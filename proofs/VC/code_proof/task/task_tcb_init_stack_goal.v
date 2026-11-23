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
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_sched_publication_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_modular_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_timer_phase_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_name_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec
    Ucos2Verify.VC.code.task.spec.task_create_continuation_spec
    Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function OS_TCBInit -----*)

Definition OS_TCBInit_safety_wit_1 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (retval: Z) (PreH1 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH2 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH3 : (task_tcb_init_entry sg_phase_call_spec (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))) invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec )) (PreH4 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH5 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH6 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH7 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH8 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH9 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH10 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) ,
  (task_tcb_init_modular_save_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec call_phase_call_spec mask_phase_call_spec retval initial_phase_call_spec )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_2 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call)) )) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec acquired )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> (task_tcb_init_free_root (sg_phase_call_spec) (acquired)))
  **  (task_tcb_init_public_without_free_root sg_phase_call_spec acquired )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_tcb_init_free_root (sg_phase_call_spec) (acquired)))
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_3 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) (PreH21 : (task_stack_live_coverage (TskState ((task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)))) (task_stack_call_active_key (first_call)) )) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state ((task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ((os_sched_call_invocation (first_call))) ((os_sched_call_origin (first_call))) (acquired) (slot) (rest) (free_image)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (tcb_layout_common_image (free_image)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_4 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= prio_pre) ” 
  &&  “ (3 <= 31) ” 
  &&  “ (0 <= 3) ”
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= prio_pre) ” 
  &&  “ (3 <= 31) ” 
  &&  “ (0 <= 3) ”
).

Definition OS_TCBInit_safety_wit_4_split_goal_1 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= prio_pre) ”
.

Definition OS_TCBInit_safety_wit_4_split_goal_2 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (3 <= 31) ”
.

Definition OS_TCBInit_safety_wit_4_split_goal_3 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= 3) ”
.

Definition OS_TCBInit_safety_wit_5 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ ((unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)) <= 63) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8))) ”
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ ((unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)) <= 63) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8))) ”
).

Definition OS_TCBInit_safety_wit_5_split_goal_1 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ ((unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)) <= 63) ”
.

Definition OS_TCBInit_safety_wit_5_split_goal_2 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8))) ”
.

Definition OS_TCBInit_safety_wit_6 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ ((Z.land prio_pre 7) <= 63) ” 
  &&  “ (0 <= (Z.land prio_pre 7)) ”
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ ((Z.land prio_pre 7) <= 63) ” 
  &&  “ (0 <= (Z.land prio_pre 7)) ”
).

Definition OS_TCBInit_safety_wit_6_split_goal_1 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ ((Z.land prio_pre 7) <= 63) ”
.

Definition OS_TCBInit_safety_wit_6_split_goal_2 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= (Z.land prio_pre 7)) ”
.

Definition OS_TCBInit_safety_wit_7 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_8 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_9 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_10 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (cpu_sr: Z) (ptcb: Z) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (PreH1 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH2 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH3 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH4 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH5 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH6 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH7 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH8 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH9 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH10 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH11 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH13 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH14 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH15 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH16 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH17 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH18 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH19 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH20 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH21 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH22 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH23 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) ,
  (store_stringLit (LitMap_phase_call_spec (("?"%string))) ("?"%string) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_tcb_init_literal_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) (LitMap_phase_call_spec (("?"%string))) )
  **  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_11 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (i: Z) (checkpoint: UCOS2_Verify_State) (checkpoint_call: OsSchedCallContext) (retval: Z) (PreH1 : (task_tcb_init_stack_same_call checkpoint_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec checkpoint )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec checkpoint_call checkpoint )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec checkpoint )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH9 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) checkpoint )) (PreH10 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH11 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH12 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH13 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH14 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH15 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH16 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH17 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH18 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH19 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH20 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH21 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH22 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH23 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH24 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH25 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH26 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH27 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH28 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH29 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) (PreH30 : (i = 1)) ,
  (task_tcb_init_modular_save_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec checkpoint_call mask_phase_call_spec retval checkpoint )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args_phase_call_spec) ((tcb_layout_common_image (free_image)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_12 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_stack_same_call current_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (current_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) (PreH21 : (i = 1)) (PreH22 : (0 <= prio_pre)) (PreH23 : (prio_pre < 64)) (PreH24 : (0 <= (prio_pre ÷ 8 ))) (PreH25 : ((prio_pre ÷ 8 ) < 8)) (PreH26 : (0 <= (prio_pre % ( 8 ) ))) (PreH27 : ((prio_pre % ( 8 ) ) < 8)) (PreH28 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) current )) (PreH29 : (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired current slot )) (PreH30 : (UCOS2_state_inv sg_phase_call_spec current )) (PreH31 : (task_stack_live_coverage (TskState (current)) (task_stack_call_active_key (current_call)) )) ,
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
  **  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |->_)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current)))
  **  (task_tcb_init_used_storage sg_phase_call_spec current )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_tcb_init_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg_phase_call_spec) (current)) )
  **  (task_tcb_init_publication_other sg_phase_call_spec current )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_13 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_stack_same_call current_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (current_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) (PreH21 : (i = 1)) (PreH22 : (0 <= prio_pre)) (PreH23 : (prio_pre < 64)) (PreH24 : (0 <= (prio_pre ÷ 8 ))) (PreH25 : ((prio_pre ÷ 8 ) < 8)) (PreH26 : (0 <= (prio_pre % ( 8 ) ))) (PreH27 : ((prio_pre % ( 8 ) ) < 8)) (PreH28 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) current )) (PreH29 : (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired current slot )) (PreH30 : (UCOS2_state_inv sg_phase_call_spec current )) (PreH31 : (task_stack_live_coverage (TskState (current)) (task_stack_call_active_key (current_call)) )) ,
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
  **  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current)))
  **  (task_tcb_init_used_storage sg_phase_call_spec current )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_tcb_init_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg_phase_call_spec) (current)) )
  **  (task_tcb_init_publication_other sg_phase_call_spec current )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_14 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (lease: TaskStackLease) (cpu_sr: Z) (i: Z) (PreH1 : (task_tcb_init_stack_same_call current_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (current_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH17 : (i = 1)) (PreH18 : (task_tcb_init_stack_call_result critical_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 0 (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH19 : (UCOS2_state_inv sg_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH20 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH21 : (task_tcb_init_publication_call_observation sg_phase_call_spec (task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease)) current_call current )) (PreH22 : (task_stack_live_coverage (TskState ((task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)))) (task_stack_call_active_key (current_call)) )) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec current_call cpu_sr (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) ((os_sched_call_invocation (current_call))) ((os_sched_call_origin (current_call))) (acquired) (slot) (free_image) (lease))) (current)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_safety_wit_15 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH17 : (task_tcb_init_call_result sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 66 acquired )) (PreH18 : (UCOS2_state_inv sg_phase_call_spec acquired )) (PreH19 : (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call)) )) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TCBInit_entail_wit_1 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (retval: Z) (PreH1 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH2 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH3 : (task_tcb_init_entry sg_phase_call_spec (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))) invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec )) (PreH4 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH5 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH6 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH7 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH8 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH9 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH10 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) ,
  (task_tcb_init_modular_save_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec call_phase_call_spec mask_phase_call_spec retval initial_phase_call_spec )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (acquired: UCOS2_Verify_State)  (first_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec retval ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec retval acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec acquired )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> (task_tcb_init_free_root (sg_phase_call_spec) (acquired)))
  **  (task_tcb_init_public_without_free_root sg_phase_call_spec acquired )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (retval: Z) (PreH1 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH2 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH3 : (task_tcb_init_entry sg_phase_call_spec (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))) invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec )) (PreH4 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH5 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH6 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH7 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH8 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH9 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH10 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) ,
  (task_tcb_init_modular_save_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec call_phase_call_spec mask_phase_call_spec retval initial_phase_call_spec )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (acquired: UCOS2_Verify_State)  (first_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec retval ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec retval acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec acquired )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> (task_tcb_init_free_root (sg_phase_call_spec) (acquired)))
  **  (task_tcb_init_public_without_free_root sg_phase_call_spec acquired )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
).

Definition OS_TCBInit_entail_wit_2 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call_2: OsSchedCallContext) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((task_tcb_init_free_root (sg_phase_call_spec) (acquired)) <> 0)) (PreH2 : (task_tcb_init_stack_same_call first_call_2 call_phase_call_spec )) (PreH3 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH4 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call_2 acquired )) (PreH5 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH6 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH7 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH8 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH9 : ((os_sched_call_invocation (first_call_2)) = invocation_phase_call_spec)) (PreH10 : ((os_sched_call_origin (first_call_2)) = origin_phase_call_spec)) (PreH11 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH12 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH13 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH14 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH15 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH16 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH17 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH18 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH19 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH20 : (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call_2)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call_2 )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec acquired )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> (task_tcb_init_free_root (sg_phase_call_spec) (acquired)))
  **  (task_tcb_init_public_without_free_root sg_phase_call_spec acquired )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (next_free: Z)  (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired_2: UCOS2_Verify_State)  (first_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired_2 ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot rest free_image ) ” 
  &&  “ (task_tcb_init_free_next_image free_image next_free ) ” 
  &&  “ (next_free = (task_tcb_init_free_next (sg_phase_call_spec) (rest))) ” 
  &&  “ ((task_tcb_init_free_root (sg_phase_call_spec) (acquired)) = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (task_stack_live_coverage (TskState (acquired_2)) (task_stack_call_active_key (first_call)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired_2 )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec acquired_2 )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> (task_tcb_init_free_root (sg_phase_call_spec) (acquired)))
  **  ((&(((task_tcb_init_free_root (sg_phase_call_spec) (acquired)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> next_free)
  **  (tcb64_storage_without (task_tcb_init_free_root (sg_phase_call_spec) (acquired)) TCBNext (tcb_layout_common_image (free_image)) )
  **  (task_tcb_init_public_without_free_head sg_phase_call_spec acquired_2 rest )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call_2: OsSchedCallContext) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((task_tcb_init_free_root (sg_phase_call_spec) (acquired)) <> 0)) (PreH2 : (task_tcb_init_stack_same_call first_call_2 call_phase_call_spec )) (PreH3 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH4 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call_2 acquired )) (PreH5 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH6 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH7 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH8 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH9 : ((os_sched_call_invocation (first_call_2)) = invocation_phase_call_spec)) (PreH10 : ((os_sched_call_origin (first_call_2)) = origin_phase_call_spec)) (PreH11 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH12 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH13 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH14 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH15 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH16 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH17 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH18 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH19 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH20 : (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call_2)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call_2 )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec acquired )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (task_tcb_init_public_without_free_root sg_phase_call_spec acquired )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired_2: UCOS2_Verify_State)  (first_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired_2 ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot rest free_image ) ” 
  &&  “ (task_tcb_init_free_next_image free_image (task_tcb_init_free_next (sg_phase_call_spec) (rest)) ) ” 
  &&  “ ((task_tcb_init_free_root (sg_phase_call_spec) (acquired)) = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (task_stack_live_coverage (TskState (acquired_2)) (task_stack_call_active_key (first_call)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired_2 )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec acquired_2 )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  ((&(((task_tcb_init_free_root (sg_phase_call_spec) (acquired)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_free_next (sg_phase_call_spec) (rest)))
  **  (tcb64_storage_without (task_tcb_init_free_root (sg_phase_call_spec) (acquired)) TCBNext (tcb_layout_common_image (free_image)) )
  **  (task_tcb_init_public_without_free_head sg_phase_call_spec acquired_2 rest )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
).

Definition OS_TCBInit_entail_wit_3 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (next_free: Z) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call_2 call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call_2 acquired_2 )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call_2)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call_2)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH20 : (task_tcb_init_free_next_image free_image_2 next_free )) (PreH21 : (next_free = (task_tcb_init_free_next (sg_phase_call_spec) (rest_2)))) (PreH22 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) (PreH23 : (task_stack_live_coverage (TskState (acquired_2)) (task_stack_call_active_key (first_call_2)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired_2 )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call_2 )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec acquired_2 )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> next_free)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> next_free)
  **  (tcb64_storage_without ptcb TCBNext (tcb_layout_common_image (free_image_2)) )
  **  (task_tcb_init_public_without_free_head sg_phase_call_spec acquired_2 rest_2 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State)  (first_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (task_stack_live_coverage (TskState ((task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)))) (task_stack_call_active_key (first_call)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (UCOS2_inv sg_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (tcb64_storage_rep ptcb (tcb_layout_common_image (free_image)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (next_free: Z) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call_2 call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call_2 acquired_2 )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call_2)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call_2)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH20 : (task_tcb_init_free_next_image free_image_2 next_free )) (PreH21 : (next_free = (task_tcb_init_free_next (sg_phase_call_spec) (rest_2)))) (PreH22 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) (PreH23 : (task_stack_live_coverage (TskState (acquired_2)) (task_stack_call_active_key (first_call_2)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired_2 )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call_2 )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec acquired_2 )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> next_free)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> next_free)
  **  (tcb64_storage_without ptcb TCBNext (tcb_layout_common_image (free_image_2)) )
  **  (task_tcb_init_public_without_free_head sg_phase_call_spec acquired_2 rest_2 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State)  (first_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (task_stack_live_coverage (TskState ((task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)))) (task_stack_call_active_key (first_call)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (UCOS2_inv sg_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (tcb64_storage_rep ptcb (tcb_layout_common_image (free_image)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
).

Definition OS_TCBInit_entail_wit_4 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call_2 call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call_2 acquired_2 )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call_2)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call_2)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) (PreH21 : (task_stack_live_coverage (TskState ((task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired_2) (slot_2) (rest_2) (free_image_2)))) (task_stack_call_active_key (first_call_2)) )) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call_2 cpu_sr (task_tcb_init_detached_state ((task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ((os_sched_call_invocation (first_call_2))) ((os_sched_call_origin (first_call_2))) (acquired_2) (slot_2) (rest_2) (free_image_2)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (tcb_layout_common_image (free_image_2)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State)  (first_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ”
  &&  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call_2 call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call_2 acquired_2 )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call_2)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call_2)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) (PreH21 : (task_stack_live_coverage (TskState ((task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired_2) (slot_2) (rest_2) (free_image_2)))) (task_stack_call_active_key (first_call_2)) )) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call_2 cpu_sr (task_tcb_init_detached_state ((task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ((os_sched_call_invocation (first_call_2))) ((os_sched_call_origin (first_call_2))) (acquired_2) (slot_2) (rest_2) (free_image_2)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (tcb_layout_common_image (free_image_2)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (x_19: Z)  (x_18: Z)  (x_17: Z)  (x_16: Z)  (x_15: Z)  (x_14: Z)  (x_13: Z)  (x_12: Z)  (x_11: Z)  (x_10: Z)  (x_9: Z)  (x_8: Z)  (x_7: Z)  (x_6: Z)  (x_5: Z)  (x_4: Z)  (x_3: Z)  (x_2: Z)  (x: Z)  (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State)  (first_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ”
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
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
).

Definition OS_TCBInit_entail_wit_5 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (cpu_sr: Z) (ptcb: Z) (first_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (PreH1 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH2 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH3 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH4 : (task_tcb_init_stack_same_call first_call_2 call_phase_call_spec )) (PreH5 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH6 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call_2 acquired_2 )) (PreH7 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 )) (PreH8 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH9 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH10 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH11 : ((os_sched_call_invocation (first_call_2)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (first_call_2)) = origin_phase_call_spec)) (PreH13 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH14 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH15 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH16 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH17 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH18 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH19 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH20 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH21 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH22 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH23 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call_2 cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired_2) (slot_2) (rest_2) (free_image_2)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> ((LitMap_phase_call_spec (("?"%string))) + (0 * sizeof(CHAR))))
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State)  (first_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ”
  &&  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 0 0 (zeros (0)) )
  **  (UIntArray.undef_seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 0 1 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (critical_phase_call_spec: CriticalRegionResources) (cpu_sr: Z) (ptcb: Z) (first_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (PreH1 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH2 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH3 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH4 : (task_tcb_init_stack_same_call first_call_2 call_phase_call_spec )) (PreH5 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH6 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call_2 acquired_2 )) (PreH7 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 )) (PreH8 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH9 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH10 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH11 : ((os_sched_call_invocation (first_call_2)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (first_call_2)) = origin_phase_call_spec)) (PreH13 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH14 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH15 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH16 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH17 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH18 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH19 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH20 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH21 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH22 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH23 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)) = (prio_pre ÷ 8 )) ” 
  &&  “ ((Z.land prio_pre 7) = (prio_pre % ( 8 ) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))) (8)) = (Z.shiftl 1 (prio_pre ÷ 8 ))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)) = (Z.shiftl 1 (prio_pre % ( 8 ) ))) ” 
  &&  “ (((LitMap_phase_call_spec (("?"%string))) + (0 * sizeof(CHAR))) = (LitMap_phase_call_spec (("?"%string)))) ” 
  &&  “ ((zeros (0)) = (@nil Z)) ”
  &&  emp
).

Definition OS_TCBInit_entail_wit_5_split_goal_1 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (critical_phase_call_spec: CriticalRegionResources) (cpu_sr: Z) (ptcb: Z) (first_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (PreH1 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH2 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH3 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH4 : (task_tcb_init_stack_same_call first_call_2 call_phase_call_spec )) (PreH5 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH6 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call_2 acquired_2 )) (PreH7 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 )) (PreH8 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH9 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH10 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH11 : ((os_sched_call_invocation (first_call_2)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (first_call_2)) = origin_phase_call_spec)) (PreH13 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH14 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH15 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH16 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH17 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH18 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH19 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH20 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH21 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH22 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH23 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) ,
  ((unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)) = (prio_pre ÷ 8 ))
.

Definition OS_TCBInit_entail_wit_5_split_goal_2 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (critical_phase_call_spec: CriticalRegionResources) (cpu_sr: Z) (ptcb: Z) (first_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (PreH1 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH2 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH3 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH4 : (task_tcb_init_stack_same_call first_call_2 call_phase_call_spec )) (PreH5 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH6 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call_2 acquired_2 )) (PreH7 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 )) (PreH8 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH9 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH10 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH11 : ((os_sched_call_invocation (first_call_2)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (first_call_2)) = origin_phase_call_spec)) (PreH13 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH14 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH15 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH16 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH17 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH18 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH19 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH20 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH21 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH22 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH23 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) ,
  ((Z.land prio_pre 7) = (prio_pre % ( 8 ) ))
.

Definition OS_TCBInit_entail_wit_5_split_goal_3 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (critical_phase_call_spec: CriticalRegionResources) (cpu_sr: Z) (ptcb: Z) (first_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (PreH1 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH2 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH3 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH4 : (task_tcb_init_stack_same_call first_call_2 call_phase_call_spec )) (PreH5 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH6 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call_2 acquired_2 )) (PreH7 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 )) (PreH8 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH9 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH10 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH11 : ((os_sched_call_invocation (first_call_2)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (first_call_2)) = origin_phase_call_spec)) (PreH13 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH14 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH15 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH16 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH17 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH18 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH19 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH20 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH21 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH22 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH23 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) ,
  ((unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr prio_pre 3)) (8)))) (8)) = (Z.shiftl 1 (prio_pre ÷ 8 )))
.

Definition OS_TCBInit_entail_wit_5_split_goal_4 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (critical_phase_call_spec: CriticalRegionResources) (cpu_sr: Z) (ptcb: Z) (first_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (PreH1 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH2 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH3 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH4 : (task_tcb_init_stack_same_call first_call_2 call_phase_call_spec )) (PreH5 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH6 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call_2 acquired_2 )) (PreH7 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 )) (PreH8 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH9 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH10 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH11 : ((os_sched_call_invocation (first_call_2)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (first_call_2)) = origin_phase_call_spec)) (PreH13 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH14 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH15 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH16 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH17 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH18 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH19 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH20 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH21 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH22 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH23 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) ,
  ((unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)) = (Z.shiftl 1 (prio_pre % ( 8 ) )))
.

Definition OS_TCBInit_entail_wit_5_split_goal_5 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (critical_phase_call_spec: CriticalRegionResources) (cpu_sr: Z) (ptcb: Z) (first_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (PreH1 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH2 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH3 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH4 : (task_tcb_init_stack_same_call first_call_2 call_phase_call_spec )) (PreH5 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH6 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call_2 acquired_2 )) (PreH7 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 )) (PreH8 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH9 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH10 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH11 : ((os_sched_call_invocation (first_call_2)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (first_call_2)) = origin_phase_call_spec)) (PreH13 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH14 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH15 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH16 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH17 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH18 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH19 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH20 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH21 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH22 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH23 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) ,
  (((LitMap_phase_call_spec (("?"%string))) + (0 * sizeof(CHAR))) = (LitMap_phase_call_spec (("?"%string))))
.

Definition OS_TCBInit_entail_wit_5_split_goal_6 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (critical_phase_call_spec: CriticalRegionResources) (cpu_sr: Z) (ptcb: Z) (first_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (PreH1 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH2 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH3 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH4 : (task_tcb_init_stack_same_call first_call_2 call_phase_call_spec )) (PreH5 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH6 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call_2 acquired_2 )) (PreH7 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 )) (PreH8 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH9 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH10 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH11 : ((os_sched_call_invocation (first_call_2)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (first_call_2)) = origin_phase_call_spec)) (PreH13 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH14 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH15 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH16 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH17 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH18 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH19 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH20 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH21 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH22 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH23 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) ,
  ((zeros (0)) = (@nil Z))
.

Definition OS_TCBInit_entail_wit_6 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (i: Z) (ptcb: Z) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (acquired_2: UCOS2_Verify_State) (first_call_2: OsSchedCallContext) (PreH1 : (i < 1)) (PreH2 : (task_tcb_init_stack_same_call first_call_2 call_phase_call_spec )) (PreH3 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH4 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call_2 acquired_2 )) (PreH5 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 )) (PreH6 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH7 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH8 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH9 : ((os_sched_call_invocation (first_call_2)) = invocation_phase_call_spec)) (PreH10 : ((os_sched_call_origin (first_call_2)) = origin_phase_call_spec)) (PreH11 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH12 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH13 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH14 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH15 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH16 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH17 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH18 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH19 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH20 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH21 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) (PreH22 : (0 <= i)) (PreH23 : (i <= 1)) ,
  (UIntArray.seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 0 (i + 1 ) (app ((zeros (i))) ((cons (0) ((@nil Z))))) )
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call_2 cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired_2) (slot_2) (rest_2) (free_image_2)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State)  (first_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 1) ”
  &&  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 0 (i + 1 ) (zeros ((i + 1 ))) )
  **  (UIntArray.undef_seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") (i + 1 ) 1 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (i: Z) (ptcb: Z) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (acquired_2: UCOS2_Verify_State) (first_call_2: OsSchedCallContext) (PreH1 : (i < 1)) (PreH2 : (task_tcb_init_stack_same_call first_call_2 call_phase_call_spec )) (PreH3 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH4 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call_2 acquired_2 )) (PreH5 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 )) (PreH6 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH7 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH8 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH9 : ((os_sched_call_invocation (first_call_2)) = invocation_phase_call_spec)) (PreH10 : ((os_sched_call_origin (first_call_2)) = origin_phase_call_spec)) (PreH11 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH12 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH13 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH14 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH15 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH16 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH17 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH18 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH19 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH20 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH21 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) (PreH22 : (0 <= i)) (PreH23 : (i <= 1)) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call_2 cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired_2) (slot_2) (rest_2) (free_image_2)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image_2)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State)  (first_call: OsSchedCallContext) ,
  “ ((app ((zeros (i))) ((cons (0) ((@nil Z))))) = (zeros ((i + 1 )))) ” 
  &&  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 1) ”
  &&  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (task_tcb_init_retained_storage ptcb (tcb_layout_common_image (free_image)) )
  **  (UIntArray.undef_seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") (i + 1 ) 1 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
).

Definition OS_TCBInit_entail_wit_7 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (i: Z) (ptcb: Z) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (acquired_2: UCOS2_Verify_State) (first_call_2: OsSchedCallContext) (PreH1 : (i >= 1)) (PreH2 : (task_tcb_init_stack_same_call first_call_2 call_phase_call_spec )) (PreH3 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH4 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call_2 acquired_2 )) (PreH5 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 )) (PreH6 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH7 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH8 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH9 : ((os_sched_call_invocation (first_call_2)) = invocation_phase_call_spec)) (PreH10 : ((os_sched_call_origin (first_call_2)) = origin_phase_call_spec)) (PreH11 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH12 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH13 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH14 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH15 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH16 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH17 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH18 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH19 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH20 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH21 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) (PreH22 : (0 <= i)) (PreH23 : (i <= 1)) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call_2 cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired_2) (slot_2) (rest_2) (free_image_2)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 0 i (zeros (i)) )
  **  (UIntArray.undef_seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") i 1 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State)  (first_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (i = 1) ”
  &&  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args_phase_call_spec) ((tcb_layout_common_image (free_image)))) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (i: Z) (ptcb: Z) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (acquired_2: UCOS2_Verify_State) (first_call_2: OsSchedCallContext) (PreH1 : (stk_size_pre <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : (stk_size_pre >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (i >= 1)) (PreH6 : (task_tcb_init_stack_same_call first_call_2 call_phase_call_spec )) (PreH7 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH8 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call_2 acquired_2 )) (PreH9 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 )) (PreH10 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH11 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH12 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH13 : ((os_sched_call_invocation (first_call_2)) = invocation_phase_call_spec)) (PreH14 : ((os_sched_call_origin (first_call_2)) = origin_phase_call_spec)) (PreH15 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH16 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH17 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH18 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH19 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH20 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH21 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH22 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH23 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH24 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH25 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) (PreH26 : (0 <= i)) (PreH27 : (i <= 1)) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call_2 cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired_2) (slot_2) (rest_2) (free_image_2)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 0 i (zeros (i)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State)  (first_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (i = 1) ”
  &&  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args_phase_call_spec) ((tcb_layout_common_image (free_image)))) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
).

Definition OS_TCBInit_entail_wit_8 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (i: Z) (checkpoint: UCOS2_Verify_State) (checkpoint_call: OsSchedCallContext) (retval: Z) (PreH1 : (task_tcb_init_stack_same_call checkpoint_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec checkpoint )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec checkpoint_call checkpoint )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec checkpoint )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH9 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired_2) (slot_2) (rest_2) (free_image_2)) checkpoint )) (PreH10 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH11 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH12 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired_2 )) (PreH13 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 )) (PreH14 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH15 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH16 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH17 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH18 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH19 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH20 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH21 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH22 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH23 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH24 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH25 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH26 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH27 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH28 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH29 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) (PreH30 : (i = 1)) ,
  (task_tcb_init_modular_save_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec checkpoint_call mask_phase_call_spec retval checkpoint )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args_phase_call_spec) ((tcb_layout_common_image (free_image_2)))) )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State)  (current: UCOS2_Verify_State)  (current_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call current_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec current ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (current_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec retval ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec current ) ” 
  &&  “ (task_stack_live_coverage (TskState (current)) (task_stack_call_active_key (current_call)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec retval current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |->_)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |->_)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current)))
  **  (task_tcb_init_used_storage sg_phase_call_spec current )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_tcb_init_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg_phase_call_spec) (current)) )
  **  (task_tcb_init_publication_other sg_phase_call_spec current )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (i: Z) (checkpoint: UCOS2_Verify_State) (checkpoint_call: OsSchedCallContext) (retval: Z) (PreH1 : (task_tcb_init_stack_same_call checkpoint_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec checkpoint )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec checkpoint_call checkpoint )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec checkpoint )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH9 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired_2) (slot_2) (rest_2) (free_image_2)) checkpoint )) (PreH10 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH11 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH12 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired_2 )) (PreH13 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 )) (PreH14 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH15 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH16 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH17 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH18 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH19 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH20 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH21 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH22 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH23 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH24 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH25 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH26 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH27 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH28 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH29 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) (PreH30 : (i = 1)) ,
  (task_tcb_init_modular_save_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec checkpoint_call mask_phase_call_spec retval checkpoint )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args_phase_call_spec) ((tcb_layout_common_image (free_image_2)))) )
|--
  EX (x_2: Z)  (x: Z)  (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State)  (current: UCOS2_Verify_State)  (current_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call current_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec current ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (current_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec retval ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec current ) ” 
  &&  “ (task_stack_live_coverage (TskState (current)) (task_stack_call_active_key (current_call)) ) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> x_2)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> x)
  **  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec retval current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current)))
  **  (task_tcb_init_used_storage sg_phase_call_spec current )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_tcb_init_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg_phase_call_spec) (current)) )
  **  (task_tcb_init_publication_other sg_phase_call_spec current )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
).

Definition OS_TCBInit_entail_wit_9 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (current_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : ((task_tcb_init_active_head (sg_phase_call_spec) (current_2)) <> 0)) (PreH2 : (task_tcb_init_stack_same_call current_call_2 call_phase_call_spec )) (PreH3 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current_2 )) (PreH4 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call_2 current_2 )) (PreH5 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current_2 )) (PreH6 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH7 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH8 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH9 : ((os_sched_call_invocation (current_call_2)) = invocation_phase_call_spec)) (PreH10 : ((os_sched_call_origin (current_call_2)) = origin_phase_call_spec)) (PreH11 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH12 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH13 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH14 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH15 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH16 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH17 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH18 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH19 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH20 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH21 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) (PreH22 : (i = 1)) (PreH23 : (0 <= prio_pre)) (PreH24 : (prio_pre < 64)) (PreH25 : (0 <= (prio_pre ÷ 8 ))) (PreH26 : ((prio_pre ÷ 8 ) < 8)) (PreH27 : (0 <= (prio_pre % ( 8 ) ))) (PreH28 : ((prio_pre % ( 8 ) ) < 8)) (PreH29 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired_2) (slot_2) (rest_2) (free_image_2)) current_2 )) (PreH30 : (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 current_2 slot_2 )) (PreH31 : (UCOS2_state_inv sg_phase_call_spec current_2 )) (PreH32 : (task_stack_live_coverage (TskState (current_2)) (task_stack_call_active_key (current_call_2)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current_2 )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call_2 )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current_2 )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current_2)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current_2)))
  **  (task_tcb_init_used_storage sg_phase_call_spec current_2 )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_tcb_init_ready_group (current_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg_phase_call_spec) (current_2)) )
  **  (task_tcb_init_publication_other sg_phase_call_spec current_2 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (previous: Z)  (head: Z)  (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State)  (current: UCOS2_Verify_State)  (current_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call current_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec current ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (current_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec current ) ” 
  &&  “ (head = (task_tcb_init_active_head (sg_phase_call_spec) (current))) ” 
  &&  “ (head <> 0) ” 
  &&  “ (task_stack_live_coverage (TskState (current)) (task_stack_call_active_key (current_call)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> head)
  **  ((&((head)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> previous)
  **  (task_tcb_init_used_without_head_prev sg_phase_call_spec current )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_tcb_init_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg_phase_call_spec) (current)) )
  **  (task_tcb_init_publication_other sg_phase_call_spec current )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (current_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : ((task_tcb_init_active_head (sg_phase_call_spec) (current_2)) <> 0)) (PreH2 : (task_tcb_init_stack_same_call current_call_2 call_phase_call_spec )) (PreH3 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current_2 )) (PreH4 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call_2 current_2 )) (PreH5 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current_2 )) (PreH6 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH7 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH8 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH9 : ((os_sched_call_invocation (current_call_2)) = invocation_phase_call_spec)) (PreH10 : ((os_sched_call_origin (current_call_2)) = origin_phase_call_spec)) (PreH11 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH12 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH13 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH14 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH15 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH16 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH17 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH18 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH19 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH20 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH21 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) (PreH22 : (i = 1)) (PreH23 : (0 <= prio_pre)) (PreH24 : (prio_pre < 64)) (PreH25 : (0 <= (prio_pre ÷ 8 ))) (PreH26 : ((prio_pre ÷ 8 ) < 8)) (PreH27 : (0 <= (prio_pre % ( 8 ) ))) (PreH28 : ((prio_pre % ( 8 ) ) < 8)) (PreH29 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired_2) (slot_2) (rest_2) (free_image_2)) current_2 )) (PreH30 : (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 current_2 slot_2 )) (PreH31 : (UCOS2_state_inv sg_phase_call_spec current_2 )) (PreH32 : (task_stack_live_coverage (TskState (current_2)) (task_stack_call_active_key (current_call_2)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current_2 )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call_2 )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current_2 )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image_2)) )
  **  (task_tcb_init_used_storage sg_phase_call_spec current_2 )
  **  (task_tcb_init_publication_other sg_phase_call_spec current_2 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (previous: Z)  (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State)  (current: UCOS2_Verify_State)  (current_call: OsSchedCallContext) ,
  “ ((task_tcb_init_priority_table (sg_phase_call_spec) (current_2)) = (task_tcb_init_priority_table (sg_phase_call_spec) (current))) ” 
  &&  “ ((task_tcb_init_ready_rows (current_2)) = (task_tcb_init_ready_rows (current))) ” 
  &&  “ ((task_tcb_init_ready_group (current_2)) = (task_tcb_init_ready_group (current))) ” 
  &&  “ ((task_tcb_init_count (current_2)) = (task_tcb_init_count (current))) ” 
  &&  “ ((task_tcb_init_active_head (sg_phase_call_spec) (current_2)) = (task_tcb_init_active_head (sg_phase_call_spec) (current))) ” 
  &&  “ ((task_tcb_init_active_head (sg_phase_call_spec) (current_2)) = (task_tcb_init_active_head (sg_phase_call_spec) (current))) ” 
  &&  “ (task_tcb_init_stack_same_call current_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec current ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (current_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec current ) ” 
  &&  “ ((task_tcb_init_active_head (sg_phase_call_spec) (current)) <> 0) ” 
  &&  “ (task_stack_live_coverage (TskState (current)) (task_stack_call_active_key (current_call)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image)) )
  **  ((&(((task_tcb_init_active_head (sg_phase_call_spec) (current)))  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> previous)
  **  (task_tcb_init_used_without_head_prev sg_phase_call_spec current )
  **  (task_tcb_init_publication_other sg_phase_call_spec current )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
).

Definition OS_TCBInit_entail_wit_10_1 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (current_2: UCOS2_Verify_State) (head: Z) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_stack_same_call current_call_2 call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current_2 )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call_2 current_2 )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current_2 )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (current_call_2)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (current_call_2)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) (PreH21 : (i = 1)) (PreH22 : (0 <= prio_pre)) (PreH23 : (prio_pre < 64)) (PreH24 : (0 <= (prio_pre ÷ 8 ))) (PreH25 : ((prio_pre ÷ 8 ) < 8)) (PreH26 : (0 <= (prio_pre % ( 8 ) ))) (PreH27 : ((prio_pre % ( 8 ) ) < 8)) (PreH28 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired_2) (slot_2) (rest_2) (free_image_2)) current_2 )) (PreH29 : (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 current_2 slot_2 )) (PreH30 : (UCOS2_state_inv sg_phase_call_spec current_2 )) (PreH31 : (head = (task_tcb_init_active_head (sg_phase_call_spec) (current_2)))) (PreH32 : (head <> 0)) (PreH33 : (task_stack_live_coverage (TskState (current_2)) (task_stack_call_active_key (current_call_2)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current_2 )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call_2 )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current_2 )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current_2)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> head)
  **  ((&((head)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> ptcb)
  **  (task_tcb_init_used_without_head_prev sg_phase_call_spec current_2 )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_tcb_init_ready_group (current_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg_phase_call_spec) (current_2)) )
  **  (task_tcb_init_publication_other sg_phase_call_spec current_2 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State)  (current: UCOS2_Verify_State)  (current_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call current_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec current ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (current_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec current ) ” 
  &&  “ (task_stack_live_coverage (TskState (current)) (task_stack_call_active_key (current_call)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current)))
  **  (task_tcb_init_used_with_head_prev sg_phase_call_spec current slot )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_tcb_init_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg_phase_call_spec) (current)) )
  **  (task_tcb_init_publication_other sg_phase_call_spec current )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (current_2: UCOS2_Verify_State) (head: Z) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_stack_same_call current_call_2 call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current_2 )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call_2 current_2 )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current_2 )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (current_call_2)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (current_call_2)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) (PreH21 : (i = 1)) (PreH22 : (0 <= prio_pre)) (PreH23 : (prio_pre < 64)) (PreH24 : (0 <= (prio_pre ÷ 8 ))) (PreH25 : ((prio_pre ÷ 8 ) < 8)) (PreH26 : (0 <= (prio_pre % ( 8 ) ))) (PreH27 : ((prio_pre % ( 8 ) ) < 8)) (PreH28 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired_2) (slot_2) (rest_2) (free_image_2)) current_2 )) (PreH29 : (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 current_2 slot_2 )) (PreH30 : (UCOS2_state_inv sg_phase_call_spec current_2 )) (PreH31 : (head = (task_tcb_init_active_head (sg_phase_call_spec) (current_2)))) (PreH32 : (head <> 0)) (PreH33 : (task_stack_live_coverage (TskState (current_2)) (task_stack_call_active_key (current_call_2)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current_2 )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call_2 )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current_2 )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image_2)) )
  **  ((&((head)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> ptcb)
  **  (task_tcb_init_used_without_head_prev sg_phase_call_spec current_2 )
  **  (task_tcb_init_publication_other sg_phase_call_spec current_2 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State)  (current: UCOS2_Verify_State)  (current_call: OsSchedCallContext) ,
  “ ((task_tcb_init_priority_table (sg_phase_call_spec) (current_2)) = (task_tcb_init_priority_table (sg_phase_call_spec) (current))) ” 
  &&  “ ((task_tcb_init_ready_rows (current_2)) = (task_tcb_init_ready_rows (current))) ” 
  &&  “ ((task_tcb_init_ready_group (current_2)) = (task_tcb_init_ready_group (current))) ” 
  &&  “ ((task_tcb_init_count (current_2)) = (task_tcb_init_count (current))) ” 
  &&  “ (head = (task_tcb_init_active_head (sg_phase_call_spec) (current))) ” 
  &&  “ ((task_tcb_init_active_head (sg_phase_call_spec) (current_2)) = (task_tcb_init_active_head (sg_phase_call_spec) (current))) ” 
  &&  “ (task_tcb_init_stack_same_call current_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec current ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (current_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec current ) ” 
  &&  “ (task_stack_live_coverage (TskState (current)) (task_stack_call_active_key (current_call)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image)) )
  **  (task_tcb_init_used_with_head_prev sg_phase_call_spec current slot )
  **  (task_tcb_init_publication_other sg_phase_call_spec current )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
).

Definition OS_TCBInit_entail_wit_10_2 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (current_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : ((task_tcb_init_active_head (sg_phase_call_spec) (current_2)) = 0)) (PreH2 : (task_tcb_init_stack_same_call current_call_2 call_phase_call_spec )) (PreH3 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current_2 )) (PreH4 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call_2 current_2 )) (PreH5 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current_2 )) (PreH6 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH7 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH8 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH9 : ((os_sched_call_invocation (current_call_2)) = invocation_phase_call_spec)) (PreH10 : ((os_sched_call_origin (current_call_2)) = origin_phase_call_spec)) (PreH11 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH12 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH13 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH14 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH15 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH16 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH17 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH18 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH19 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH20 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH21 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) (PreH22 : (i = 1)) (PreH23 : (0 <= prio_pre)) (PreH24 : (prio_pre < 64)) (PreH25 : (0 <= (prio_pre ÷ 8 ))) (PreH26 : ((prio_pre ÷ 8 ) < 8)) (PreH27 : (0 <= (prio_pre % ( 8 ) ))) (PreH28 : ((prio_pre % ( 8 ) ) < 8)) (PreH29 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired_2) (slot_2) (rest_2) (free_image_2)) current_2 )) (PreH30 : (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 current_2 slot_2 )) (PreH31 : (UCOS2_state_inv sg_phase_call_spec current_2 )) (PreH32 : (task_stack_live_coverage (TskState (current_2)) (task_stack_call_active_key (current_call_2)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current_2 )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call_2 )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current_2 )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current_2)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current_2)))
  **  (task_tcb_init_used_storage sg_phase_call_spec current_2 )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_tcb_init_ready_group (current_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current_2)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg_phase_call_spec) (current_2)) )
  **  (task_tcb_init_publication_other sg_phase_call_spec current_2 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State)  (current: UCOS2_Verify_State)  (current_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call current_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec current ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (current_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec current ) ” 
  &&  “ (task_stack_live_coverage (TskState (current)) (task_stack_call_active_key (current_call)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current)))
  **  (task_tcb_init_used_with_head_prev sg_phase_call_spec current slot )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (task_tcb_init_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg_phase_call_spec) (current)) )
  **  (task_tcb_init_publication_other sg_phase_call_spec current )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest_2: (@list Z)) (free_image_2: TCBLayoutImage) (current_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : ((task_tcb_init_active_head (sg_phase_call_spec) (current_2)) = 0)) (PreH2 : (task_tcb_init_stack_same_call current_call_2 call_phase_call_spec )) (PreH3 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current_2 )) (PreH4 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call_2 current_2 )) (PreH5 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current_2 )) (PreH6 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH7 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH8 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH9 : ((os_sched_call_invocation (current_call_2)) = invocation_phase_call_spec)) (PreH10 : ((os_sched_call_origin (current_call_2)) = origin_phase_call_spec)) (PreH11 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH12 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH13 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH14 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH15 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH16 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH17 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH18 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH19 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH20 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 )) (PreH21 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) (PreH22 : (i = 1)) (PreH23 : (0 <= prio_pre)) (PreH24 : (prio_pre < 64)) (PreH25 : (0 <= (prio_pre ÷ 8 ))) (PreH26 : ((prio_pre ÷ 8 ) < 8)) (PreH27 : (0 <= (prio_pre % ( 8 ) ))) (PreH28 : ((prio_pre % ( 8 ) ) < 8)) (PreH29 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired_2) (slot_2) (rest_2) (free_image_2)) current_2 )) (PreH30 : (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 current_2 slot_2 )) (PreH31 : (UCOS2_state_inv sg_phase_call_spec current_2 )) (PreH32 : (task_stack_live_coverage (TskState (current_2)) (task_stack_call_active_key (current_call_2)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current_2 )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call_2 )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current_2 )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image_2)) )
  **  (task_tcb_init_used_storage sg_phase_call_spec current_2 )
  **  (task_tcb_init_publication_other sg_phase_call_spec current_2 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (slot: Z)  (rest: (@list Z))  (free_image: TCBLayoutImage)  (acquired: UCOS2_Verify_State)  (current: UCOS2_Verify_State)  (current_call: OsSchedCallContext) ,
  “ ((task_tcb_init_priority_table (sg_phase_call_spec) (current_2)) = (task_tcb_init_priority_table (sg_phase_call_spec) (current))) ” 
  &&  “ ((task_tcb_init_ready_rows (current_2)) = (task_tcb_init_ready_rows (current))) ” 
  &&  “ ((task_tcb_init_ready_group (current_2)) = (task_tcb_init_ready_group (current))) ” 
  &&  “ ((task_tcb_init_count (current_2)) = (task_tcb_init_count (current))) ” 
  &&  “ ((task_tcb_init_active_head (sg_phase_call_spec) (current_2)) = (task_tcb_init_active_head (sg_phase_call_spec) (current))) ” 
  &&  “ (task_tcb_init_stack_same_call current_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec current ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (current_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec current ) ” 
  &&  “ (task_stack_live_coverage (TskState (current)) (task_stack_call_active_key (current_call)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (task_tcb_init_retained_without_links ptcb (tcb_layout_common_image (free_image)) )
  **  (task_tcb_init_used_with_head_prev sg_phase_call_spec current slot )
  **  (task_tcb_init_publication_other sg_phase_call_spec current )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
).

Definition OS_TCBInit_entail_wit_11 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest: (@list Z)) (free_image_2: TCBLayoutImage) (current_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_stack_same_call current_call_2 call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current_2 )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call_2 current_2 )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current_2 )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (current_call_2)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (current_call_2)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest free_image_2 )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) (PreH21 : (i = 1)) (PreH22 : (0 <= prio_pre)) (PreH23 : (prio_pre < 64)) (PreH24 : (0 <= (prio_pre ÷ 8 ))) (PreH25 : ((prio_pre ÷ 8 ) < 8)) (PreH26 : (0 <= (prio_pre % ( 8 ) ))) (PreH27 : ((prio_pre % ( 8 ) ) < 8)) (PreH28 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired_2) (slot_2) (rest) (free_image_2)) current_2 )) (PreH29 : (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 current_2 slot_2 )) (PreH30 : (UCOS2_state_inv sg_phase_call_spec current_2 )) (PreH31 : (task_stack_live_coverage (TskState (current_2)) (task_stack_call_active_key (current_call_2)) )) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth (prio_pre) (ptcb) ((task_tcb_init_priority_table (sg_phase_call_spec) (current_2)))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((prio_pre ÷ 8 )) ((Z.lor (unsigned_last_nbits ((Znth (prio_pre ÷ 8 ) (task_tcb_init_ready_rows (current_2)) 0)) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre % ( 8 ) ))) (8)))) ((task_tcb_init_ready_rows (current_2)))) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current_2 )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call_2 )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current_2 )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current_2)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_used_with_head_prev sg_phase_call_spec current_2 slot_2 )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (unsigned_last_nbits (((task_tcb_init_count (current_2)) + 1 )) (8)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_tcb_init_ready_group (current_2))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre ÷ 8 ))) (8))))
  **  (task_tcb_init_publication_other sg_phase_call_spec current_2 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (acquired: UCOS2_Verify_State)  (slot: Z)  (free_image: TCBLayoutImage)  (lease: TaskStackLease)  (current: UCOS2_Verify_State)  (current_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call current_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec current ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (current_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (i = 1) ” 
  &&  “ (task_tcb_init_stack_call_result critical_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 0 (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) ) ” 
  &&  “ (task_tcb_init_publication_call_observation sg_phase_call_spec (task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease)) current_call current ) ” 
  &&  “ (task_stack_live_coverage (TskState ((task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)))) (task_stack_call_active_key (current_call)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (UCOS2_inv sg_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (slot_2: Z) (rest: (@list Z)) (free_image_2: TCBLayoutImage) (current_2: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (stk_size_pre <= UINT_MAX)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : (stk_size_pre >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (task_tcb_init_stack_same_call current_call_2 call_phase_call_spec )) (PreH6 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current_2 )) (PreH7 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call_2 current_2 )) (PreH8 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current_2 )) (PreH9 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH10 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH11 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH12 : ((os_sched_call_invocation (current_call_2)) = invocation_phase_call_spec)) (PreH13 : ((os_sched_call_origin (current_call_2)) = origin_phase_call_spec)) (PreH14 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH15 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH16 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH17 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH18 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH19 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH20 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH21 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH22 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH23 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest free_image_2 )) (PreH24 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot_2)))) (PreH25 : (i = 1)) (PreH26 : (0 <= prio_pre)) (PreH27 : (prio_pre < 64)) (PreH28 : (0 <= (prio_pre ÷ 8 ))) (PreH29 : ((prio_pre ÷ 8 ) < 8)) (PreH30 : (0 <= (prio_pre % ( 8 ) ))) (PreH31 : ((prio_pre % ( 8 ) ) < 8)) (PreH32 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired_2) (slot_2) (rest) (free_image_2)) current_2 )) (PreH33 : (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 current_2 slot_2 )) (PreH34 : (UCOS2_state_inv sg_phase_call_spec current_2 )) (PreH35 : (task_stack_live_coverage (TskState (current_2)) (task_stack_call_active_key (current_call_2)) )) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth (prio_pre) (ptcb) ((task_tcb_init_priority_table (sg_phase_call_spec) (current_2)))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((prio_pre ÷ 8 )) ((Z.lor (unsigned_last_nbits ((Znth (prio_pre ÷ 8 ) (task_tcb_init_ready_rows (current_2)) 0)) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre % ( 8 ) ))) (8)))) ((task_tcb_init_ready_rows (current_2)))) )
  **  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current_2 )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call_2 )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current_2 )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current_2)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_used_with_head_prev sg_phase_call_spec current_2 slot_2 )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (unsigned_last_nbits (((task_tcb_init_count (current_2)) + 1 )) (8)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_tcb_init_ready_group (current_2))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre ÷ 8 ))) (8))))
  **  (task_tcb_init_publication_other sg_phase_call_spec current_2 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (acquired: UCOS2_Verify_State)  (slot: Z)  (free_image: TCBLayoutImage)  (lease: TaskStackLease)  (current: UCOS2_Verify_State)  (current_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call current_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec current ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (current_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (i = 1) ” 
  &&  “ (task_tcb_init_stack_call_result critical_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 0 (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) ) ” 
  &&  “ (task_tcb_init_publication_call_observation sg_phase_call_spec (task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease)) current_call current ) ” 
  &&  “ (task_stack_live_coverage (TskState ((task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)))) (task_stack_call_active_key (current_call)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (UCOS2_inv sg_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
).

Definition OS_TCBInit_entail_wit_12 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((task_tcb_init_free_root (sg_phase_call_spec) (acquired_2)) = 0)) (PreH2 : (task_tcb_init_stack_same_call first_call_2 call_phase_call_spec )) (PreH3 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH4 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call_2 acquired_2 )) (PreH5 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 )) (PreH6 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH7 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH8 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH9 : ((os_sched_call_invocation (first_call_2)) = invocation_phase_call_spec)) (PreH10 : ((os_sched_call_origin (first_call_2)) = origin_phase_call_spec)) (PreH11 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH12 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH13 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH14 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH15 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH16 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH17 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH18 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH19 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH20 : (task_stack_live_coverage (TskState (acquired_2)) (task_stack_call_active_key (first_call_2)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired_2 )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call_2 )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec acquired_2 )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> (task_tcb_init_free_root (sg_phase_call_spec) (acquired_2)))
  **  (task_tcb_init_public_without_free_root sg_phase_call_spec acquired_2 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_tcb_init_free_root (sg_phase_call_spec) (acquired_2)))
|--
  EX (acquired: UCOS2_Verify_State)  (first_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_call_result sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 66 acquired ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec acquired ) ” 
  &&  “ (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec acquired )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (UCOS2_inv sg_phase_call_spec acquired )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call_2: OsSchedCallContext) (acquired_2: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((task_tcb_init_free_root (sg_phase_call_spec) (acquired_2)) = 0)) (PreH2 : (task_tcb_init_stack_same_call first_call_2 call_phase_call_spec )) (PreH3 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH4 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call_2 acquired_2 )) (PreH5 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired_2 )) (PreH6 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH7 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH8 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH9 : ((os_sched_call_invocation (first_call_2)) = invocation_phase_call_spec)) (PreH10 : ((os_sched_call_origin (first_call_2)) = origin_phase_call_spec)) (PreH11 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH12 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH13 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH14 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH15 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH16 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH17 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired_2 )) (PreH18 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH19 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 )) (PreH20 : (task_stack_live_coverage (TskState (acquired_2)) (task_stack_call_active_key (first_call_2)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired_2 )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call_2 )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec acquired_2 )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> (task_tcb_init_free_root (sg_phase_call_spec) (acquired_2)))
  **  (task_tcb_init_public_without_free_root sg_phase_call_spec acquired_2 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  EX (acquired: UCOS2_Verify_State)  (first_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_call_result sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 66 acquired ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec acquired ) ” 
  &&  “ (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec acquired )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (UCOS2_inv sg_phase_call_spec acquired )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
).

Definition OS_TCBInit_return_wit_1 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH17 : (task_tcb_init_call_result sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 66 acquired )) (PreH18 : (UCOS2_state_inv sg_phase_call_spec acquired )) (PreH19 : (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call)) )) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr acquired )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  (task_tcb_init_modular_phase_call_post environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec mask_phase_call_spec initial_phase_call_spec call_phase_call_spec 66 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH17 : (task_tcb_init_call_result sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 66 acquired )) (PreH18 : (UCOS2_state_inv sg_phase_call_spec acquired )) (PreH19 : (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call)) )) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr acquired )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  (task_tcb_init_modular_phase_call_post environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec mask_phase_call_spec initial_phase_call_spec call_phase_call_spec 66 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
).

Definition OS_TCBInit_return_wit_1_split_goal_spatial := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH17 : (task_tcb_init_call_result sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 66 acquired )) (PreH18 : (UCOS2_state_inv sg_phase_call_spec acquired )) (PreH19 : (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call)) )) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr acquired )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  (task_tcb_init_modular_phase_call_post environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec mask_phase_call_spec initial_phase_call_spec call_phase_call_spec 66 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
.

Definition OS_TCBInit_return_wit_2 := 
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (lease: TaskStackLease) (cpu_sr: Z) (i: Z) (PreH1 : (task_tcb_init_stack_same_call current_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (current_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH17 : (i = 1)) (PreH18 : (task_tcb_init_stack_call_result critical_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 0 (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH19 : (UCOS2_state_inv sg_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH20 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH21 : (task_tcb_init_publication_call_observation sg_phase_call_spec (task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease)) current_call current )) (PreH22 : (task_stack_live_coverage (TskState ((task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)))) (task_stack_call_active_key (current_call)) )) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec current_call cpu_sr (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) ((os_sched_call_invocation (current_call))) ((os_sched_call_origin (current_call))) (acquired) (slot) (free_image) (lease))) (current)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  (task_tcb_init_modular_phase_call_post environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec mask_phase_call_spec initial_phase_call_spec call_phase_call_spec 0 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
) \/
(
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (lease: TaskStackLease) (cpu_sr: Z) (i: Z) (PreH1 : (task_tcb_init_stack_same_call current_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (current_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH17 : (i = 1)) (PreH18 : (task_tcb_init_stack_call_result critical_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 0 (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH19 : (UCOS2_state_inv sg_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH20 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH21 : (task_tcb_init_publication_call_observation sg_phase_call_spec (task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease)) current_call current )) (PreH22 : (task_stack_live_coverage (TskState ((task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)))) (task_stack_call_active_key (current_call)) )) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec current_call cpu_sr (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) ((os_sched_call_invocation (current_call))) ((os_sched_call_origin (current_call))) (acquired) (slot) (free_image) (lease))) (current)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  (task_tcb_init_modular_phase_call_post environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec mask_phase_call_spec initial_phase_call_spec call_phase_call_spec 0 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
).

Definition OS_TCBInit_return_wit_2_split_goal_spatial := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (lease: TaskStackLease) (cpu_sr: Z) (i: Z) (PreH1 : (task_tcb_init_stack_same_call current_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (current_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH17 : (i = 1)) (PreH18 : (task_tcb_init_stack_call_result critical_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 0 (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH19 : (UCOS2_state_inv sg_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH20 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH21 : (task_tcb_init_publication_call_observation sg_phase_call_spec (task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease)) current_call current )) (PreH22 : (task_stack_live_coverage (TskState ((task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)))) (task_stack_call_active_key (current_call)) )) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec current_call cpu_sr (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) ((os_sched_call_invocation (current_call))) ((os_sched_call_origin (current_call))) (acquired) (slot) (free_image) (lease))) (current)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  (task_tcb_init_modular_phase_call_post environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec mask_phase_call_spec initial_phase_call_spec call_phase_call_spec 0 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
.

Definition OS_TCBInit_partial_solve_wit_1 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (PreH1 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH2 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH3 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH4 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH5 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH6 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) ,
  (task_tcb_init_continuation_call_pre environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec mask_phase_call_spec initial_phase_call_spec call_phase_call_spec )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ”
  &&  (task_tcb_init_continuation_call_pre environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec mask_phase_call_spec initial_phase_call_spec call_phase_call_spec )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
.

Definition OS_TCBInit_partial_solve_wit_2 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (PreH1 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH2 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH3 : (task_tcb_init_entry sg_phase_call_spec (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))) invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec )) (PreH4 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH5 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH6 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH7 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH8 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH9 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH10 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) ,
  (task_tcb_init_continuation_save_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec call_phase_call_spec mask_phase_call_spec initial_phase_call_spec )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))) invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ”
  &&  (task_tcb_init_continuation_save_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec call_phase_call_spec mask_phase_call_spec initial_phase_call_spec )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
.

Definition OS_TCBInit_partial_solve_wit_3_pure := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) (PreH21 : (task_stack_live_coverage (TskState ((task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)))) (task_stack_call_active_key (first_call)) )) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (UCOS2_inv sg_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (tcb64_storage_rep ptcb (tcb_layout_common_image (free_image)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (task_stack_live_coverage (TskState ((task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)))) (task_stack_call_active_key (first_call)) ) ”
.

Definition OS_TCBInit_partial_solve_wit_3_aux := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) (PreH21 : (task_stack_live_coverage (TskState ((task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)))) (task_stack_call_active_key (first_call)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (UCOS2_inv sg_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (tcb64_storage_rep ptcb (tcb_layout_common_image (free_image)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (task_stack_live_coverage (TskState ((task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)))) (task_stack_call_active_key (first_call)) ) ” 
  &&  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (task_stack_live_coverage (TskState ((task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)))) (task_stack_call_active_key (first_call)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (UCOS2_inv sg_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (tcb_layout_common_image (free_image)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
.

Definition OS_TCBInit_partial_solve_wit_3 := OS_TCBInit_partial_solve_wit_3_pure -> OS_TCBInit_partial_solve_wit_3_aux.

Definition OS_TCBInit_partial_solve_wit_4_pure := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) (PreH21 : (task_stack_live_coverage (TskState ((task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)))) (task_stack_call_active_key (first_call)) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_tcb_init_continuation_restore_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr acquired (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (tcb_layout_common_image (free_image)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OS_TCBInit_partial_solve_wit_4_aux := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) (PreH21 : (task_stack_live_coverage (TskState ((task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)))) (task_stack_call_active_key (first_call)) )) ,
  (task_tcb_init_continuation_restore_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr acquired (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (tcb_layout_common_image (free_image)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (task_stack_live_coverage (TskState ((task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)))) (task_stack_call_active_key (first_call)) ) ”
  &&  (task_tcb_init_continuation_restore_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr acquired (task_tcb_init_detached_state ((task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ((os_sched_call_invocation (first_call))) ((os_sched_call_origin (first_call))) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (tcb_layout_common_image (free_image)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
.

Definition OS_TCBInit_partial_solve_wit_4 := OS_TCBInit_partial_solve_wit_4_pure -> OS_TCBInit_partial_solve_wit_4_aux.

Definition OS_TCBInit_partial_solve_wit_5_pure := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (cpu_sr: Z) (ptcb: Z) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ”
.

Definition OS_TCBInit_partial_solve_wit_5_aux := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (cpu_sr: Z) (ptcb: Z) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ”
  &&  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
.

Definition OS_TCBInit_partial_solve_wit_5 := OS_TCBInit_partial_solve_wit_5_pure -> OS_TCBInit_partial_solve_wit_5_aux.

Definition OS_TCBInit_partial_solve_wit_6 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (cpu_sr: Z) (ptcb: Z) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (PreH1 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH2 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH3 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH4 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH5 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH6 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH7 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH8 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH9 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH10 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH11 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH13 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH14 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH15 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH16 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH17 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH18 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH19 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH20 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH21 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH22 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH23 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) ,
  (store_stringLit (LitMap_phase_call_spec (("?"%string))) ("?"%string) )
  **  (task_tcb_init_literal_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) (LitMap_phase_call_spec (("?"%string))) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> ((LitMap_phase_call_spec (("?"%string))) + (0 * sizeof(CHAR))))
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ”
  &&  (store_stringLit (LitMap_phase_call_spec (("?"%string))) ("?"%string) )
  **  (task_tcb_init_literal_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) (LitMap_phase_call_spec (("?"%string))) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> ((LitMap_phase_call_spec (("?"%string))) + (0 * sizeof(CHAR))))
  **  (UIntArray.undef_full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 )
.

Definition OS_TCBInit_partial_solve_wit_7 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (i: Z) (ptcb: Z) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (first_call: OsSchedCallContext) (PreH1 : (i < 1)) (PreH2 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH3 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH4 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH5 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH6 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH7 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH8 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH9 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH10 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH11 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH12 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH13 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH14 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH15 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH16 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH17 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH18 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH19 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH20 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH21 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) (PreH22 : (0 <= i)) (PreH23 : (i <= 1)) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 0 i (zeros (i)) )
  **  (UIntArray.undef_seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") i 1 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  “ (i < 1) ” 
  &&  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 1) ”
  &&  (((&((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") + (i * sizeof(UINT)))) # UInt  |->_)
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.seg &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 0 i (zeros (i)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
.

Definition OS_TCBInit_partial_solve_wit_8 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) (PreH21 : (i = 1)) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args_phase_call_spec) ((tcb_layout_common_image (free_image)))) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (i = 1) ”
  &&  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args_phase_call_spec) ((tcb_layout_common_image (free_image)))) )
.

Definition OS_TCBInit_partial_solve_wit_9 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) (PreH21 : (i = 1)) ,
  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args_phase_call_spec) ((tcb_layout_common_image (free_image)))) )
|--
  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (i = 1) ”
  &&  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args_phase_call_spec) ((tcb_layout_common_image (free_image)))) )
.

Definition OS_TCBInit_partial_solve_wit_10_pure := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) (PreH21 : (i = 1)) ,
  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args_phase_call_spec) ((tcb_layout_common_image (free_image)))) )
|--
  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ”
.

Definition OS_TCBInit_partial_solve_wit_10_aux := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) (PreH21 : (i = 1)) ,
  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args_phase_call_spec) ((tcb_layout_common_image (free_image)))) )
|--
  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (i = 1) ”
  &&  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args_phase_call_spec) ((tcb_layout_common_image (free_image)))) )
.

Definition OS_TCBInit_partial_solve_wit_10 := OS_TCBInit_partial_solve_wit_10_pure -> OS_TCBInit_partial_solve_wit_10_aux.

Definition OS_TCBInit_partial_solve_wit_11 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (ptcb: Z) (i: Z) (checkpoint: UCOS2_Verify_State) (checkpoint_call: OsSchedCallContext) (PreH1 : (task_tcb_init_stack_same_call checkpoint_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec checkpoint )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec checkpoint_call checkpoint )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec checkpoint )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH9 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) checkpoint )) (PreH10 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH11 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH12 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH13 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH14 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH15 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH16 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH17 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH18 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH19 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH20 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH21 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH22 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH23 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH24 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH25 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH26 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH27 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH28 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH29 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) (PreH30 : (i = 1)) ,
  (task_tcb_init_continuation_save_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec checkpoint_call mask_phase_call_spec checkpoint )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args_phase_call_spec) ((tcb_layout_common_image (free_image)))) )
|--
  “ (task_tcb_init_stack_same_call checkpoint_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec checkpoint ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec checkpoint_call checkpoint ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec checkpoint ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) checkpoint ) ” 
  &&  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (i = 1) ”
  &&  (task_tcb_init_continuation_save_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec checkpoint_call mask_phase_call_spec checkpoint )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (tcb64_storage_rep ptcb (task_tcb_init_raw_image (args_phase_call_spec) ((tcb_layout_common_image (free_image)))) )
.

Definition OS_TCBInit_partial_solve_wit_12 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_stack_same_call current_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (current_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) (PreH21 : (i = 1)) (PreH22 : (0 <= prio_pre)) (PreH23 : (prio_pre < 64)) (PreH24 : (0 <= (prio_pre ÷ 8 ))) (PreH25 : ((prio_pre ÷ 8 ) < 8)) (PreH26 : (0 <= (prio_pre % ( 8 ) ))) (PreH27 : ((prio_pre % ( 8 ) ) < 8)) (PreH28 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) current )) (PreH29 : (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired current slot )) (PreH30 : (UCOS2_state_inv sg_phase_call_spec current )) (PreH31 : (task_stack_live_coverage (TskState (current)) (task_stack_call_active_key (current_call)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_used_with_head_prev sg_phase_call_spec current slot )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_tcb_init_ready_group (current))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre ÷ 8 ))) (8))))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg_phase_call_spec) (current)) )
  **  (task_tcb_init_publication_other sg_phase_call_spec current )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  “ (task_tcb_init_stack_same_call current_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec current ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (current_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec current ) ” 
  &&  “ (task_stack_live_coverage (TskState (current)) (task_stack_call_active_key (current_call)) ) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((prio_pre ÷ 8 ) * sizeof(UCHAR)))) # UChar  |-> (Znth (prio_pre ÷ 8 ) (task_tcb_init_ready_rows (current)) 0))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (prio_pre ÷ 8 ) 0 8 (task_tcb_init_ready_rows (current)) )
  **  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_used_with_head_prev sg_phase_call_spec current slot )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_tcb_init_ready_group (current))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre ÷ 8 ))) (8))))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg_phase_call_spec) (current)) )
  **  (task_tcb_init_publication_other sg_phase_call_spec current )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
.

Definition OS_TCBInit_partial_solve_wit_13 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_stack_same_call current_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (current_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) (PreH21 : (i = 1)) (PreH22 : (0 <= prio_pre)) (PreH23 : (prio_pre < 64)) (PreH24 : (0 <= (prio_pre ÷ 8 ))) (PreH25 : ((prio_pre ÷ 8 ) < 8)) (PreH26 : (0 <= (prio_pre % ( 8 ) ))) (PreH27 : ((prio_pre % ( 8 ) ) < 8)) (PreH28 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) current )) (PreH29 : (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired current slot )) (PreH30 : (UCOS2_state_inv sg_phase_call_spec current )) (PreH31 : (task_stack_live_coverage (TskState (current)) (task_stack_call_active_key (current_call)) )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (task_tcb_init_ready_rows (current)) )
  **  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_used_with_head_prev sg_phase_call_spec current slot )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_tcb_init_ready_group (current))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre ÷ 8 ))) (8))))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg_phase_call_spec) (current)) )
  **  (task_tcb_init_publication_other sg_phase_call_spec current )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  “ (task_tcb_init_stack_same_call current_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec current ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (current_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec current ) ” 
  &&  “ (task_stack_live_coverage (TskState (current)) (task_stack_call_active_key (current_call)) ) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((prio_pre ÷ 8 ) * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (prio_pre ÷ 8 ) 0 8 (task_tcb_init_ready_rows (current)) )
  **  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_used_with_head_prev sg_phase_call_spec current slot )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (task_tcb_init_count (current)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_tcb_init_ready_group (current))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre ÷ 8 ))) (8))))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg_phase_call_spec) (current)) )
  **  (task_tcb_init_publication_other sg_phase_call_spec current )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
.

Definition OS_TCBInit_partial_solve_wit_14 := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (cpu_sr: Z) (ptcb: Z) (i: Z) (PreH1 : (task_tcb_init_stack_same_call current_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (current_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) (PreH17 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH18 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH19 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) (PreH20 : (ptcb = (tcb64_addr (sg_phase_call_spec) (slot)))) (PreH21 : (i = 1)) (PreH22 : (0 <= prio_pre)) (PreH23 : (prio_pre < 64)) (PreH24 : (0 <= (prio_pre ÷ 8 ))) (PreH25 : ((prio_pre ÷ 8 ) < 8)) (PreH26 : (0 <= (prio_pre % ( 8 ) ))) (PreH27 : ((prio_pre % ( 8 ) ) < 8)) (PreH28 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) current )) (PreH29 : (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired current slot )) (PreH30 : (UCOS2_state_inv sg_phase_call_spec current )) (PreH31 : (task_stack_live_coverage (TskState (current)) (task_stack_call_active_key (current_call)) )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((prio_pre ÷ 8 )) ((Z.lor (unsigned_last_nbits ((Znth (prio_pre ÷ 8 ) (task_tcb_init_ready_rows (current)) 0)) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre % ( 8 ) ))) (8)))) ((task_tcb_init_ready_rows (current)))) )
  **  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_used_with_head_prev sg_phase_call_spec current slot )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (unsigned_last_nbits (((task_tcb_init_count (current)) + 1 )) (8)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_tcb_init_ready_group (current))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre ÷ 8 ))) (8))))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (task_tcb_init_priority_table (sg_phase_call_spec) (current)) )
  **  (task_tcb_init_publication_other sg_phase_call_spec current )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  “ (task_tcb_init_stack_same_call current_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec current ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (current_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image ) ” 
  &&  “ (ptcb = (tcb64_addr (sg_phase_call_spec) (slot))) ” 
  &&  “ (i = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= (prio_pre ÷ 8 )) ” 
  &&  “ ((prio_pre ÷ 8 ) < 8) ” 
  &&  “ (0 <= (prio_pre % ( 8 ) )) ” 
  &&  “ ((prio_pre % ( 8 ) ) < 8) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) current ) ” 
  &&  “ (task_tcb_init_commit_binding args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired current slot ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec current ) ” 
  &&  “ (task_stack_live_coverage (TskState (current)) (task_stack_call_active_key (current_call)) ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.missing_i ( &( "OSTCBPrioTbl" ) ) prio_pre 0 64 (task_tcb_init_priority_table (sg_phase_call_spec) (current)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((prio_pre ÷ 8 )) ((Z.lor (unsigned_last_nbits ((Znth (prio_pre ÷ 8 ) (task_tcb_init_ready_rows (current)) 0)) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre % ( 8 ) ))) (8)))) ((task_tcb_init_ready_rows (current)))) )
  **  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
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
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> (LitMap_phase_call_spec (("?"%string))))
  **  (UIntArray.full &((ptcb)  # "os_tcb" ->ₛ "OSTCBRegTbl") 1 (zeros (1)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (task_tcb_init_active_head (sg_phase_call_spec) (current)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> ptcb)
  **  (task_tcb_init_used_with_head_prev sg_phase_call_spec current slot )
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> (unsigned_last_nbits (((task_tcb_init_count (current)) + 1 )) (8)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((task_tcb_init_ready_group (current))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (prio_pre ÷ 8 ))) (8))))
  **  (task_tcb_init_publication_other sg_phase_call_spec current )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
.

Definition OS_TCBInit_partial_solve_wit_15_pure := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (lease: TaskStackLease) (cpu_sr: Z) (i: Z) (PreH1 : (task_tcb_init_stack_same_call current_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (current_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH17 : (i = 1)) (PreH18 : (task_tcb_init_stack_call_result critical_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 0 (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH19 : (UCOS2_state_inv sg_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH20 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH21 : (task_tcb_init_publication_call_observation sg_phase_call_spec (task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease)) current_call current )) (PreH22 : (task_stack_live_coverage (TskState ((task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)))) (task_stack_call_active_key (current_call)) )) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (UCOS2_inv sg_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (current_call)) = origin_phase_call_spec) ” 
  &&  “ (task_stack_live_coverage (TskState ((task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)))) (task_stack_call_active_key (current_call)) ) ”
.

Definition OS_TCBInit_partial_solve_wit_15_aux := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (lease: TaskStackLease) (cpu_sr: Z) (i: Z) (PreH1 : (task_tcb_init_stack_same_call current_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (current_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH17 : (i = 1)) (PreH18 : (task_tcb_init_stack_call_result critical_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 0 (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH19 : (UCOS2_state_inv sg_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH20 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH21 : (task_tcb_init_publication_call_observation sg_phase_call_spec (task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease)) current_call current )) (PreH22 : (task_stack_live_coverage (TskState ((task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)))) (task_stack_call_active_key (current_call)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (UCOS2_inv sg_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  “ ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (current_call)) = origin_phase_call_spec) ” 
  &&  “ (task_stack_live_coverage (TskState ((task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)))) (task_stack_call_active_key (current_call)) ) ” 
  &&  “ (task_tcb_init_stack_same_call current_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec current ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (current_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (i = 1) ” 
  &&  “ (task_tcb_init_stack_call_result critical_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 0 (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) ) ” 
  &&  “ (task_tcb_init_publication_call_observation sg_phase_call_spec (task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease)) current_call current ) ” 
  &&  “ (task_stack_live_coverage (TskState ((task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)))) (task_stack_call_active_key (current_call)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (UCOS2_inv sg_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
.

Definition OS_TCBInit_partial_solve_wit_15 := OS_TCBInit_partial_solve_wit_15_pure -> OS_TCBInit_partial_solve_wit_15_aux.

Definition OS_TCBInit_partial_solve_wit_16_pure := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (lease: TaskStackLease) (cpu_sr: Z) (i: Z) (PreH1 : (task_tcb_init_stack_same_call current_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (current_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH17 : (i = 1)) (PreH18 : (task_tcb_init_stack_call_result critical_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 0 (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH19 : (UCOS2_state_inv sg_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH20 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH21 : (task_tcb_init_publication_call_observation sg_phase_call_spec (task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease)) current_call current )) (PreH22 : (task_stack_live_coverage (TskState ((task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)))) (task_stack_call_active_key (current_call)) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_tcb_init_continuation_restore_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec current_call cpu_sr current (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
  **  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OS_TCBInit_partial_solve_wit_16_aux := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (current_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (free_image: TCBLayoutImage) (current: UCOS2_Verify_State) (lease: TaskStackLease) (cpu_sr: Z) (i: Z) (PreH1 : (task_tcb_init_stack_same_call current_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec current )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (current_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH17 : (i = 1)) (PreH18 : (task_tcb_init_stack_call_result critical_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 0 (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH19 : (UCOS2_state_inv sg_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH20 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )) (PreH21 : (task_tcb_init_publication_call_observation sg_phase_call_spec (task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease)) current_call current )) (PreH22 : (task_stack_live_coverage (TskState ((task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)))) (task_stack_call_active_key (current_call)) )) ,
  (task_tcb_init_continuation_restore_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec current_call cpu_sr current (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (task_tcb_init_stack_same_call current_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call current ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec current ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (current_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (i = 1) ” 
  &&  “ (task_tcb_init_stack_call_result critical_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 0 (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) ) ” 
  &&  “ (task_tcb_init_publication_call_observation sg_phase_call_spec (task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease)) current_call current ) ” 
  &&  “ (task_stack_live_coverage (TskState ((task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)))) (task_stack_call_active_key (current_call)) ) ”
  &&  (task_tcb_init_continuation_restore_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec current_call cpu_sr current (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) ((os_sched_call_invocation (current_call))) ((os_sched_call_origin (current_call))) (acquired) (slot) (free_image) (lease))) (current)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
.

Definition OS_TCBInit_partial_solve_wit_16 := OS_TCBInit_partial_solve_wit_16_pure -> OS_TCBInit_partial_solve_wit_16_aux.

Definition OS_TCBInit_partial_solve_wit_17_pure := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH17 : (task_tcb_init_call_result sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 66 acquired )) (PreH18 : (UCOS2_state_inv sg_phase_call_spec acquired )) (PreH19 : (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call)) )) ,
  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec acquired )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (UCOS2_inv sg_phase_call_spec acquired )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call)) ) ”
.

Definition OS_TCBInit_partial_solve_wit_17_aux := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH17 : (task_tcb_init_call_result sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 66 acquired )) (PreH18 : (UCOS2_state_inv sg_phase_call_spec acquired )) (PreH19 : (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec acquired )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (UCOS2_inv sg_phase_call_spec acquired )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call)) ) ” 
  &&  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_call_result sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 66 acquired ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec acquired ) ” 
  &&  “ (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call)) ) ”
  &&  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (UCOS2_inv sg_phase_call_spec acquired )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec acquired )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
.

Definition OS_TCBInit_partial_solve_wit_17 := OS_TCBInit_partial_solve_wit_17_pure -> OS_TCBInit_partial_solve_wit_17_aux.

Definition OS_TCBInit_partial_solve_wit_18_pure := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH17 : (task_tcb_init_call_result sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 66 acquired )) (PreH18 : (UCOS2_state_inv sg_phase_call_spec acquired )) (PreH19 : (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call)) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_tcb_init_continuation_restore_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr acquired acquired )
  **  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pext" ) )) # Ptr  |-> pext_pre)
  **  ((( &( "stk_size" ) )) # UInt  |-> stk_size_pre)
  **  ((( &( "id" ) )) # UShort  |-> id_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos_pre)
  **  ((( &( "ptos" ) )) # Ptr  |-> ptos_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OS_TCBInit_partial_solve_wit_18_aux := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_phase_call_spec: (@list string)) (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH10 : (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))))) (PreH11 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH12 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH13 : (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec )) (PreH14 : (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) )) (PreH15 : (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) )) (PreH16 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH17 : (task_tcb_init_call_result sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 66 acquired )) (PreH18 : (UCOS2_state_inv sg_phase_call_spec acquired )) (PreH19 : (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call)) )) ,
  (task_tcb_init_continuation_restore_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr acquired acquired )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (task_tcb_init_stack_same_call first_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (first_call)) = origin_phase_call_spec) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_call_result sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 66 acquired ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec acquired ) ” 
  &&  “ (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call)) ) ”
  &&  (task_tcb_init_continuation_restore_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr acquired acquired )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec )
.

Definition OS_TCBInit_partial_solve_wit_18 := OS_TCBInit_partial_solve_wit_18_pure -> OS_TCBInit_partial_solve_wit_18_aux.

Definition OS_TCBInit_which_implies_wit_1 := 
(
forall (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) ,
  (task_tcb_init_continuation_call_pre environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec mask_phase_call_spec initial_phase_call_spec call_phase_call_spec )
|--
  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))) invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ”
  &&  (task_tcb_init_continuation_save_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec call_phase_call_spec mask_phase_call_spec initial_phase_call_spec )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
) \/
(
forall (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) ,
  (task_tcb_init_continuation_call_pre environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec mask_phase_call_spec initial_phase_call_spec call_phase_call_spec )
|--
  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ” 
  &&  “ (task_tcb_init_entry sg_phase_call_spec (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))) invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ” 
  &&  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ”
  &&  (task_tcb_init_continuation_save_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec call_phase_call_spec mask_phase_call_spec initial_phase_call_spec )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
).

Definition OS_TCBInit_which_implies_wit_1_split_goal_1 := 
forall (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) ,
  (task_tcb_init_continuation_call_pre environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec mask_phase_call_spec initial_phase_call_spec call_phase_call_spec )
|--
  “ (task_create_stack_layout TaskStackNoVFP region_phase_call_spec create_args_phase_call_spec lower_phase_call_spec upper_phase_call_spec ) ”
.

Definition OS_TCBInit_which_implies_wit_1_split_goal_2 := 
forall (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) ,
  (task_tcb_init_continuation_call_pre environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec mask_phase_call_spec initial_phase_call_spec call_phase_call_spec )
|--
  “ (task_tcb_init_entry sg_phase_call_spec (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string))))) invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec ) ”
.

Definition OS_TCBInit_which_implies_wit_1_split_goal_3 := 
forall (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) ,
  (task_tcb_init_continuation_call_pre environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec mask_phase_call_spec initial_phase_call_spec call_phase_call_spec )
|--
  “ ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec) ”
.

Definition OS_TCBInit_which_implies_wit_1_split_goal_4 := 
forall (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) ,
  (task_tcb_init_continuation_call_pre environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec mask_phase_call_spec initial_phase_call_spec call_phase_call_spec )
|--
  “ ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec) ”
.

Definition OS_TCBInit_which_implies_wit_1_split_goal_spatial := 
forall (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) ,
  (task_tcb_init_continuation_call_pre environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec mask_phase_call_spec initial_phase_call_spec call_phase_call_spec )
|--
  (task_tcb_init_continuation_save_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec call_phase_call_spec mask_phase_call_spec initial_phase_call_spec )
  **  (task_stack_storage region_phase_call_spec (task_create_stack_image (TaskStackNoVFP) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec)) )
.

Definition OS_TCBInit_which_implies_wit_2 := 
(
forall (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (free_image: TCBLayoutImage) (rest: (@list Z)) (slot: Z) (acquired: UCOS2_Verify_State) (first_call: OsSchedCallContext) (cpu_sr: Z) (PreH1 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH2 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH3 : (task_stack_live_coverage (TskState ((task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)))) (task_stack_call_active_key (first_call)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (UCOS2_inv sg_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
|--
  (task_tcb_init_continuation_restore_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr acquired (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
) \/
(
forall (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (free_image: TCBLayoutImage) (rest: (@list Z)) (slot: Z) (acquired: UCOS2_Verify_State) (first_call: OsSchedCallContext) (cpu_sr: Z) (PreH1 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH2 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH3 : (task_stack_live_coverage (TskState ((task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)))) (task_stack_call_active_key (first_call)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (UCOS2_inv sg_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
|--
  (task_tcb_init_continuation_restore_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr acquired (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
).

Definition OS_TCBInit_which_implies_wit_2_split_goal_spatial := 
forall (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (free_image: TCBLayoutImage) (rest: (@list Z)) (slot: Z) (acquired: UCOS2_Verify_State) (first_call: OsSchedCallContext) (cpu_sr: Z) (PreH1 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH2 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH3 : (task_stack_live_coverage (TskState ((task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)))) (task_stack_call_active_key (first_call)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (UCOS2_inv sg_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
|--
  (task_tcb_init_continuation_restore_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr acquired (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
.

Definition OS_TCBInit_which_implies_wit_3 := 
(
forall (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (PreH1 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH2 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH3 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
|--
  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired ) ”
  &&  (store_stringLit (LitMap_phase_call_spec (("?"%string))) ("?"%string) )
  **  (task_tcb_init_literal_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) (LitMap_phase_call_spec (("?"%string))) )
) \/
(
forall (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (PreH1 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH2 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH3 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
|--
  (store_stringLit (LitMap_phase_call_spec (("?"%string))) ("?"%string) )
  **  (task_tcb_init_literal_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) (LitMap_phase_call_spec (("?"%string))) )
).

Definition OS_TCBInit_which_implies_wit_3_split_goal_spatial := 
forall (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) (PreH1 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH2 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH3 : (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec initial_phase_call_spec acquired )) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
|--
  (store_stringLit (LitMap_phase_call_spec (("?"%string))) ("?"%string) )
  **  (task_tcb_init_literal_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) (LitMap_phase_call_spec (("?"%string))) )
.

Definition OS_TCBInit_which_implies_wit_4 := 
(
forall (LitMap_phase_call_spec: (string -> Z)) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) ,
  (store_stringLit (LitMap_phase_call_spec (("?"%string))) ("?"%string) )
  **  (task_tcb_init_literal_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) (LitMap_phase_call_spec (("?"%string))) )
|--
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
) \/
(
forall (LitMap_phase_call_spec: (string -> Z)) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) ,
  (store_stringLit (LitMap_phase_call_spec (("?"%string))) ("?"%string) )
  **  (task_tcb_init_literal_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) (LitMap_phase_call_spec (("?"%string))) )
|--
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
).

Definition OS_TCBInit_which_implies_wit_4_split_goal_spatial := 
forall (LitMap_phase_call_spec: (string -> Z)) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (acquired: UCOS2_Verify_State) (slot: Z) (rest: (@list Z)) (free_image: TCBLayoutImage) (cpu_sr: Z) ,
  (store_stringLit (LitMap_phase_call_spec (("?"%string))) ("?"%string) )
  **  (task_tcb_init_literal_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) (LitMap_phase_call_spec (("?"%string))) )
|--
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
.

Definition OS_TCBInit_which_implies_wit_5 := 
(
forall (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (free_image: TCBLayoutImage) (rest: (@list Z)) (slot: Z) (acquired: UCOS2_Verify_State) (first_call: OsSchedCallContext) (cpu_sr: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH10 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH11 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH12 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
|--
  EX (checkpoint: UCOS2_Verify_State)  (checkpoint_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call checkpoint_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec checkpoint ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec checkpoint_call checkpoint ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec checkpoint ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) checkpoint ) ”
  &&  (task_tcb_init_continuation_save_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec checkpoint_call mask_phase_call_spec checkpoint )
) \/
(
forall (LitMap_phase_call_spec: (string -> Z)) (initial_phase_call_spec: UCOS2_Verify_State) (mask_phase_call_spec: Z) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (call_phase_call_spec: OsSchedCallContext) (args_phase_call_spec: TaskTCBInitArgs) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (free_image: TCBLayoutImage) (rest: (@list Z)) (slot: Z) (acquired: UCOS2_Verify_State) (first_call: OsSchedCallContext) (cpu_sr: Z) (PreH1 : (task_tcb_init_stack_same_call first_call call_phase_call_spec )) (PreH2 : (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec acquired )) (PreH3 : (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired )) (PreH4 : (task_tcb_init_timer_phase_eq initial_phase_call_spec acquired )) (PreH5 : (kernel_sched_ready_clients critical_phase_call_spec )) (PreH6 : (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec )) (PreH7 : (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec )) (PreH8 : ((os_sched_call_invocation (call_phase_call_spec)) = invocation_phase_call_spec)) (PreH9 : ((os_sched_call_origin (call_phase_call_spec)) = origin_phase_call_spec)) (PreH10 : (interrupt_saved_value mask_phase_call_spec cpu_sr )) (PreH11 : (task_tcb_init_entry sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired )) (PreH12 : (task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image )) ,
  (task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) )
|--
  EX (checkpoint: UCOS2_Verify_State)  (checkpoint_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call checkpoint_call call_phase_call_spec ) ” 
  &&  “ (task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec checkpoint ) ” 
  &&  “ (task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec checkpoint_call checkpoint ) ” 
  &&  “ (task_tcb_init_timer_phase_eq initial_phase_call_spec checkpoint ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ” 
  &&  “ (interrupt_saved_value mask_phase_call_spec cpu_sr ) ” 
  &&  “ (task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec (task_tcb_init_detached_state (args_phase_call_spec) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (rest) (free_image)) checkpoint ) ”
  &&  (task_tcb_init_continuation_save_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec checkpoint_call mask_phase_call_spec checkpoint )
).

Definition OS_TCBInit_which_implies_wit_6 := 
(
forall (LitMap_phase_call_spec: (string -> Z)) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (lease: TaskStackLease) (free_image: TCBLayoutImage) (slot: Z) (current: UCOS2_Verify_State) (acquired: UCOS2_Verify_State) (current_call: OsSchedCallContext) (cpu_sr: Z) (PreH1 : ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec)) (PreH2 : ((os_sched_call_origin (current_call)) = origin_phase_call_spec)) (PreH3 : (task_stack_live_coverage (TskState ((task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)))) (task_stack_call_active_key (current_call)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (UCOS2_inv sg_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
|--
  (task_tcb_init_continuation_restore_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec current_call cpu_sr current (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
) \/
(
forall (LitMap_phase_call_spec: (string -> Z)) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (lease: TaskStackLease) (free_image: TCBLayoutImage) (slot: Z) (current: UCOS2_Verify_State) (acquired: UCOS2_Verify_State) (current_call: OsSchedCallContext) (cpu_sr: Z) (PreH1 : ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec)) (PreH2 : ((os_sched_call_origin (current_call)) = origin_phase_call_spec)) (PreH3 : (task_stack_live_coverage (TskState ((task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)))) (task_stack_call_active_key (current_call)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (UCOS2_inv sg_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
|--
  (task_tcb_init_continuation_restore_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec current_call cpu_sr current (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
).

Definition OS_TCBInit_which_implies_wit_6_split_goal_spatial := 
forall (LitMap_phase_call_spec: (string -> Z)) (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (upper_phase_call_spec: (@list (@option Z))) (lower_phase_call_spec: (@list (@option Z))) (task_return_phase_call_spec: Z) (create_args_phase_call_spec: TaskCreateArgs) (region_phase_call_spec: TaskStackRegion) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (lease: TaskStackLease) (free_image: TCBLayoutImage) (slot: Z) (current: UCOS2_Verify_State) (acquired: UCOS2_Verify_State) (current_call: OsSchedCallContext) (cpu_sr: Z) (PreH1 : ((os_sched_call_invocation (current_call)) = invocation_phase_call_spec)) (PreH2 : ((os_sched_call_origin (current_call)) = origin_phase_call_spec)) (PreH3 : (task_stack_live_coverage (TskState ((task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)))) (task_stack_call_active_key (current_call)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current )
  **  (task_tcb_init_stack_context environment_phase_call_spec current_call )
  **  (UCOS2_inv sg_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
|--
  (task_tcb_init_continuation_restore_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec current_call cpu_sr current (task_create_stack_publication_state (sg_phase_call_spec) ((task_tcb_init_stack_publication (region_phase_call_spec) (create_args_phase_call_spec) (task_return_phase_call_spec) (lower_phase_call_spec) (upper_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))) (invocation_phase_call_spec) (origin_phase_call_spec) (acquired) (slot) (free_image) (lease))) (current)) )
.

Definition OS_TCBInit_which_implies_wit_7 := 
(
forall (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (first_call: OsSchedCallContext) (cpu_sr: Z) (PreH1 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH2 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH3 : (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (UCOS2_inv sg_phase_call_spec acquired )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec acquired )
|--
  (task_tcb_init_continuation_restore_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr acquired acquired )
) \/
(
forall (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (first_call: OsSchedCallContext) (cpu_sr: Z) (PreH1 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH2 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH3 : (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (UCOS2_inv sg_phase_call_spec acquired )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec acquired )
|--
  (task_tcb_init_continuation_restore_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr acquired acquired )
).

Definition OS_TCBInit_which_implies_wit_7_split_goal_spatial := 
forall (origin_phase_call_spec: TaskInvocationOrigin) (invocation_phase_call_spec: nat) (sg_phase_call_spec: StableGlobVars) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (critical_phase_call_spec: CriticalRegionResources) (environment_phase_call_spec: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (first_call: OsSchedCallContext) (cpu_sr: Z) (PreH1 : ((os_sched_call_invocation (first_call)) = invocation_phase_call_spec)) (PreH2 : ((os_sched_call_origin (first_call)) = origin_phase_call_spec)) (PreH3 : (task_stack_live_coverage (TskState (acquired)) (task_stack_call_active_key (first_call)) )) ,
  (critical_region_masked (task_stack_call_platform (environment_phase_call_spec)) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr acquired )
  **  (task_tcb_init_stack_context environment_phase_call_spec first_call )
  **  (UCOS2_inv sg_phase_call_spec acquired )
  **  (task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec acquired )
|--
  (task_tcb_init_continuation_restore_input environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec first_call cpu_sr acquired acquired )
.

Definition OS_TCBInit_derive_name_call_spec_by_phase_call_spec := 
forall (opt_pre: Z) (pext_pre: Z) (stk_size_pre: Z) (id_pre: Z) (pbos_pre: Z) (ptos_pre: Z) (prio_pre: Z) (literals_name_call_spec: (@list string)) (LitMap_name_call_spec: (string -> Z)) (initial_name_call_spec: UCOS2_Verify_State) (mask_name_call_spec: Z) (origin_name_call_spec: TaskInvocationOrigin) (invocation_name_call_spec: nat) (call_name_call_spec: OsSchedCallContext) (upper_name_call_spec: (@list (@option Z))) (lower_name_call_spec: (@list (@option Z))) (task_return_name_call_spec: Z) (create_args_name_call_spec: TaskCreateArgs) (region_name_call_spec: TaskStackRegion) (args_name_call_spec: TaskTCBInitArgs) (sg_name_call_spec: StableGlobVars) (saved_local_name_call_spec: (Armv7aContinuation -> Assertion)) (critical_name_call_spec: CriticalRegionResources) (environment_name_call_spec: TaskStackCallEnvironment) ,
  “ (task_tcb_init_global_addresses sg_name_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_name_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_name_call_spec (("?"%string))) ) ” 
  &&  “ (args_name_call_spec = (task_tcb_init_stack_call_args (create_args_name_call_spec) ((LitMap_name_call_spec (("?"%string)))))) ” 
  &&  “ (kernel_sched_ready_clients critical_name_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_name_call_spec (("?"%string))) initial_name_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_name_call_spec initial_name_call_spec ) ”
  &&  (task_tcb_init_continuation_call_pre environment_name_call_spec critical_name_call_spec saved_local_name_call_spec sg_name_call_spec region_name_call_spec create_args_name_call_spec task_return_name_call_spec lower_name_call_spec upper_name_call_spec (LitMap_name_call_spec (("?"%string))) invocation_name_call_spec origin_name_call_spec mask_name_call_spec initial_name_call_spec call_name_call_spec )
  **  (GlobalStrings_missing LitMap_name_call_spec literals_name_call_spec )
|--
EX (environment_phase_call_spec: TaskStackCallEnvironment) (critical_phase_call_spec: CriticalRegionResources) (saved_local_phase_call_spec: (Armv7aContinuation -> Assertion)) (sg_phase_call_spec: StableGlobVars) (args_phase_call_spec: TaskTCBInitArgs) (region_phase_call_spec: TaskStackRegion) (create_args_phase_call_spec: TaskCreateArgs) (task_return_phase_call_spec: Z) (lower_phase_call_spec: (@list (@option Z))) (upper_phase_call_spec: (@list (@option Z))) (call_phase_call_spec: OsSchedCallContext) (invocation_phase_call_spec: nat) (origin_phase_call_spec: TaskInvocationOrigin) (mask_phase_call_spec: Z) (initial_phase_call_spec: UCOS2_Verify_State) (LitMap_phase_call_spec: (string -> Z)) (literals_phase_call_spec: (@list string)) ,
  (“ (task_tcb_init_global_addresses sg_phase_call_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (task_tcb_init_arguments args_phase_call_spec prio_pre ptos_pre pbos_pre id_pre stk_size_pre pext_pre opt_pre (LitMap_phase_call_spec (("?"%string))) ) ” 
  &&  “ (args_phase_call_spec = (task_tcb_init_stack_call_args (create_args_phase_call_spec) ((LitMap_phase_call_spec (("?"%string)))))) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_call_spec ) ” 
  &&  “ (task_create_default_name_binding (LitMap_phase_call_spec (("?"%string))) initial_phase_call_spec ) ” 
  &&  “ (UCOS2_state_inv sg_phase_call_spec initial_phase_call_spec ) ”
  &&  (task_tcb_init_continuation_call_pre environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec mask_phase_call_spec initial_phase_call_spec call_phase_call_spec )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec ))
  **
  ((EX retval_2,
  (task_tcb_init_modular_phase_call_post environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec (("?"%string))) invocation_phase_call_spec origin_phase_call_spec mask_phase_call_spec initial_phase_call_spec call_phase_call_spec retval_2 )
  **  (GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec ))
  -*
  (EX retval,
  (task_tcb_init_modular_name_call_post environment_name_call_spec critical_name_call_spec saved_local_name_call_spec sg_name_call_spec region_name_call_spec create_args_name_call_spec task_return_name_call_spec lower_name_call_spec upper_name_call_spec (LitMap_name_call_spec (("?"%string))) invocation_name_call_spec origin_name_call_spec mask_name_call_spec initial_name_call_spec call_name_call_spec retval )
  **  (GlobalStrings_missing LitMap_name_call_spec literals_name_call_spec )))
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

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
Axiom proof_of_OS_TCBInit_partial_solve_wit_4_pure : OS_TCBInit_partial_solve_wit_4_pure.
Axiom proof_of_OS_TCBInit_partial_solve_wit_4 : OS_TCBInit_partial_solve_wit_4.
Axiom proof_of_OS_TCBInit_partial_solve_wit_5_pure : OS_TCBInit_partial_solve_wit_5_pure.
Axiom proof_of_OS_TCBInit_partial_solve_wit_5 : OS_TCBInit_partial_solve_wit_5.
Axiom proof_of_OS_TCBInit_partial_solve_wit_6 : OS_TCBInit_partial_solve_wit_6.
Axiom proof_of_OS_TCBInit_partial_solve_wit_7 : OS_TCBInit_partial_solve_wit_7.
Axiom proof_of_OS_TCBInit_partial_solve_wit_8 : OS_TCBInit_partial_solve_wit_8.
Axiom proof_of_OS_TCBInit_partial_solve_wit_9 : OS_TCBInit_partial_solve_wit_9.
Axiom proof_of_OS_TCBInit_partial_solve_wit_10_pure : OS_TCBInit_partial_solve_wit_10_pure.
Axiom proof_of_OS_TCBInit_partial_solve_wit_10 : OS_TCBInit_partial_solve_wit_10.
Axiom proof_of_OS_TCBInit_partial_solve_wit_11 : OS_TCBInit_partial_solve_wit_11.
Axiom proof_of_OS_TCBInit_partial_solve_wit_12 : OS_TCBInit_partial_solve_wit_12.
Axiom proof_of_OS_TCBInit_partial_solve_wit_13 : OS_TCBInit_partial_solve_wit_13.
Axiom proof_of_OS_TCBInit_partial_solve_wit_14 : OS_TCBInit_partial_solve_wit_14.
Axiom proof_of_OS_TCBInit_partial_solve_wit_15_pure : OS_TCBInit_partial_solve_wit_15_pure.
Axiom proof_of_OS_TCBInit_partial_solve_wit_15 : OS_TCBInit_partial_solve_wit_15.
Axiom proof_of_OS_TCBInit_partial_solve_wit_16_pure : OS_TCBInit_partial_solve_wit_16_pure.
Axiom proof_of_OS_TCBInit_partial_solve_wit_16 : OS_TCBInit_partial_solve_wit_16.
Axiom proof_of_OS_TCBInit_partial_solve_wit_17_pure : OS_TCBInit_partial_solve_wit_17_pure.
Axiom proof_of_OS_TCBInit_partial_solve_wit_17 : OS_TCBInit_partial_solve_wit_17.
Axiom proof_of_OS_TCBInit_partial_solve_wit_18_pure : OS_TCBInit_partial_solve_wit_18_pure.
Axiom proof_of_OS_TCBInit_partial_solve_wit_18 : OS_TCBInit_partial_solve_wit_18.
Axiom proof_of_OS_TCBInit_which_implies_wit_1 : OS_TCBInit_which_implies_wit_1.
Axiom proof_of_OS_TCBInit_which_implies_wit_2 : OS_TCBInit_which_implies_wit_2.
Axiom proof_of_OS_TCBInit_which_implies_wit_3 : OS_TCBInit_which_implies_wit_3.
Axiom proof_of_OS_TCBInit_which_implies_wit_4 : OS_TCBInit_which_implies_wit_4.
Axiom proof_of_OS_TCBInit_which_implies_wit_5 : OS_TCBInit_which_implies_wit_5.
Axiom proof_of_OS_TCBInit_which_implies_wit_6 : OS_TCBInit_which_implies_wit_6.
Axiom proof_of_OS_TCBInit_which_implies_wit_7 : OS_TCBInit_which_implies_wit_7.
Axiom proof_of_OS_TCBInit_derive_name_call_spec_by_phase_call_spec : OS_TCBInit_derive_name_call_spec_by_phase_call_spec.

End VC_Correct.
