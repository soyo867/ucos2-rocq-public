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
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_hook_isr_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.

(*----- Function OSTimeTick -----*)

Definition OSTimeTick_safety_wit_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (interrupt_saved_value 192 retval )) (PreH2 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH3 : (time_tick_entry sg invocation origin initial )) (PreH4 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH5 : (0 <= counter)) (PreH6 : (counter <= 65535)) (PreH7 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH8 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH9 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  (UCOS2_inv sg hook_state )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeTick_safety_wit_2 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg hook_state )) (PreH2 : (0 <= (time_tick_time (hook_state)))) (PreH3 : (0 <= (time_tick_step (hook_state)))) (PreH4 : ((time_tick_step (hook_state)) < 256)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH7 : (time_tick_entry sg invocation origin initial )) (PreH8 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH9 : (0 <= counter)) (PreH10 : (counter <= 65535)) (PreH11 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH12 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH13 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeTick_safety_wit_3 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_word: Z) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (time_tick_entry sg invocation origin initial )) (PreH3 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH4 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH5 : ((time_tick_process_byte (hook_state)) = 1)) (PreH6 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH7 : (UCOS2_state_inv sg current )) (PreH8 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_word)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition OSTimeTick_safety_wit_4 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (interrupt_saved_value 192 retval )) (PreH2 : (UCOS2_state_inv sg current )) (PreH3 : (time_tick_lookup current tid node )) (PreH4 : (0 <= (time_tick_y (node)))) (PreH5 : ((time_tick_y (node)) < 8)) (PreH6 : (0 <= (time_tick_delay (node)))) (PreH7 : ((time_tick_delay (node)) < 4294967296)) (PreH8 : ((time_tick_priority (node)) <> 63)) (PreH9 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (time_tick_entry sg invocation origin initial )) (PreH11 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH12 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH13 : ((time_tick_process_byte (hook_state)) = 1)) (PreH14 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH15 : (UCOS2_state_inv sg current )) (PreH16 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (time_tick_delay (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (time_tick_pend_result (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeTick_safety_wit_5 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0)) (PreH2 : ((time_tick_delay (node)) <> 0)) (PreH3 : (interrupt_saved_value 192 retval )) (PreH4 : (UCOS2_state_inv sg current )) (PreH5 : (time_tick_lookup current tid node )) (PreH6 : (0 <= (time_tick_y (node)))) (PreH7 : ((time_tick_y (node)) < 8)) (PreH8 : (0 <= (time_tick_delay (node)))) (PreH9 : ((time_tick_delay (node)) < 4294967296)) (PreH10 : ((time_tick_priority (node)) <> 63)) (PreH11 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (time_tick_entry sg invocation origin initial )) (PreH13 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH14 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH15 : ((time_tick_process_byte (hook_state)) = 1)) (PreH16 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH17 : (UCOS2_state_inv sg current )) (PreH18 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (time_tick_pend_result (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (55 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 55) ”
.

Definition OSTimeTick_safety_wit_6 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (time_tick_status (node)) 55) <> 0)) (PreH2 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0)) (PreH3 : ((time_tick_delay (node)) <> 0)) (PreH4 : (interrupt_saved_value 192 retval )) (PreH5 : (UCOS2_state_inv sg current )) (PreH6 : (time_tick_lookup current tid node )) (PreH7 : (0 <= (time_tick_y (node)))) (PreH8 : ((time_tick_y (node)) < 8)) (PreH9 : (0 <= (time_tick_delay (node)))) (PreH10 : ((time_tick_delay (node)) < 4294967296)) (PreH11 : ((time_tick_priority (node)) <> 63)) (PreH12 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (time_tick_entry sg invocation origin initial )) (PreH14 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH15 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH16 : ((time_tick_process_byte (hook_state)) = 1)) (PreH17 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH18 : (UCOS2_state_inv sg current )) (PreH19 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (time_tick_pend_result (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (55 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 55) ”
.

Definition OSTimeTick_safety_wit_7 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))) 8) = 0)) (PreH2 : ((Z.land (time_tick_status (node)) 55) <> 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0)) (PreH4 : ((time_tick_delay (node)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current )) (PreH7 : (time_tick_lookup current tid node )) (PreH8 : (0 <= (time_tick_y (node)))) (PreH9 : ((time_tick_y (node)) < 8)) (PreH10 : (0 <= (time_tick_delay (node)))) (PreH11 : ((time_tick_delay (node)) < 4294967296)) (PreH12 : ((time_tick_priority (node)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH17 : ((time_tick_process_byte (hook_state)) = 1)) (PreH18 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH19 : (UCOS2_state_inv sg current )) (PreH20 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((time_tick_y (node))) ((Z.lor (unsigned_last_nbits ((Znth (time_tick_y (node)) (time_tick_ready_rows (current)) 0)) (8)) (unsigned_last_nbits ((time_tick_bit_x (node))) (8)))) ((time_tick_ready_rows (current)))) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 1)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((time_tick_ready_group (current))) (8)) (unsigned_last_nbits ((time_tick_bit_y (node))) (8))))
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeTick_safety_wit_8 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (time_tick_status (node)) 8) = 0)) (PreH2 : ((Z.land (time_tick_status (node)) 55) = 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0)) (PreH4 : ((time_tick_delay (node)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current )) (PreH7 : (time_tick_lookup current tid node )) (PreH8 : (0 <= (time_tick_y (node)))) (PreH9 : ((time_tick_y (node)) < 8)) (PreH10 : (0 <= (time_tick_delay (node)))) (PreH11 : ((time_tick_delay (node)) < 4294967296)) (PreH12 : ((time_tick_priority (node)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH17 : ((time_tick_process_byte (hook_state)) = 1)) (PreH18 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH19 : (UCOS2_state_inv sg current )) (PreH20 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((time_tick_y (node))) ((Z.lor (unsigned_last_nbits ((Znth (time_tick_y (node)) (time_tick_ready_rows (current)) 0)) (8)) (unsigned_last_nbits ((time_tick_bit_x (node))) (8)))) ((time_tick_ready_rows (current)))) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((time_tick_ready_group (current))) (8)) (unsigned_last_nbits ((time_tick_bit_y (node))) (8))))
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeTick_safety_wit_9 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (time_tick_status (node)) 8) <> 0)) (PreH2 : ((Z.land (time_tick_status (node)) 55) = 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0)) (PreH4 : ((time_tick_delay (node)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current )) (PreH7 : (time_tick_lookup current tid node )) (PreH8 : (0 <= (time_tick_y (node)))) (PreH9 : ((time_tick_y (node)) < 8)) (PreH10 : (0 <= (time_tick_delay (node)))) (PreH11 : ((time_tick_delay (node)) < 4294967296)) (PreH12 : ((time_tick_priority (node)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH17 : ((time_tick_process_byte (hook_state)) = 1)) (PreH18 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH19 : (UCOS2_state_inv sg current )) (PreH20 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeTick_safety_wit_10 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))) 8) <> 0)) (PreH2 : ((Z.land (time_tick_status (node)) 55) <> 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0)) (PreH4 : ((time_tick_delay (node)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current )) (PreH7 : (time_tick_lookup current tid node )) (PreH8 : (0 <= (time_tick_y (node)))) (PreH9 : ((time_tick_y (node)) < 8)) (PreH10 : (0 <= (time_tick_delay (node)))) (PreH11 : ((time_tick_delay (node)) < 4294967296)) (PreH12 : ((time_tick_priority (node)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH17 : ((time_tick_process_byte (hook_state)) = 1)) (PreH18 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH19 : (UCOS2_state_inv sg current )) (PreH20 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 1)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeTick_safety_wit_11 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) <> 0)) (PreH2 : ((time_tick_delay (node)) <> 0)) (PreH3 : (interrupt_saved_value 192 retval )) (PreH4 : (UCOS2_state_inv sg current )) (PreH5 : (time_tick_lookup current tid node )) (PreH6 : (0 <= (time_tick_y (node)))) (PreH7 : ((time_tick_y (node)) < 8)) (PreH8 : (0 <= (time_tick_delay (node)))) (PreH9 : ((time_tick_delay (node)) < 4294967296)) (PreH10 : ((time_tick_priority (node)) <> 63)) (PreH11 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (time_tick_entry sg invocation origin initial )) (PreH13 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH14 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH15 : ((time_tick_process_byte (hook_state)) = 1)) (PreH16 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH17 : (UCOS2_state_inv sg current )) (PreH18 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (time_tick_pend_result (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeTick_safety_wit_12 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((time_tick_delay (node)) = 0)) (PreH2 : (interrupt_saved_value 192 retval )) (PreH3 : (UCOS2_state_inv sg current )) (PreH4 : (time_tick_lookup current tid node )) (PreH5 : (0 <= (time_tick_y (node)))) (PreH6 : ((time_tick_y (node)) < 8)) (PreH7 : (0 <= (time_tick_delay (node)))) (PreH8 : ((time_tick_delay (node)) < 4294967296)) (PreH9 : ((time_tick_priority (node)) <> 63)) (PreH10 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (time_tick_entry sg invocation origin initial )) (PreH12 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : ((time_tick_process_byte (hook_state)) = 1)) (PreH15 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH16 : (UCOS2_state_inv sg current )) (PreH17 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (time_tick_delay (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (time_tick_pend_result (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeTick_entail_wit_1_1 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after_2: Z) (counter_after_2: Z) (hook_state_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state_2)) )) (PreH2 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state_2))) (32)) <> 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state_2)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state_2)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state_2)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state_2))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state_2)) )) (PreH8 : (UCOS2_state_inv sg hook_state_2 )) (PreH9 : (0 <= (time_tick_time (hook_state_2)))) (PreH10 : (0 <= (time_tick_step (hook_state_2)))) (PreH11 : ((time_tick_step (hook_state_2)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after_2 counter_after_2 hook_state_2 )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 = (time_tick_step (hook_state_2)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state_2)) )
  **  ((( &( "step" ) )) # UChar  |-> (time_tick_process_byte (hook_state_2)))
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after_2 counter_address counter_after_2 )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state_2)))
|--
  EX (visited: (@list Z))  (remaining: (@list Z))  (current: UCOS2_Verify_State)  (tid: Z)  (node: TaskAbstractState)  (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after_2: Z) (counter_after_2: Z) (hook_state_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state_2)) )) (PreH2 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state_2))) (32)) <> 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state_2)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state_2)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state_2)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state_2))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state_2)) )) (PreH8 : (UCOS2_state_inv sg hook_state_2 )) (PreH9 : (0 <= (time_tick_time (hook_state_2)))) (PreH10 : (0 <= (time_tick_step (hook_state_2)))) (PreH11 : ((time_tick_step (hook_state_2)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after_2 counter_after_2 hook_state_2 )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 = (time_tick_step (hook_state_2)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state_2)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after_2 counter_address counter_after_2 )
|--
  EX (visited: (@list Z))  (remaining: (@list Z))  (current: UCOS2_Verify_State)  (tid: Z)  (node: TaskAbstractState)  (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ ((time_tick_list_head (sg) (hook_state_2)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((time_tick_process_byte (hook_state_2)) = 1) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
).

Definition OSTimeTick_entail_wit_1_2 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after_2: Z) (counter_after_2: Z) (hook_state_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state_2)) )) (PreH2 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state_2))) (32)) <> 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state_2)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state_2)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state_2)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state_2))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state_2)) )) (PreH8 : (UCOS2_state_inv sg hook_state_2 )) (PreH9 : (0 <= (time_tick_time (hook_state_2)))) (PreH10 : (0 <= (time_tick_step (hook_state_2)))) (PreH11 : ((time_tick_step (hook_state_2)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after_2 counter_after_2 hook_state_2 )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state_2)))) (PreH23 : (1 = (time_tick_step (hook_state_2)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state_2)) )
  **  ((( &( "step" ) )) # UChar  |-> (time_tick_process_byte (hook_state_2)))
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after_2 counter_address counter_after_2 )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state_2)))
|--
  EX (visited: (@list Z))  (remaining: (@list Z))  (current: UCOS2_Verify_State)  (tid: Z)  (node: TaskAbstractState)  (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after_2: Z) (counter_after_2: Z) (hook_state_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state_2)) )) (PreH2 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state_2))) (32)) <> 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state_2)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state_2)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state_2)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state_2))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state_2)) )) (PreH8 : (UCOS2_state_inv sg hook_state_2 )) (PreH9 : (0 <= (time_tick_time (hook_state_2)))) (PreH10 : (0 <= (time_tick_step (hook_state_2)))) (PreH11 : ((time_tick_step (hook_state_2)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after_2 counter_after_2 hook_state_2 )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state_2)))) (PreH23 : (1 = (time_tick_step (hook_state_2)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state_2)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after_2 counter_address counter_after_2 )
|--
  EX (visited: (@list Z))  (remaining: (@list Z))  (current: UCOS2_Verify_State)  (tid: Z)  (node: TaskAbstractState)  (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ ((time_tick_list_head (sg) (hook_state_2)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((time_tick_process_byte (hook_state_2)) = 1) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
).

Definition OSTimeTick_entail_wit_1_3 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after_2: Z) (counter_after_2: Z) (hook_state_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state_2)) )) (PreH2 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state_2))) (32)) <> 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state_2)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state_2)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state_2)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state_2))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state_2)) )) (PreH8 : (UCOS2_state_inv sg hook_state_2 )) (PreH9 : (0 <= (time_tick_time (hook_state_2)))) (PreH10 : (0 <= (time_tick_step (hook_state_2)))) (PreH11 : ((time_tick_step (hook_state_2)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after_2 counter_after_2 hook_state_2 )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state_2)))) (PreH23 : (1 <> (time_tick_step (hook_state_2)))) (PreH24 : (2 = (time_tick_step (hook_state_2)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state_2)) )
  **  ((( &( "step" ) )) # UChar  |-> (time_tick_process_byte (hook_state_2)))
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after_2 counter_address counter_after_2 )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state_2)))
|--
  EX (visited: (@list Z))  (remaining: (@list Z))  (current: UCOS2_Verify_State)  (tid: Z)  (node: TaskAbstractState)  (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after_2: Z) (counter_after_2: Z) (hook_state_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state_2)) )) (PreH2 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state_2))) (32)) <> 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state_2)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state_2)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state_2)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state_2))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state_2)) )) (PreH8 : (UCOS2_state_inv sg hook_state_2 )) (PreH9 : (0 <= (time_tick_time (hook_state_2)))) (PreH10 : (0 <= (time_tick_step (hook_state_2)))) (PreH11 : ((time_tick_step (hook_state_2)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after_2 counter_after_2 hook_state_2 )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state_2)))) (PreH23 : (1 <> (time_tick_step (hook_state_2)))) (PreH24 : (2 = (time_tick_step (hook_state_2)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state_2)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after_2 counter_address counter_after_2 )
|--
  EX (visited: (@list Z))  (remaining: (@list Z))  (current: UCOS2_Verify_State)  (tid: Z)  (node: TaskAbstractState)  (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ ((time_tick_list_head (sg) (hook_state_2)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((time_tick_process_byte (hook_state_2)) = 1) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
).

Definition OSTimeTick_entail_wit_1_4 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after_2: Z) (counter_after_2: Z) (hook_state_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state_2)) )) (PreH2 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state_2))) (32)) <> 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state_2)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state_2)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state_2)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state_2))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state_2)) )) (PreH8 : (UCOS2_state_inv sg hook_state_2 )) (PreH9 : (0 <= (time_tick_time (hook_state_2)))) (PreH10 : (0 <= (time_tick_step (hook_state_2)))) (PreH11 : ((time_tick_step (hook_state_2)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after_2 counter_after_2 hook_state_2 )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state_2)))) (PreH23 : (1 <> (time_tick_step (hook_state_2)))) (PreH24 : (2 <> (time_tick_step (hook_state_2)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state_2)) )
  **  ((( &( "step" ) )) # UChar  |-> (time_tick_process_byte (hook_state_2)))
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after_2 counter_address counter_after_2 )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state_2)))
|--
  EX (visited: (@list Z))  (remaining: (@list Z))  (current: UCOS2_Verify_State)  (tid: Z)  (node: TaskAbstractState)  (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after_2: Z) (counter_after_2: Z) (hook_state_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state_2)) )) (PreH2 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state_2))) (32)) <> 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state_2)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state_2)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state_2)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state_2))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state_2)) )) (PreH8 : (UCOS2_state_inv sg hook_state_2 )) (PreH9 : (0 <= (time_tick_time (hook_state_2)))) (PreH10 : (0 <= (time_tick_step (hook_state_2)))) (PreH11 : ((time_tick_step (hook_state_2)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after_2 counter_after_2 hook_state_2 )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state_2)))) (PreH23 : (1 <> (time_tick_step (hook_state_2)))) (PreH24 : (2 <> (time_tick_step (hook_state_2)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state_2)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after_2 counter_address counter_after_2 )
|--
  EX (visited: (@list Z))  (remaining: (@list Z))  (current: UCOS2_Verify_State)  (tid: Z)  (node: TaskAbstractState)  (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ ((time_tick_list_head (sg) (hook_state_2)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((time_tick_process_byte (hook_state_2)) = 1) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
).

Definition OSTimeTick_entail_wit_2_1 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited_2: (@list Z)) (remaining_2: (@list Z)) (current_2: UCOS2_Verify_State) (tid_2: Z) (node_2: TaskAbstractState) (app_after_2: Z) (counter_after_2: Z) (hook_state_2: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (Z.land (time_tick_status (node_2)) (unsigned_last_nbits ((Z.lnot 55)) (8))) 8) = 0)) (PreH2 : ((Z.land (time_tick_status (node_2)) 55) <> 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)) = 0)) (PreH4 : ((time_tick_delay (node_2)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current_2 )) (PreH7 : (time_tick_lookup current_2 tid_2 node_2 )) (PreH8 : (0 <= (time_tick_y (node_2)))) (PreH9 : ((time_tick_y (node_2)) < 8)) (PreH10 : (0 <= (time_tick_delay (node_2)))) (PreH11 : ((time_tick_delay (node_2)) < 4294967296)) (PreH12 : ((time_tick_priority (node_2)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after_2 counter_after_2 hook_state_2 )) (PreH17 : ((time_tick_process_byte (hook_state_2)) = 1)) (PreH18 : (time_tick_cursor sg hook_state_2 visited_2 remaining_2 current_2 tid_2 node_2 )) (PreH19 : (UCOS2_state_inv sg current_2 )) (PreH20 : (time_tick_lookup current_2 tid_2 node_2 )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((time_tick_y (node_2))) ((Z.lor (unsigned_last_nbits ((Znth (time_tick_y (node_2)) (time_tick_ready_rows (current_2)) 0)) (8)) (unsigned_last_nbits ((time_tick_bit_x (node_2))) (8)))) ((time_tick_ready_rows (current_2)))) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_next (sg) (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (time_tick_status (node_2)) (unsigned_last_nbits ((Z.lnot 55)) (8))))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 1)
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((time_tick_ready_group (current_2))) (8)) (unsigned_last_nbits ((time_tick_bit_y (node_2))) (8))))
  **  (time_tick_body_residual sg current_2 tid_2 node_2 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after_2 counter_address counter_after_2 )
|--
  EX (visited: (@list Z))  (remaining: (@list Z))  (current: UCOS2_Verify_State)  (tid: Z)  (node: TaskAbstractState)  (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited_2: (@list Z)) (remaining_2: (@list Z)) (current_2: UCOS2_Verify_State) (tid_2: Z) (node_2: TaskAbstractState) (app_after_2: Z) (counter_after_2: Z) (hook_state_2: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)) >= 0)) (PreH3 : ((Z.land (Z.land (time_tick_status (node_2)) (unsigned_last_nbits ((Z.lnot 55)) (8))) 8) = 0)) (PreH4 : ((Z.land (time_tick_status (node_2)) 55) <> 0)) (PreH5 : ((unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)) = 0)) (PreH6 : ((time_tick_delay (node_2)) <> 0)) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (UCOS2_state_inv sg current_2 )) (PreH9 : (time_tick_lookup current_2 tid_2 node_2 )) (PreH10 : (0 <= (time_tick_y (node_2)))) (PreH11 : ((time_tick_y (node_2)) < 8)) (PreH12 : (0 <= (time_tick_delay (node_2)))) (PreH13 : ((time_tick_delay (node_2)) < 4294967296)) (PreH14 : ((time_tick_priority (node_2)) <> 63)) (PreH15 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (time_tick_entry sg invocation origin initial )) (PreH17 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH18 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after_2 counter_after_2 hook_state_2 )) (PreH19 : ((time_tick_process_byte (hook_state_2)) = 1)) (PreH20 : (time_tick_cursor sg hook_state_2 visited_2 remaining_2 current_2 tid_2 node_2 )) (PreH21 : (UCOS2_state_inv sg current_2 )) (PreH22 : (time_tick_lookup current_2 tid_2 node_2 )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((time_tick_y (node_2))) ((Z.lor (unsigned_last_nbits ((Znth (time_tick_y (node_2)) (time_tick_ready_rows (current_2)) 0)) (8)) (unsigned_last_nbits ((time_tick_bit_x (node_2))) (8)))) ((time_tick_ready_rows (current_2)))) )
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (time_tick_status (node_2)) (unsigned_last_nbits ((Z.lnot 55)) (8))))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 1)
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((time_tick_ready_group (current_2))) (8)) (unsigned_last_nbits ((time_tick_bit_y (node_2))) (8))))
  **  (time_tick_body_residual sg current_2 tid_2 node_2 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after_2 counter_address counter_after_2 )
|--
  EX (visited: (@list Z))  (remaining: (@list Z))  (current: UCOS2_Verify_State)  (tid: Z)  (node: TaskAbstractState)  (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ ((time_tick_next (sg) (node_2)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
).

Definition OSTimeTick_entail_wit_2_2 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited_2: (@list Z)) (remaining_2: (@list Z)) (current_2: UCOS2_Verify_State) (tid_2: Z) (node_2: TaskAbstractState) (app_after_2: Z) (counter_after_2: Z) (hook_state_2: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (time_tick_status (node_2)) 8) = 0)) (PreH2 : ((Z.land (time_tick_status (node_2)) 55) = 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)) = 0)) (PreH4 : ((time_tick_delay (node_2)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current_2 )) (PreH7 : (time_tick_lookup current_2 tid_2 node_2 )) (PreH8 : (0 <= (time_tick_y (node_2)))) (PreH9 : ((time_tick_y (node_2)) < 8)) (PreH10 : (0 <= (time_tick_delay (node_2)))) (PreH11 : ((time_tick_delay (node_2)) < 4294967296)) (PreH12 : ((time_tick_priority (node_2)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after_2 counter_after_2 hook_state_2 )) (PreH17 : ((time_tick_process_byte (hook_state_2)) = 1)) (PreH18 : (time_tick_cursor sg hook_state_2 visited_2 remaining_2 current_2 tid_2 node_2 )) (PreH19 : (UCOS2_state_inv sg current_2 )) (PreH20 : (time_tick_lookup current_2 tid_2 node_2 )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((time_tick_y (node_2))) ((Z.lor (unsigned_last_nbits ((Znth (time_tick_y (node_2)) (time_tick_ready_rows (current_2)) 0)) (8)) (unsigned_last_nbits ((time_tick_bit_x (node_2))) (8)))) ((time_tick_ready_rows (current_2)))) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_next (sg) (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((time_tick_ready_group (current_2))) (8)) (unsigned_last_nbits ((time_tick_bit_y (node_2))) (8))))
  **  (time_tick_body_residual sg current_2 tid_2 node_2 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after_2 counter_address counter_after_2 )
|--
  EX (visited: (@list Z))  (remaining: (@list Z))  (current: UCOS2_Verify_State)  (tid: Z)  (node: TaskAbstractState)  (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited_2: (@list Z)) (remaining_2: (@list Z)) (current_2: UCOS2_Verify_State) (tid_2: Z) (node_2: TaskAbstractState) (app_after_2: Z) (counter_after_2: Z) (hook_state_2: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)) >= 0)) (PreH3 : ((Z.land (time_tick_status (node_2)) 8) = 0)) (PreH4 : ((Z.land (time_tick_status (node_2)) 55) = 0)) (PreH5 : ((unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)) = 0)) (PreH6 : ((time_tick_delay (node_2)) <> 0)) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (UCOS2_state_inv sg current_2 )) (PreH9 : (time_tick_lookup current_2 tid_2 node_2 )) (PreH10 : (0 <= (time_tick_y (node_2)))) (PreH11 : ((time_tick_y (node_2)) < 8)) (PreH12 : (0 <= (time_tick_delay (node_2)))) (PreH13 : ((time_tick_delay (node_2)) < 4294967296)) (PreH14 : ((time_tick_priority (node_2)) <> 63)) (PreH15 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (time_tick_entry sg invocation origin initial )) (PreH17 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH18 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after_2 counter_after_2 hook_state_2 )) (PreH19 : ((time_tick_process_byte (hook_state_2)) = 1)) (PreH20 : (time_tick_cursor sg hook_state_2 visited_2 remaining_2 current_2 tid_2 node_2 )) (PreH21 : (UCOS2_state_inv sg current_2 )) (PreH22 : (time_tick_lookup current_2 tid_2 node_2 )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((time_tick_y (node_2))) ((Z.lor (unsigned_last_nbits ((Znth (time_tick_y (node_2)) (time_tick_ready_rows (current_2)) 0)) (8)) (unsigned_last_nbits ((time_tick_bit_x (node_2))) (8)))) ((time_tick_ready_rows (current_2)))) )
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((time_tick_ready_group (current_2))) (8)) (unsigned_last_nbits ((time_tick_bit_y (node_2))) (8))))
  **  (time_tick_body_residual sg current_2 tid_2 node_2 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after_2 counter_address counter_after_2 )
|--
  EX (visited: (@list Z))  (remaining: (@list Z))  (current: UCOS2_Verify_State)  (tid: Z)  (node: TaskAbstractState)  (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ ((time_tick_next (sg) (node_2)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
).

Definition OSTimeTick_entail_wit_2_3 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited_2: (@list Z)) (remaining_2: (@list Z)) (current_2: UCOS2_Verify_State) (tid_2: Z) (node_2: TaskAbstractState) (app_after_2: Z) (counter_after_2: Z) (hook_state_2: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (time_tick_status (node_2)) 8) <> 0)) (PreH2 : ((Z.land (time_tick_status (node_2)) 55) = 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)) = 0)) (PreH4 : ((time_tick_delay (node_2)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current_2 )) (PreH7 : (time_tick_lookup current_2 tid_2 node_2 )) (PreH8 : (0 <= (time_tick_y (node_2)))) (PreH9 : ((time_tick_y (node_2)) < 8)) (PreH10 : (0 <= (time_tick_delay (node_2)))) (PreH11 : ((time_tick_delay (node_2)) < 4294967296)) (PreH12 : ((time_tick_priority (node_2)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after_2 counter_after_2 hook_state_2 )) (PreH17 : ((time_tick_process_byte (hook_state_2)) = 1)) (PreH18 : (time_tick_cursor sg hook_state_2 visited_2 remaining_2 current_2 tid_2 node_2 )) (PreH19 : (UCOS2_state_inv sg current_2 )) (PreH20 : (time_tick_lookup current_2 tid_2 node_2 )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_next (sg) (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current_2)) )
  **  (time_tick_body_residual sg current_2 tid_2 node_2 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after_2 counter_address counter_after_2 )
|--
  EX (visited: (@list Z))  (remaining: (@list Z))  (current: UCOS2_Verify_State)  (tid: Z)  (node: TaskAbstractState)  (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited_2: (@list Z)) (remaining_2: (@list Z)) (current_2: UCOS2_Verify_State) (tid_2: Z) (node_2: TaskAbstractState) (app_after_2: Z) (counter_after_2: Z) (hook_state_2: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)) >= 0)) (PreH3 : ((Z.land (time_tick_status (node_2)) 8) <> 0)) (PreH4 : ((Z.land (time_tick_status (node_2)) 55) = 0)) (PreH5 : ((unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)) = 0)) (PreH6 : ((time_tick_delay (node_2)) <> 0)) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (UCOS2_state_inv sg current_2 )) (PreH9 : (time_tick_lookup current_2 tid_2 node_2 )) (PreH10 : (0 <= (time_tick_y (node_2)))) (PreH11 : ((time_tick_y (node_2)) < 8)) (PreH12 : (0 <= (time_tick_delay (node_2)))) (PreH13 : ((time_tick_delay (node_2)) < 4294967296)) (PreH14 : ((time_tick_priority (node_2)) <> 63)) (PreH15 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (time_tick_entry sg invocation origin initial )) (PreH17 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH18 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after_2 counter_after_2 hook_state_2 )) (PreH19 : ((time_tick_process_byte (hook_state_2)) = 1)) (PreH20 : (time_tick_cursor sg hook_state_2 visited_2 remaining_2 current_2 tid_2 node_2 )) (PreH21 : (UCOS2_state_inv sg current_2 )) (PreH22 : (time_tick_lookup current_2 tid_2 node_2 )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current_2)) )
  **  (time_tick_body_residual sg current_2 tid_2 node_2 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after_2 counter_address counter_after_2 )
|--
  EX (visited: (@list Z))  (remaining: (@list Z))  (current: UCOS2_Verify_State)  (tid: Z)  (node: TaskAbstractState)  (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ ((time_tick_next (sg) (node_2)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
).

Definition OSTimeTick_entail_wit_2_4 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited_2: (@list Z)) (remaining_2: (@list Z)) (current_2: UCOS2_Verify_State) (tid_2: Z) (node_2: TaskAbstractState) (app_after_2: Z) (counter_after_2: Z) (hook_state_2: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (Z.land (time_tick_status (node_2)) (unsigned_last_nbits ((Z.lnot 55)) (8))) 8) <> 0)) (PreH2 : ((Z.land (time_tick_status (node_2)) 55) <> 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)) = 0)) (PreH4 : ((time_tick_delay (node_2)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current_2 )) (PreH7 : (time_tick_lookup current_2 tid_2 node_2 )) (PreH8 : (0 <= (time_tick_y (node_2)))) (PreH9 : ((time_tick_y (node_2)) < 8)) (PreH10 : (0 <= (time_tick_delay (node_2)))) (PreH11 : ((time_tick_delay (node_2)) < 4294967296)) (PreH12 : ((time_tick_priority (node_2)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after_2 counter_after_2 hook_state_2 )) (PreH17 : ((time_tick_process_byte (hook_state_2)) = 1)) (PreH18 : (time_tick_cursor sg hook_state_2 visited_2 remaining_2 current_2 tid_2 node_2 )) (PreH19 : (UCOS2_state_inv sg current_2 )) (PreH20 : (time_tick_lookup current_2 tid_2 node_2 )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_next (sg) (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (time_tick_status (node_2)) (unsigned_last_nbits ((Z.lnot 55)) (8))))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 1)
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current_2)) )
  **  (time_tick_body_residual sg current_2 tid_2 node_2 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after_2 counter_address counter_after_2 )
|--
  EX (visited: (@list Z))  (remaining: (@list Z))  (current: UCOS2_Verify_State)  (tid: Z)  (node: TaskAbstractState)  (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited_2: (@list Z)) (remaining_2: (@list Z)) (current_2: UCOS2_Verify_State) (tid_2: Z) (node_2: TaskAbstractState) (app_after_2: Z) (counter_after_2: Z) (hook_state_2: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)) >= 0)) (PreH3 : ((Z.land (Z.land (time_tick_status (node_2)) (unsigned_last_nbits ((Z.lnot 55)) (8))) 8) <> 0)) (PreH4 : ((Z.land (time_tick_status (node_2)) 55) <> 0)) (PreH5 : ((unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)) = 0)) (PreH6 : ((time_tick_delay (node_2)) <> 0)) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (UCOS2_state_inv sg current_2 )) (PreH9 : (time_tick_lookup current_2 tid_2 node_2 )) (PreH10 : (0 <= (time_tick_y (node_2)))) (PreH11 : ((time_tick_y (node_2)) < 8)) (PreH12 : (0 <= (time_tick_delay (node_2)))) (PreH13 : ((time_tick_delay (node_2)) < 4294967296)) (PreH14 : ((time_tick_priority (node_2)) <> 63)) (PreH15 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (time_tick_entry sg invocation origin initial )) (PreH17 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH18 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after_2 counter_after_2 hook_state_2 )) (PreH19 : ((time_tick_process_byte (hook_state_2)) = 1)) (PreH20 : (time_tick_cursor sg hook_state_2 visited_2 remaining_2 current_2 tid_2 node_2 )) (PreH21 : (UCOS2_state_inv sg current_2 )) (PreH22 : (time_tick_lookup current_2 tid_2 node_2 )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (time_tick_status (node_2)) (unsigned_last_nbits ((Z.lnot 55)) (8))))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 1)
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current_2)) )
  **  (time_tick_body_residual sg current_2 tid_2 node_2 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after_2 counter_address counter_after_2 )
|--
  EX (visited: (@list Z))  (remaining: (@list Z))  (current: UCOS2_Verify_State)  (tid: Z)  (node: TaskAbstractState)  (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ ((time_tick_next (sg) (node_2)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
).

Definition OSTimeTick_entail_wit_2_5 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited_2: (@list Z)) (remaining_2: (@list Z)) (current_2: UCOS2_Verify_State) (tid_2: Z) (node_2: TaskAbstractState) (app_after_2: Z) (counter_after_2: Z) (hook_state_2: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)) <> 0)) (PreH2 : ((time_tick_delay (node_2)) <> 0)) (PreH3 : (interrupt_saved_value 192 retval )) (PreH4 : (UCOS2_state_inv sg current_2 )) (PreH5 : (time_tick_lookup current_2 tid_2 node_2 )) (PreH6 : (0 <= (time_tick_y (node_2)))) (PreH7 : ((time_tick_y (node_2)) < 8)) (PreH8 : (0 <= (time_tick_delay (node_2)))) (PreH9 : ((time_tick_delay (node_2)) < 4294967296)) (PreH10 : ((time_tick_priority (node_2)) <> 63)) (PreH11 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (time_tick_entry sg invocation origin initial )) (PreH13 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH14 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after_2 counter_after_2 hook_state_2 )) (PreH15 : ((time_tick_process_byte (hook_state_2)) = 1)) (PreH16 : (time_tick_cursor sg hook_state_2 visited_2 remaining_2 current_2 tid_2 node_2 )) (PreH17 : (UCOS2_state_inv sg current_2 )) (PreH18 : (time_tick_lookup current_2 tid_2 node_2 )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_next (sg) (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (time_tick_pend_result (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current_2)) )
  **  (time_tick_body_residual sg current_2 tid_2 node_2 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after_2 counter_address counter_after_2 )
|--
  EX (visited: (@list Z))  (remaining: (@list Z))  (current: UCOS2_Verify_State)  (tid: Z)  (node: TaskAbstractState)  (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited_2: (@list Z)) (remaining_2: (@list Z)) (current_2: UCOS2_Verify_State) (tid_2: Z) (node_2: TaskAbstractState) (app_after_2: Z) (counter_after_2: Z) (hook_state_2: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)) >= 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)) <> 0)) (PreH4 : ((time_tick_delay (node_2)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current_2 )) (PreH7 : (time_tick_lookup current_2 tid_2 node_2 )) (PreH8 : (0 <= (time_tick_y (node_2)))) (PreH9 : ((time_tick_y (node_2)) < 8)) (PreH10 : (0 <= (time_tick_delay (node_2)))) (PreH11 : ((time_tick_delay (node_2)) < 4294967296)) (PreH12 : ((time_tick_priority (node_2)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after_2 counter_after_2 hook_state_2 )) (PreH17 : ((time_tick_process_byte (hook_state_2)) = 1)) (PreH18 : (time_tick_cursor sg hook_state_2 visited_2 remaining_2 current_2 tid_2 node_2 )) (PreH19 : (UCOS2_state_inv sg current_2 )) (PreH20 : (time_tick_lookup current_2 tid_2 node_2 )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node_2)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (time_tick_pend_result (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current_2)) )
  **  (time_tick_body_residual sg current_2 tid_2 node_2 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after_2 counter_address counter_after_2 )
|--
  EX (visited: (@list Z))  (remaining: (@list Z))  (current: UCOS2_Verify_State)  (tid: Z)  (node: TaskAbstractState)  (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ ((time_tick_next (sg) (node_2)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
).

Definition OSTimeTick_entail_wit_2_6 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited_2: (@list Z)) (remaining_2: (@list Z)) (current_2: UCOS2_Verify_State) (tid_2: Z) (node_2: TaskAbstractState) (app_after_2: Z) (counter_after_2: Z) (hook_state_2: UCOS2_Verify_State) (retval: Z) (PreH1 : ((time_tick_delay (node_2)) = 0)) (PreH2 : (interrupt_saved_value 192 retval )) (PreH3 : (UCOS2_state_inv sg current_2 )) (PreH4 : (time_tick_lookup current_2 tid_2 node_2 )) (PreH5 : (0 <= (time_tick_y (node_2)))) (PreH6 : ((time_tick_y (node_2)) < 8)) (PreH7 : (0 <= (time_tick_delay (node_2)))) (PreH8 : ((time_tick_delay (node_2)) < 4294967296)) (PreH9 : ((time_tick_priority (node_2)) <> 63)) (PreH10 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (time_tick_entry sg invocation origin initial )) (PreH12 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after_2 counter_after_2 hook_state_2 )) (PreH14 : ((time_tick_process_byte (hook_state_2)) = 1)) (PreH15 : (time_tick_cursor sg hook_state_2 visited_2 remaining_2 current_2 tid_2 node_2 )) (PreH16 : (UCOS2_state_inv sg current_2 )) (PreH17 : (time_tick_lookup current_2 tid_2 node_2 )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_next (sg) (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (time_tick_delay (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (time_tick_pend_result (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current_2)) )
  **  (time_tick_body_residual sg current_2 tid_2 node_2 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after_2 counter_address counter_after_2 )
|--
  EX (visited: (@list Z))  (remaining: (@list Z))  (current: UCOS2_Verify_State)  (tid: Z)  (node: TaskAbstractState)  (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited_2: (@list Z)) (remaining_2: (@list Z)) (current_2: UCOS2_Verify_State) (tid_2: Z) (node_2: TaskAbstractState) (app_after_2: Z) (counter_after_2: Z) (hook_state_2: UCOS2_Verify_State) (retval: Z) (PreH1 : ((time_tick_delay (node_2)) <= UINT_MAX)) (PreH2 : ((time_tick_delay (node_2)) >= 0)) (PreH3 : ((time_tick_delay (node_2)) = 0)) (PreH4 : (interrupt_saved_value 192 retval )) (PreH5 : (UCOS2_state_inv sg current_2 )) (PreH6 : (time_tick_lookup current_2 tid_2 node_2 )) (PreH7 : (0 <= (time_tick_y (node_2)))) (PreH8 : ((time_tick_y (node_2)) < 8)) (PreH9 : (0 <= (time_tick_delay (node_2)))) (PreH10 : ((time_tick_delay (node_2)) < 4294967296)) (PreH11 : ((time_tick_priority (node_2)) <> 63)) (PreH12 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (time_tick_entry sg invocation origin initial )) (PreH14 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH15 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after_2 counter_after_2 hook_state_2 )) (PreH16 : ((time_tick_process_byte (hook_state_2)) = 1)) (PreH17 : (time_tick_cursor sg hook_state_2 visited_2 remaining_2 current_2 tid_2 node_2 )) (PreH18 : (UCOS2_state_inv sg current_2 )) (PreH19 : (time_tick_lookup current_2 tid_2 node_2 )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (time_tick_delay (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (time_tick_pend_result (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node_2)))
  **  ((&(((task_slot_addr (sg) (tid_2)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node_2)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current_2)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current_2)) )
  **  (time_tick_body_residual sg current_2 tid_2 node_2 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after_2 counter_address counter_after_2 )
|--
  EX (visited: (@list Z))  (remaining: (@list Z))  (current: UCOS2_Verify_State)  (tid: Z)  (node: TaskAbstractState)  (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ ((time_tick_next (sg) (node_2)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
).

Definition OSTimeTick_return_wit_1 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) = 0)) (PreH2 : ((time_tick_process_byte (hook_state)) = (time_tick_process_byte (hook_state)))) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 = (time_tick_step (hook_state)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  (time_tick_post platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) = 0)) (PreH2 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH3 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH4 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH5 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH6 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH7 : (UCOS2_state_inv sg hook_state )) (PreH8 : (0 <= (time_tick_time (hook_state)))) (PreH9 : (0 <= (time_tick_step (hook_state)))) (PreH10 : ((time_tick_step (hook_state)) < 256)) (PreH11 : (interrupt_saved_value 192 retval )) (PreH12 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH13 : (time_tick_entry sg invocation origin initial )) (PreH14 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH15 : (0 <= counter)) (PreH16 : (counter <= 65535)) (PreH17 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH18 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH19 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (0 = (time_tick_step (hook_state)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  (time_tick_post platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
).

Definition OSTimeTick_return_wit_1_split_goal_spatial := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) = 0)) (PreH2 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH3 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH4 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH5 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH6 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH7 : (UCOS2_state_inv sg hook_state )) (PreH8 : (0 <= (time_tick_time (hook_state)))) (PreH9 : (0 <= (time_tick_step (hook_state)))) (PreH10 : ((time_tick_step (hook_state)) < 256)) (PreH11 : (interrupt_saved_value 192 retval )) (PreH12 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH13 : (time_tick_entry sg invocation origin initial )) (PreH14 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH15 : (0 <= counter)) (PreH16 : (counter <= 65535)) (PreH17 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH18 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH19 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (0 = (time_tick_step (hook_state)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  (time_tick_post platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
.

Definition OSTimeTick_return_wit_2 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) = 0)) (PreH2 : ((time_tick_process_byte (hook_state)) = (time_tick_process_byte (hook_state)))) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 = (time_tick_step (hook_state)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  (time_tick_post platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) = 0)) (PreH2 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH3 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH4 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH5 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH6 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH7 : (UCOS2_state_inv sg hook_state )) (PreH8 : (0 <= (time_tick_time (hook_state)))) (PreH9 : (0 <= (time_tick_step (hook_state)))) (PreH10 : ((time_tick_step (hook_state)) < 256)) (PreH11 : (interrupt_saved_value 192 retval )) (PreH12 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH13 : (time_tick_entry sg invocation origin initial )) (PreH14 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH15 : (0 <= counter)) (PreH16 : (counter <= 65535)) (PreH17 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH18 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH19 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (0 <> (time_tick_step (hook_state)))) (PreH22 : (1 = (time_tick_step (hook_state)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  (time_tick_post platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
).

Definition OSTimeTick_return_wit_2_split_goal_spatial := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) = 0)) (PreH2 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH3 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH4 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH5 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH6 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH7 : (UCOS2_state_inv sg hook_state )) (PreH8 : (0 <= (time_tick_time (hook_state)))) (PreH9 : (0 <= (time_tick_step (hook_state)))) (PreH10 : ((time_tick_step (hook_state)) < 256)) (PreH11 : (interrupt_saved_value 192 retval )) (PreH12 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH13 : (time_tick_entry sg invocation origin initial )) (PreH14 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH15 : (0 <= counter)) (PreH16 : (counter <= 65535)) (PreH17 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH18 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH19 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (0 <> (time_tick_step (hook_state)))) (PreH22 : (1 = (time_tick_step (hook_state)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  (time_tick_post platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
.

Definition OSTimeTick_return_wit_3 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) = 0)) (PreH2 : ((time_tick_process_byte (hook_state)) = (time_tick_process_byte (hook_state)))) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 <> (time_tick_step (hook_state)))) (PreH24 : (2 = (time_tick_step (hook_state)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  (time_tick_post platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) = 0)) (PreH2 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH3 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH4 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH5 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH6 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH7 : (UCOS2_state_inv sg hook_state )) (PreH8 : (0 <= (time_tick_time (hook_state)))) (PreH9 : (0 <= (time_tick_step (hook_state)))) (PreH10 : ((time_tick_step (hook_state)) < 256)) (PreH11 : (interrupt_saved_value 192 retval )) (PreH12 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH13 : (time_tick_entry sg invocation origin initial )) (PreH14 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH15 : (0 <= counter)) (PreH16 : (counter <= 65535)) (PreH17 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH18 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH19 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (0 <> (time_tick_step (hook_state)))) (PreH22 : (1 <> (time_tick_step (hook_state)))) (PreH23 : (2 = (time_tick_step (hook_state)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  (time_tick_post platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
).

Definition OSTimeTick_return_wit_3_split_goal_spatial := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) = 0)) (PreH2 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH3 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH4 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH5 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH6 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH7 : (UCOS2_state_inv sg hook_state )) (PreH8 : (0 <= (time_tick_time (hook_state)))) (PreH9 : (0 <= (time_tick_step (hook_state)))) (PreH10 : ((time_tick_step (hook_state)) < 256)) (PreH11 : (interrupt_saved_value 192 retval )) (PreH12 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH13 : (time_tick_entry sg invocation origin initial )) (PreH14 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH15 : (0 <= counter)) (PreH16 : (counter <= 65535)) (PreH17 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH18 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH19 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (0 <> (time_tick_step (hook_state)))) (PreH22 : (1 <> (time_tick_step (hook_state)))) (PreH23 : (2 = (time_tick_step (hook_state)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  (time_tick_post platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
.

Definition OSTimeTick_return_wit_4 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) = 0)) (PreH2 : ((time_tick_process_byte (hook_state)) = (time_tick_process_byte (hook_state)))) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 <> (time_tick_step (hook_state)))) (PreH24 : (2 <> (time_tick_step (hook_state)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  (time_tick_post platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) = 0)) (PreH2 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH3 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH4 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH5 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH6 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH7 : (UCOS2_state_inv sg hook_state )) (PreH8 : (0 <= (time_tick_time (hook_state)))) (PreH9 : (0 <= (time_tick_step (hook_state)))) (PreH10 : ((time_tick_step (hook_state)) < 256)) (PreH11 : (interrupt_saved_value 192 retval )) (PreH12 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH13 : (time_tick_entry sg invocation origin initial )) (PreH14 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH15 : (0 <= counter)) (PreH16 : (counter <= 65535)) (PreH17 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH18 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH19 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (0 <> (time_tick_step (hook_state)))) (PreH22 : (1 <> (time_tick_step (hook_state)))) (PreH23 : (2 <> (time_tick_step (hook_state)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  (time_tick_post platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
).

Definition OSTimeTick_return_wit_4_split_goal_spatial := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) = 0)) (PreH2 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH3 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH4 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH5 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH6 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH7 : (UCOS2_state_inv sg hook_state )) (PreH8 : (0 <= (time_tick_time (hook_state)))) (PreH9 : (0 <= (time_tick_step (hook_state)))) (PreH10 : ((time_tick_step (hook_state)) < 256)) (PreH11 : (interrupt_saved_value 192 retval )) (PreH12 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH13 : (time_tick_entry sg invocation origin initial )) (PreH14 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH15 : (0 <= counter)) (PreH16 : (counter <= 65535)) (PreH17 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH18 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH19 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (0 <> (time_tick_step (hook_state)))) (PreH22 : (1 <> (time_tick_step (hook_state)))) (PreH23 : (2 <> (time_tick_step (hook_state)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  (time_tick_post platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
.

Definition OSTimeTick_return_wit_5 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (PreH1 : ((time_tick_priority (node)) = 63)) (PreH2 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (time_tick_entry sg invocation origin initial )) (PreH4 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH5 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH6 : ((time_tick_process_byte (hook_state)) = 1)) (PreH7 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH8 : (UCOS2_state_inv sg current )) (PreH9 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
|--
  (time_tick_post platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (PreH1 : ((time_tick_priority (node)) = 63)) (PreH2 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (time_tick_entry sg invocation origin initial )) (PreH4 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH5 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH6 : ((time_tick_process_byte (hook_state)) = 1)) (PreH7 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH8 : (UCOS2_state_inv sg current )) (PreH9 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
|--
  (time_tick_post platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
).

Definition OSTimeTick_return_wit_5_split_goal_spatial := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (PreH1 : ((time_tick_priority (node)) = 63)) (PreH2 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (time_tick_entry sg invocation origin initial )) (PreH4 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH5 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH6 : ((time_tick_process_byte (hook_state)) = 1)) (PreH7 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH8 : (UCOS2_state_inv sg current )) (PreH9 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
|--
  (time_tick_post platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
.

Definition OSTimeTick_return_wit_6 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) <> 1)) (PreH2 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH3 : (UCOS2_state_inv sg hook_state )) (PreH4 : (0 <= (time_tick_time (hook_state)))) (PreH5 : (0 <= (time_tick_step (hook_state)))) (PreH6 : ((time_tick_step (hook_state)) < 256)) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH9 : (time_tick_entry sg invocation origin initial )) (PreH10 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH11 : (0 <= counter)) (PreH12 : (counter <= 65535)) (PreH13 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH14 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH15 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (time_tick_running (hook_state)))
  **  (time_tick_sched_without_running sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  (time_tick_post platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) <> 1)) (PreH2 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH3 : (UCOS2_state_inv sg hook_state )) (PreH4 : (0 <= (time_tick_time (hook_state)))) (PreH5 : (0 <= (time_tick_step (hook_state)))) (PreH6 : ((time_tick_step (hook_state)) < 256)) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH9 : (time_tick_entry sg invocation origin initial )) (PreH10 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH11 : (0 <= counter)) (PreH12 : (counter <= 65535)) (PreH13 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH14 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH15 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (time_tick_running (hook_state)))
  **  (time_tick_sched_without_running sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  (time_tick_post platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
).

Definition OSTimeTick_return_wit_6_split_goal_spatial := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) <> 1)) (PreH2 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH3 : (UCOS2_state_inv sg hook_state )) (PreH4 : (0 <= (time_tick_time (hook_state)))) (PreH5 : (0 <= (time_tick_step (hook_state)))) (PreH6 : ((time_tick_step (hook_state)) < 256)) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH9 : (time_tick_entry sg invocation origin initial )) (PreH10 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH11 : (0 <= counter)) (PreH12 : (counter <= 65535)) (PreH13 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH14 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH15 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (time_tick_running (hook_state)))
  **  (time_tick_sched_without_running sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  (time_tick_post platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
.

Definition OSTimeTick_partial_solve_wit_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH2 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH3 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_tick_pre platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
|--
  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (time_tick_pre platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
.

Definition OSTimeTick_partial_solve_wit_2_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (time_tick_entry sg invocation origin initial )) (PreH2 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH3 : (0 <= counter)) (PreH4 : (counter <= 65535)) (PreH5 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH6 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH7 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_tick_owned platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry app_value counter_address counter initial )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "step" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTimeTick_partial_solve_wit_2_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (time_tick_entry sg invocation origin initial )) (PreH2 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH3 : (0 <= counter)) (PreH4 : (counter <= 65535)) (PreH5 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH6 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH7 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_tick_owned platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry app_value counter_address counter initial )
|--
  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (time_tick_owned platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry app_value ( &( "OSTmrCtr" ) ) counter initial )
.

Definition OSTimeTick_partial_solve_wit_2 := OSTimeTick_partial_solve_wit_2_pure -> OSTimeTick_partial_solve_wit_2_aux.

Definition OSTimeTick_partial_solve_wit_3_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (time_tick_entry sg invocation origin initial )) (PreH2 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH3 : (0 <= counter)) (PreH4 : (counter <= 65535)) (PreH5 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH6 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH7 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_tick_hook_isr_post platform critical application sg invocation origin region_entry initial app_value ( &( "OSTmrCtr" ) ) counter )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "step" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (( &( "OSTmrCtr" ) ) = counter_address) ”
.

Definition OSTimeTick_partial_solve_wit_3_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (time_tick_entry sg invocation origin initial )) (PreH2 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH3 : (0 <= counter)) (PreH4 : (counter <= 65535)) (PreH5 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH6 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH7 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_tick_hook_isr_post platform critical application sg invocation origin region_entry initial app_value ( &( "OSTmrCtr" ) ) counter )
|--
  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (time_tick_hook_isr_post platform critical application sg invocation origin region_entry initial app_value ( &( "OSTmrCtr" ) ) counter )
.

Definition OSTimeTick_partial_solve_wit_3 := OSTimeTick_partial_solve_wit_3_pure -> OSTimeTick_partial_solve_wit_3_aux.

Definition OSTimeTick_partial_solve_wit_4 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH2 : (time_tick_entry sg invocation origin initial )) (PreH3 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH4 : (0 <= counter)) (PreH5 : (counter <= 65535)) (PreH6 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH7 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH8 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  (UCOS2_inv sg hook_state )
|--
  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  (UCOS2_inv sg hook_state )
.

Definition OSTimeTick_partial_solve_wit_5_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (interrupt_saved_value 192 retval )) (PreH2 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH3 : (time_tick_entry sg invocation origin initial )) (PreH4 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH5 : (0 <= counter)) (PreH6 : (counter <= 65535)) (PreH7 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH8 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH9 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  (UCOS2_inv sg hook_state )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTimeTick_partial_solve_wit_5_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (interrupt_saved_value 192 retval )) (PreH2 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH3 : (time_tick_entry sg invocation origin initial )) (PreH4 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH5 : (0 <= counter)) (PreH6 : (counter <= 65535)) (PreH7 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH8 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH9 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  (UCOS2_inv sg hook_state )
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (UCOS2_inv sg hook_state )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_5 := OSTimeTick_partial_solve_wit_5_pure -> OSTimeTick_partial_solve_wit_5_aux.

Definition OSTimeTick_partial_solve_wit_6_pure := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg hook_state )) (PreH2 : (0 <= (time_tick_time (hook_state)))) (PreH3 : (0 <= (time_tick_step (hook_state)))) (PreH4 : ((time_tick_step (hook_state)) < 256)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH7 : (time_tick_entry sg invocation origin initial )) (PreH8 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH9 : (0 <= counter)) (PreH10 : (counter <= 65535)) (PreH11 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH12 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH13 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSTime" ) )) # UInt  |-> (unsigned_last_nbits (((time_tick_time (hook_state)) + 1 )) (32)))
  **  (time_tick_without_time sg hook_state )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ ((time_tick_step (hook_state)) < 256) ” 
  &&  “ ((unsigned_last_nbits (((time_tick_time (hook_state)) + 1 )) (32)) = (((time_tick_time (hook_state)) + 1 ) % ( 4294967296 ) )) ”
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits (((time_tick_time (hook_state)) + 1 )) (32)) <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((unsigned_last_nbits (((time_tick_time (hook_state)) + 1 )) (32)) >= 0)) (PreH5 : (UCOS2_state_inv sg hook_state )) (PreH6 : (0 <= (time_tick_time (hook_state)))) (PreH7 : (0 <= (time_tick_step (hook_state)))) (PreH8 : ((time_tick_step (hook_state)) < 256)) (PreH9 : (interrupt_saved_value 192 retval )) (PreH10 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH11 : (time_tick_entry sg invocation origin initial )) (PreH12 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH13 : (0 <= counter)) (PreH14 : (counter <= 65535)) (PreH15 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH16 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH17 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSTime" ) )) # UInt  |-> (unsigned_last_nbits (((time_tick_time (hook_state)) + 1 )) (32)))
  **  (time_tick_without_time sg hook_state )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ ((unsigned_last_nbits (((time_tick_time (hook_state)) + 1 )) (32)) = (((time_tick_time (hook_state)) + 1 ) % ( 4294967296 ) )) ”
).

Definition OSTimeTick_partial_solve_wit_6_pure_split_goal_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits (((time_tick_time (hook_state)) + 1 )) (32)) <= UINT_MAX)) (PreH3 : (retval >= 0)) (PreH4 : ((unsigned_last_nbits (((time_tick_time (hook_state)) + 1 )) (32)) >= 0)) (PreH5 : (UCOS2_state_inv sg hook_state )) (PreH6 : (0 <= (time_tick_time (hook_state)))) (PreH7 : (0 <= (time_tick_step (hook_state)))) (PreH8 : ((time_tick_step (hook_state)) < 256)) (PreH9 : (interrupt_saved_value 192 retval )) (PreH10 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH11 : (time_tick_entry sg invocation origin initial )) (PreH12 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH13 : (0 <= counter)) (PreH14 : (counter <= 65535)) (PreH15 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH16 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH17 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSTime" ) )) # UInt  |-> (unsigned_last_nbits (((time_tick_time (hook_state)) + 1 )) (32)))
  **  (time_tick_without_time sg hook_state )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ ((unsigned_last_nbits (((time_tick_time (hook_state)) + 1 )) (32)) = (((time_tick_time (hook_state)) + 1 ) % ( 4294967296 ) )) ”
.

Definition OSTimeTick_partial_solve_wit_6_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg hook_state )) (PreH2 : (0 <= (time_tick_time (hook_state)))) (PreH3 : (0 <= (time_tick_step (hook_state)))) (PreH4 : ((time_tick_step (hook_state)) < 256)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH7 : (time_tick_entry sg invocation origin initial )) (PreH8 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH9 : (0 <= counter)) (PreH10 : (counter <= 65535)) (PreH11 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH12 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH13 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSTime" ) )) # UInt  |-> (unsigned_last_nbits (((time_tick_time (hook_state)) + 1 )) (32)))
  **  (time_tick_without_time sg hook_state )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ ((time_tick_step (hook_state)) < 256) ” 
  &&  “ ((unsigned_last_nbits (((time_tick_time (hook_state)) + 1 )) (32)) = (((time_tick_time (hook_state)) + 1 ) % ( 4294967296 ) )) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ ((time_tick_step (hook_state)) < 256) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "OSTime" ) )) # UInt  |-> (((time_tick_time (hook_state)) + 1 ) % ( 4294967296 ) ))
  **  (time_tick_without_time sg hook_state )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_6 := OSTimeTick_partial_solve_wit_6_pure -> OSTimeTick_partial_solve_wit_6_aux.

Definition OSTimeTick_partial_solve_wit_7_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg hook_state )) (PreH2 : (0 <= (time_tick_time (hook_state)))) (PreH3 : (0 <= (time_tick_step (hook_state)))) (PreH4 : ((time_tick_step (hook_state)) < 256)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH7 : (time_tick_entry sg invocation origin initial )) (PreH8 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH9 : (0 <= counter)) (PreH10 : (counter <= 65535)) (PreH11 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH12 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH13 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ”
.

Definition OSTimeTick_partial_solve_wit_7_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg hook_state )) (PreH2 : (0 <= (time_tick_time (hook_state)))) (PreH3 : (0 <= (time_tick_step (hook_state)))) (PreH4 : ((time_tick_step (hook_state)) < 256)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH7 : (time_tick_entry sg invocation origin initial )) (PreH8 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH9 : (0 <= counter)) (PreH10 : (counter <= 65535)) (PreH11 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH12 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH13 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ ((time_tick_step (hook_state)) < 256) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_7 := OSTimeTick_partial_solve_wit_7_pure -> OSTimeTick_partial_solve_wit_7_aux.

Definition OSTimeTick_partial_solve_wit_8_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg hook_state )) (PreH2 : (0 <= (time_tick_time (hook_state)))) (PreH3 : (0 <= (time_tick_step (hook_state)))) (PreH4 : ((time_tick_step (hook_state)) < 256)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH7 : (time_tick_entry sg invocation origin initial )) (PreH8 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH9 : (0 <= counter)) (PreH10 : (counter <= 65535)) (PreH11 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH12 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH13 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTimeTick_partial_solve_wit_8_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg hook_state )) (PreH2 : (0 <= (time_tick_time (hook_state)))) (PreH3 : (0 <= (time_tick_step (hook_state)))) (PreH4 : ((time_tick_step (hook_state)) < 256)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH7 : (time_tick_entry sg invocation origin initial )) (PreH8 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH9 : (0 <= counter)) (PreH10 : (counter <= 65535)) (PreH11 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH12 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH13 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ ((time_tick_step (hook_state)) < 256) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_8 := OSTimeTick_partial_solve_wit_8_pure -> OSTimeTick_partial_solve_wit_8_aux.

Definition OSTimeTick_partial_solve_wit_9_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH2 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH3 : (UCOS2_state_inv sg hook_state )) (PreH4 : (0 <= (time_tick_time (hook_state)))) (PreH5 : (0 <= (time_tick_step (hook_state)))) (PreH6 : ((time_tick_step (hook_state)) < 256)) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH9 : (time_tick_entry sg invocation origin initial )) (PreH10 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH11 : (0 <= counter)) (PreH12 : (counter <= 65535)) (PreH13 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH14 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH15 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (time_tick_running (hook_state)))
  **  (time_tick_sched_without_running sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ”
.

Definition OSTimeTick_partial_solve_wit_9_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH2 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH3 : (UCOS2_state_inv sg hook_state )) (PreH4 : (0 <= (time_tick_time (hook_state)))) (PreH5 : (0 <= (time_tick_step (hook_state)))) (PreH6 : ((time_tick_step (hook_state)) < 256)) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH9 : (time_tick_entry sg invocation origin initial )) (PreH10 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH11 : (0 <= counter)) (PreH12 : (counter <= 65535)) (PreH13 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH14 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH15 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (time_tick_running (hook_state)))
  **  (time_tick_sched_without_running sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ ((time_tick_step (hook_state)) < 256) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "OSRunning" ) )) # UChar  |-> (time_tick_running (hook_state)))
  **  (time_tick_sched_without_running sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_9 := OSTimeTick_partial_solve_wit_9_pure -> OSTimeTick_partial_solve_wit_9_aux.

Definition OSTimeTick_partial_solve_wit_10_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH2 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH3 : (UCOS2_state_inv sg hook_state )) (PreH4 : (0 <= (time_tick_time (hook_state)))) (PreH5 : (0 <= (time_tick_step (hook_state)))) (PreH6 : ((time_tick_step (hook_state)) < 256)) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH9 : (time_tick_entry sg invocation origin initial )) (PreH10 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH11 : (0 <= counter)) (PreH12 : (counter <= 65535)) (PreH13 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH14 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH15 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTimeTick_partial_solve_wit_10_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH2 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH3 : (UCOS2_state_inv sg hook_state )) (PreH4 : (0 <= (time_tick_time (hook_state)))) (PreH5 : (0 <= (time_tick_step (hook_state)))) (PreH6 : ((time_tick_step (hook_state)) < 256)) (PreH7 : (interrupt_saved_value 192 retval )) (PreH8 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH9 : (time_tick_entry sg invocation origin initial )) (PreH10 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH11 : (0 <= counter)) (PreH12 : (counter <= 65535)) (PreH13 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH14 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH15 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ ((time_tick_step (hook_state)) < 256) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_10 := OSTimeTick_partial_solve_wit_10_pure -> OSTimeTick_partial_solve_wit_10_aux.

Definition OSTimeTick_partial_solve_wit_11_pure := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH2 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH3 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH4 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH5 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH6 : (UCOS2_state_inv sg hook_state )) (PreH7 : (0 <= (time_tick_time (hook_state)))) (PreH8 : (0 <= (time_tick_step (hook_state)))) (PreH9 : ((time_tick_step (hook_state)) < 256)) (PreH10 : (interrupt_saved_value 192 retval )) (PreH11 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH12 : (time_tick_entry sg invocation origin initial )) (PreH13 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH14 : (0 <= counter)) (PreH15 : (counter <= 65535)) (PreH16 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH17 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH18 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (0 <> (time_tick_step (hook_state)))) (PreH21 : (1 <> (time_tick_step (hook_state)))) (PreH22 : (2 <> (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> 0)
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = (time_tick_process_byte (hook_state))) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ ((time_tick_running (hook_state)) = 1) ” 
  &&  “ (0 = (time_tick_step ((time_tick_clock_step_state (hook_state))))) ” 
  &&  “ (1 = (time_tick_process_byte (hook_state))) ” 
  &&  “ (1 = (time_tick_process_byte (hook_state))) ”
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 <> (time_tick_step (hook_state)))) (PreH24 : (2 <> (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> 0)
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (1 = (time_tick_process_byte (hook_state))) ” 
  &&  “ (1 = (time_tick_process_byte (hook_state))) ” 
  &&  “ (0 = (time_tick_step ((time_tick_clock_step_state (hook_state))))) ” 
  &&  “ ((time_tick_running (hook_state)) = 1) ”
).

Definition OSTimeTick_partial_solve_wit_11_pure_split_goal_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 <> (time_tick_step (hook_state)))) (PreH24 : (2 <> (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> 0)
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (1 = (time_tick_process_byte (hook_state))) ”
.

Definition OSTimeTick_partial_solve_wit_11_pure_split_goal_2 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 <> (time_tick_step (hook_state)))) (PreH24 : (2 <> (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> 0)
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (1 = (time_tick_process_byte (hook_state))) ”
.

Definition OSTimeTick_partial_solve_wit_11_pure_split_goal_3 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 <> (time_tick_step (hook_state)))) (PreH24 : (2 <> (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> 0)
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (0 = (time_tick_step ((time_tick_clock_step_state (hook_state))))) ”
.

Definition OSTimeTick_partial_solve_wit_11_pure_split_goal_4 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 <> (time_tick_step (hook_state)))) (PreH24 : (2 <> (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> 0)
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ ((time_tick_running (hook_state)) = 1) ”
.

Definition OSTimeTick_partial_solve_wit_11_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH2 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH3 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH4 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH5 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH6 : (UCOS2_state_inv sg hook_state )) (PreH7 : (0 <= (time_tick_time (hook_state)))) (PreH8 : (0 <= (time_tick_step (hook_state)))) (PreH9 : ((time_tick_step (hook_state)) < 256)) (PreH10 : (interrupt_saved_value 192 retval )) (PreH11 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH12 : (time_tick_entry sg invocation origin initial )) (PreH13 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH14 : (0 <= counter)) (PreH15 : (counter <= 65535)) (PreH16 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH17 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH18 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (0 <> (time_tick_step (hook_state)))) (PreH21 : (1 <> (time_tick_step (hook_state)))) (PreH22 : (2 <> (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> 0)
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "step" ) )) # UChar  |-> 1)
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = (time_tick_process_byte (hook_state))) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ ((time_tick_running (hook_state)) = 1) ” 
  &&  “ (0 = (time_tick_step ((time_tick_clock_step_state (hook_state))))) ” 
  &&  “ (1 = (time_tick_process_byte (hook_state))) ” 
  &&  “ (1 = (time_tick_process_byte (hook_state))) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ ((time_tick_step (hook_state)) < 256) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (time_tick_step (hook_state))) ” 
  &&  “ (1 <> (time_tick_step (hook_state))) ” 
  &&  “ (2 <> (time_tick_step (hook_state))) ”
  &&  ((( &( "step" ) )) # UChar  |-> (time_tick_process_byte (hook_state)))
  **  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step ((time_tick_clock_step_state (hook_state)))))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_11 := OSTimeTick_partial_solve_wit_11_pure -> OSTimeTick_partial_solve_wit_11_aux.

Definition OSTimeTick_partial_solve_wit_12_pure := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH2 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH3 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH4 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH5 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH6 : (UCOS2_state_inv sg hook_state )) (PreH7 : (0 <= (time_tick_time (hook_state)))) (PreH8 : (0 <= (time_tick_step (hook_state)))) (PreH9 : ((time_tick_step (hook_state)) < 256)) (PreH10 : (interrupt_saved_value 192 retval )) (PreH11 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH12 : (time_tick_entry sg invocation origin initial )) (PreH13 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH14 : (0 <= counter)) (PreH15 : (counter <= 65535)) (PreH16 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH17 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH18 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (0 <> (time_tick_step (hook_state)))) (PreH21 : (1 <> (time_tick_step (hook_state)))) (PreH22 : (2 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> 1)
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = (time_tick_process_byte (hook_state))) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ ((time_tick_running (hook_state)) = 1) ” 
  &&  “ (1 = (time_tick_step ((time_tick_clock_step_state (hook_state))))) ” 
  &&  “ (1 = (time_tick_process_byte (hook_state))) ” 
  &&  “ (1 = (time_tick_process_byte (hook_state))) ”
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 <> (time_tick_step (hook_state)))) (PreH24 : (2 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> 1)
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (1 = (time_tick_process_byte (hook_state))) ” 
  &&  “ (1 = (time_tick_process_byte (hook_state))) ” 
  &&  “ (1 = (time_tick_step ((time_tick_clock_step_state (hook_state))))) ” 
  &&  “ ((time_tick_running (hook_state)) = 1) ”
).

Definition OSTimeTick_partial_solve_wit_12_pure_split_goal_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 <> (time_tick_step (hook_state)))) (PreH24 : (2 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> 1)
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (1 = (time_tick_process_byte (hook_state))) ”
.

Definition OSTimeTick_partial_solve_wit_12_pure_split_goal_2 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 <> (time_tick_step (hook_state)))) (PreH24 : (2 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> 1)
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (1 = (time_tick_process_byte (hook_state))) ”
.

Definition OSTimeTick_partial_solve_wit_12_pure_split_goal_3 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 <> (time_tick_step (hook_state)))) (PreH24 : (2 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> 1)
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (1 = (time_tick_step ((time_tick_clock_step_state (hook_state))))) ”
.

Definition OSTimeTick_partial_solve_wit_12_pure_split_goal_4 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 <> (time_tick_step (hook_state)))) (PreH24 : (2 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> 1)
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ ((time_tick_running (hook_state)) = 1) ”
.

Definition OSTimeTick_partial_solve_wit_12_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH2 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH3 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH4 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH5 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH6 : (UCOS2_state_inv sg hook_state )) (PreH7 : (0 <= (time_tick_time (hook_state)))) (PreH8 : (0 <= (time_tick_step (hook_state)))) (PreH9 : ((time_tick_step (hook_state)) < 256)) (PreH10 : (interrupt_saved_value 192 retval )) (PreH11 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH12 : (time_tick_entry sg invocation origin initial )) (PreH13 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH14 : (0 <= counter)) (PreH15 : (counter <= 65535)) (PreH16 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH17 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH18 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (0 <> (time_tick_step (hook_state)))) (PreH21 : (1 <> (time_tick_step (hook_state)))) (PreH22 : (2 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> 1)
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "step" ) )) # UChar  |-> 1)
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = (time_tick_process_byte (hook_state))) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ ((time_tick_running (hook_state)) = 1) ” 
  &&  “ (1 = (time_tick_step ((time_tick_clock_step_state (hook_state))))) ” 
  &&  “ (1 = (time_tick_process_byte (hook_state))) ” 
  &&  “ (1 = (time_tick_process_byte (hook_state))) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ ((time_tick_step (hook_state)) < 256) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (time_tick_step (hook_state))) ” 
  &&  “ (1 <> (time_tick_step (hook_state))) ” 
  &&  “ (2 = (time_tick_step (hook_state))) ”
  &&  ((( &( "step" ) )) # UChar  |-> (time_tick_process_byte (hook_state)))
  **  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step ((time_tick_clock_step_state (hook_state)))))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_12 := OSTimeTick_partial_solve_wit_12_pure -> OSTimeTick_partial_solve_wit_12_aux.

Definition OSTimeTick_partial_solve_wit_13_pure := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH2 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH3 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH4 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH5 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH6 : (UCOS2_state_inv sg hook_state )) (PreH7 : (0 <= (time_tick_time (hook_state)))) (PreH8 : (0 <= (time_tick_step (hook_state)))) (PreH9 : ((time_tick_step (hook_state)) < 256)) (PreH10 : (interrupt_saved_value 192 retval )) (PreH11 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH12 : (time_tick_entry sg invocation origin initial )) (PreH13 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH14 : (0 <= counter)) (PreH15 : (counter <= 65535)) (PreH16 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH17 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH18 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (0 <> (time_tick_step (hook_state)))) (PreH21 : (1 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step (hook_state)))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = (time_tick_process_byte (hook_state))) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ ((time_tick_running (hook_state)) = 1) ” 
  &&  “ (1 = (time_tick_step ((time_tick_clock_step_state (hook_state))))) ” 
  &&  “ (0 = (time_tick_process_byte (hook_state))) ” 
  &&  “ (0 = (time_tick_process_byte (hook_state))) ”
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step (hook_state)))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (0 = (time_tick_process_byte (hook_state))) ” 
  &&  “ (0 = (time_tick_process_byte (hook_state))) ” 
  &&  “ (1 = (time_tick_step ((time_tick_clock_step_state (hook_state))))) ” 
  &&  “ ((time_tick_running (hook_state)) = 1) ”
).

Definition OSTimeTick_partial_solve_wit_13_pure_split_goal_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step (hook_state)))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (0 = (time_tick_process_byte (hook_state))) ”
.

Definition OSTimeTick_partial_solve_wit_13_pure_split_goal_2 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step (hook_state)))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (0 = (time_tick_process_byte (hook_state))) ”
.

Definition OSTimeTick_partial_solve_wit_13_pure_split_goal_3 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step (hook_state)))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (1 = (time_tick_step ((time_tick_clock_step_state (hook_state))))) ”
.

Definition OSTimeTick_partial_solve_wit_13_pure_split_goal_4 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step (hook_state)))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 0)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ ((time_tick_running (hook_state)) = 1) ”
.

Definition OSTimeTick_partial_solve_wit_13_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH2 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH3 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH4 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH5 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH6 : (UCOS2_state_inv sg hook_state )) (PreH7 : (0 <= (time_tick_time (hook_state)))) (PreH8 : (0 <= (time_tick_step (hook_state)))) (PreH9 : ((time_tick_step (hook_state)) < 256)) (PreH10 : (interrupt_saved_value 192 retval )) (PreH11 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH12 : (time_tick_entry sg invocation origin initial )) (PreH13 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH14 : (0 <= counter)) (PreH15 : (counter <= 65535)) (PreH16 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH17 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH18 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (0 <> (time_tick_step (hook_state)))) (PreH21 : (1 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step (hook_state)))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "step" ) )) # UChar  |-> 0)
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = (time_tick_process_byte (hook_state))) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ ((time_tick_running (hook_state)) = 1) ” 
  &&  “ (1 = (time_tick_step ((time_tick_clock_step_state (hook_state))))) ” 
  &&  “ (0 = (time_tick_process_byte (hook_state))) ” 
  &&  “ (0 = (time_tick_process_byte (hook_state))) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ ((time_tick_step (hook_state)) < 256) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (time_tick_step (hook_state))) ” 
  &&  “ (1 = (time_tick_step (hook_state))) ”
  &&  ((( &( "step" ) )) # UChar  |-> (time_tick_process_byte (hook_state)))
  **  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step ((time_tick_clock_step_state (hook_state)))))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_13 := OSTimeTick_partial_solve_wit_13_pure -> OSTimeTick_partial_solve_wit_13_aux.

Definition OSTimeTick_partial_solve_wit_14_pure := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH2 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH3 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH4 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH5 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH6 : (UCOS2_state_inv sg hook_state )) (PreH7 : (0 <= (time_tick_time (hook_state)))) (PreH8 : (0 <= (time_tick_step (hook_state)))) (PreH9 : ((time_tick_step (hook_state)) < 256)) (PreH10 : (interrupt_saved_value 192 retval )) (PreH11 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH12 : (time_tick_entry sg invocation origin initial )) (PreH13 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH14 : (0 <= counter)) (PreH15 : (counter <= 65535)) (PreH16 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH17 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH18 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (0 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step (hook_state)))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = (time_tick_process_byte (hook_state))) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ ((time_tick_running (hook_state)) = 1) ” 
  &&  “ (0 = (time_tick_step ((time_tick_clock_step_state (hook_state))))) ” 
  &&  “ (1 = (time_tick_process_byte (hook_state))) ” 
  &&  “ (1 = (time_tick_process_byte (hook_state))) ”
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step (hook_state)))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (1 = (time_tick_process_byte (hook_state))) ” 
  &&  “ (1 = (time_tick_process_byte (hook_state))) ” 
  &&  “ (0 = (time_tick_step ((time_tick_clock_step_state (hook_state))))) ” 
  &&  “ ((time_tick_running (hook_state)) = 1) ”
).

Definition OSTimeTick_partial_solve_wit_14_pure_split_goal_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step (hook_state)))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (1 = (time_tick_process_byte (hook_state))) ”
.

Definition OSTimeTick_partial_solve_wit_14_pure_split_goal_2 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step (hook_state)))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (1 = (time_tick_process_byte (hook_state))) ”
.

Definition OSTimeTick_partial_solve_wit_14_pure_split_goal_3 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step (hook_state)))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (0 = (time_tick_step ((time_tick_clock_step_state (hook_state))))) ”
.

Definition OSTimeTick_partial_solve_wit_14_pure_split_goal_4 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step (hook_state)))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ ((time_tick_running (hook_state)) = 1) ”
.

Definition OSTimeTick_partial_solve_wit_14_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH2 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH3 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH4 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH5 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH6 : (UCOS2_state_inv sg hook_state )) (PreH7 : (0 <= (time_tick_time (hook_state)))) (PreH8 : (0 <= (time_tick_step (hook_state)))) (PreH9 : ((time_tick_step (hook_state)) < 256)) (PreH10 : (interrupt_saved_value 192 retval )) (PreH11 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH12 : (time_tick_entry sg invocation origin initial )) (PreH13 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH14 : (0 <= counter)) (PreH15 : (counter <= 65535)) (PreH16 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH17 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH18 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (0 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step (hook_state)))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "step" ) )) # UChar  |-> 1)
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = (time_tick_process_byte (hook_state))) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ ((time_tick_running (hook_state)) = 1) ” 
  &&  “ (0 = (time_tick_step ((time_tick_clock_step_state (hook_state))))) ” 
  &&  “ (1 = (time_tick_process_byte (hook_state))) ” 
  &&  “ (1 = (time_tick_process_byte (hook_state))) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ ((time_tick_step (hook_state)) < 256) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 = (time_tick_step (hook_state))) ”
  &&  ((( &( "step" ) )) # UChar  |-> (time_tick_process_byte (hook_state)))
  **  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step ((time_tick_clock_step_state (hook_state)))))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_14 := OSTimeTick_partial_solve_wit_14_pure -> OSTimeTick_partial_solve_wit_14_aux.

Definition OSTimeTick_partial_solve_wit_15_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0)) (PreH2 : ((time_tick_process_byte (hook_state)) = (time_tick_process_byte (hook_state)))) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 <> (time_tick_step (hook_state)))) (PreH24 : (2 <> (time_tick_step (hook_state)))) ,
  ((( &( "step" ) )) # UChar  |-> (time_tick_process_byte (hook_state)))
  **  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTimeTick_partial_solve_wit_15_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0)) (PreH2 : ((time_tick_process_byte (hook_state)) = (time_tick_process_byte (hook_state)))) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 <> (time_tick_step (hook_state)))) (PreH24 : (2 <> (time_tick_step (hook_state)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ ((time_tick_step (hook_state)) < 256) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (time_tick_step (hook_state))) ” 
  &&  “ (1 <> (time_tick_step (hook_state))) ” 
  &&  “ (2 <> (time_tick_step (hook_state))) ”
  &&  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_15 := OSTimeTick_partial_solve_wit_15_pure -> OSTimeTick_partial_solve_wit_15_aux.

Definition OSTimeTick_partial_solve_wit_16_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0)) (PreH2 : ((time_tick_process_byte (hook_state)) = (time_tick_process_byte (hook_state)))) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 <> (time_tick_step (hook_state)))) (PreH24 : (2 = (time_tick_step (hook_state)))) ,
  ((( &( "step" ) )) # UChar  |-> (time_tick_process_byte (hook_state)))
  **  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTimeTick_partial_solve_wit_16_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0)) (PreH2 : ((time_tick_process_byte (hook_state)) = (time_tick_process_byte (hook_state)))) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 <> (time_tick_step (hook_state)))) (PreH24 : (2 = (time_tick_step (hook_state)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ ((time_tick_step (hook_state)) < 256) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (time_tick_step (hook_state))) ” 
  &&  “ (1 <> (time_tick_step (hook_state))) ” 
  &&  “ (2 = (time_tick_step (hook_state))) ”
  &&  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_16 := OSTimeTick_partial_solve_wit_16_pure -> OSTimeTick_partial_solve_wit_16_aux.

Definition OSTimeTick_partial_solve_wit_17_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0)) (PreH2 : ((time_tick_process_byte (hook_state)) = (time_tick_process_byte (hook_state)))) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 = (time_tick_step (hook_state)))) ,
  ((( &( "step" ) )) # UChar  |-> (time_tick_process_byte (hook_state)))
  **  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTimeTick_partial_solve_wit_17_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0)) (PreH2 : ((time_tick_process_byte (hook_state)) = (time_tick_process_byte (hook_state)))) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 = (time_tick_step (hook_state)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ ((time_tick_step (hook_state)) < 256) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (time_tick_step (hook_state))) ” 
  &&  “ (1 = (time_tick_step (hook_state))) ”
  &&  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_17 := OSTimeTick_partial_solve_wit_17_pure -> OSTimeTick_partial_solve_wit_17_aux.

Definition OSTimeTick_partial_solve_wit_18_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0)) (PreH2 : ((time_tick_process_byte (hook_state)) = (time_tick_process_byte (hook_state)))) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 = (time_tick_step (hook_state)))) ,
  ((( &( "step" ) )) # UChar  |-> (time_tick_process_byte (hook_state)))
  **  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTimeTick_partial_solve_wit_18_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0)) (PreH2 : ((time_tick_process_byte (hook_state)) = (time_tick_process_byte (hook_state)))) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 = (time_tick_step (hook_state)))) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ ((time_tick_step (hook_state)) < 256) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 = (time_tick_step (hook_state))) ”
  &&  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_18 := OSTimeTick_partial_solve_wit_18_pure -> OSTimeTick_partial_solve_wit_18_aux.

Definition OSTimeTick_partial_solve_wit_19_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) )) (PreH2 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 <> (time_tick_step (hook_state)))) (PreH24 : (2 <> (time_tick_step (hook_state)))) ,
  ((( &( "OSTCBList" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
  **  (time_tick_task_without_head sg (time_tick_clock_step_state (hook_state)) )
  **  ((( &( "step" ) )) # UChar  |-> (time_tick_process_byte (hook_state)))
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) ) ”
.

Definition OSTimeTick_partial_solve_wit_19_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) )) (PreH2 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 <> (time_tick_step (hook_state)))) (PreH24 : (2 <> (time_tick_step (hook_state)))) ,
  ((( &( "OSTCBList" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
  **  (time_tick_task_without_head sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) ) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) ) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ ((time_tick_step (hook_state)) < 256) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (time_tick_step (hook_state))) ” 
  &&  “ (1 <> (time_tick_step (hook_state))) ” 
  &&  “ (2 <> (time_tick_step (hook_state))) ”
  &&  ((( &( "OSTCBList" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
  **  (time_tick_task_without_head sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_19 := OSTimeTick_partial_solve_wit_19_pure -> OSTimeTick_partial_solve_wit_19_aux.

Definition OSTimeTick_partial_solve_wit_20_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) )) (PreH2 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 <> (time_tick_step (hook_state)))) (PreH24 : (2 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTCBList" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
  **  (time_tick_task_without_head sg (time_tick_clock_step_state (hook_state)) )
  **  ((( &( "step" ) )) # UChar  |-> (time_tick_process_byte (hook_state)))
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) ) ”
.

Definition OSTimeTick_partial_solve_wit_20_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) )) (PreH2 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 <> (time_tick_step (hook_state)))) (PreH24 : (2 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTCBList" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
  **  (time_tick_task_without_head sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) ) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) ) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ ((time_tick_step (hook_state)) < 256) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (time_tick_step (hook_state))) ” 
  &&  “ (1 <> (time_tick_step (hook_state))) ” 
  &&  “ (2 = (time_tick_step (hook_state))) ”
  &&  ((( &( "OSTCBList" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
  **  (time_tick_task_without_head sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_20 := OSTimeTick_partial_solve_wit_20_pure -> OSTimeTick_partial_solve_wit_20_aux.

Definition OSTimeTick_partial_solve_wit_21_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) )) (PreH2 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTCBList" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
  **  (time_tick_task_without_head sg (time_tick_clock_step_state (hook_state)) )
  **  ((( &( "step" ) )) # UChar  |-> (time_tick_process_byte (hook_state)))
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) ) ”
.

Definition OSTimeTick_partial_solve_wit_21_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) )) (PreH2 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 <> (time_tick_step (hook_state)))) (PreH23 : (1 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTCBList" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
  **  (time_tick_task_without_head sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) ) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) ) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ ((time_tick_step (hook_state)) < 256) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 <> (time_tick_step (hook_state))) ” 
  &&  “ (1 = (time_tick_step (hook_state))) ”
  &&  ((( &( "OSTCBList" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
  **  (time_tick_task_without_head sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_21 := OSTimeTick_partial_solve_wit_21_pure -> OSTimeTick_partial_solve_wit_21_aux.

Definition OSTimeTick_partial_solve_wit_22_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) )) (PreH2 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTCBList" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
  **  (time_tick_task_without_head sg (time_tick_clock_step_state (hook_state)) )
  **  ((( &( "step" ) )) # UChar  |-> (time_tick_process_byte (hook_state)))
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) ) ”
.

Definition OSTimeTick_partial_solve_wit_22_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) )) (PreH2 : ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0)) (PreH3 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH4 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH5 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) (PreH6 : ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1)) (PreH7 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH8 : (UCOS2_state_inv sg hook_state )) (PreH9 : (0 <= (time_tick_time (hook_state)))) (PreH10 : (0 <= (time_tick_step (hook_state)))) (PreH11 : ((time_tick_step (hook_state)) < 256)) (PreH12 : (interrupt_saved_value 192 retval )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (0 <= counter)) (PreH17 : (counter <= 65535)) (PreH18 : (( &( "OSTmrCtr" ) ) = counter_address)) (PreH19 : (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg)))) (PreH20 : (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH21 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (0 = (time_tick_step (hook_state)))) ,
  ((( &( "OSTCBList" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
  **  (time_tick_task_without_head sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) ) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) ) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_process_byte (hook_state))) (32)) <> 0) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ ((unsigned_last_nbits ((time_tick_running (hook_state))) (32)) = 1) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ ((time_tick_step (hook_state)) < 256) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ” 
  &&  “ (( &( "OSTmrCtr" ) ) = counter_address) ” 
  &&  “ (( &( "OSTmrSemSignal" ) ) = (g_OSTmrSemSignal (sg))) ” 
  &&  “ (time_tick_internal_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (0 = (time_tick_step (hook_state))) ”
  &&  ((( &( "OSTCBList" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
  **  (time_tick_task_without_head sg (time_tick_clock_step_state (hook_state)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_22 := OSTimeTick_partial_solve_wit_22_pure -> OSTimeTick_partial_solve_wit_22_aux.

Definition OSTimeTick_partial_solve_wit_23_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (cpu_word: Z) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (PreH1 : ((time_tick_priority (node)) <> 63)) (PreH2 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (time_tick_entry sg invocation origin initial )) (PreH4 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH5 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH6 : ((time_tick_process_byte (hook_state)) = 1)) (PreH7 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH8 : (UCOS2_state_inv sg current )) (PreH9 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_word)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_tick_lookup current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ”
.

Definition OSTimeTick_partial_solve_wit_23_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (PreH1 : ((time_tick_priority (node)) <> 63)) (PreH2 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (time_tick_entry sg invocation origin initial )) (PreH4 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH5 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH6 : ((time_tick_process_byte (hook_state)) = 1)) (PreH7 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH8 : (UCOS2_state_inv sg current )) (PreH9 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
|--
  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((task_slot_addr (sg) (tid)) = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_tick_lookup current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ ((time_tick_priority (node)) <> 63) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_23 := OSTimeTick_partial_solve_wit_23_pure -> OSTimeTick_partial_solve_wit_23_aux.

Definition OSTimeTick_partial_solve_wit_24 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (PreH1 : (UCOS2_state_inv sg current )) (PreH2 : (time_tick_lookup current tid node )) (PreH3 : (0 <= (time_tick_y (node)))) (PreH4 : ((time_tick_y (node)) < 8)) (PreH5 : (0 <= (time_tick_delay (node)))) (PreH6 : ((time_tick_delay (node)) < 4294967296)) (PreH7 : ((time_tick_priority (node)) <> 63)) (PreH8 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (time_tick_entry sg invocation origin initial )) (PreH10 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH11 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH12 : ((time_tick_process_byte (hook_state)) = 1)) (PreH13 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH14 : (UCOS2_state_inv sg current )) (PreH15 : (time_tick_lookup current tid node )) ,
  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (time_tick_delay (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (time_tick_pend_result (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ” 
  &&  “ (0 <= (time_tick_y (node))) ” 
  &&  “ ((time_tick_y (node)) < 8) ” 
  &&  “ (0 <= (time_tick_delay (node))) ” 
  &&  “ ((time_tick_delay (node)) < 4294967296) ” 
  &&  “ ((time_tick_priority (node)) <> 63) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (time_tick_delay (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (time_tick_pend_result (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_25 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))) 8) = 0)) (PreH2 : ((Z.land (time_tick_status (node)) 55) <> 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0)) (PreH4 : ((time_tick_delay (node)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current )) (PreH7 : (time_tick_lookup current tid node )) (PreH8 : (0 <= (time_tick_y (node)))) (PreH9 : ((time_tick_y (node)) < 8)) (PreH10 : (0 <= (time_tick_delay (node)))) (PreH11 : ((time_tick_delay (node)) < 4294967296)) (PreH12 : ((time_tick_priority (node)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH17 : ((time_tick_process_byte (hook_state)) = 1)) (PreH18 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH19 : (UCOS2_state_inv sg current )) (PreH20 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 1)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((time_tick_ready_group (current))) (8)) (unsigned_last_nbits ((time_tick_bit_y (node))) (8))))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ ((Z.land (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))) 8) = 0) ” 
  &&  “ ((Z.land (time_tick_status (node)) 55) <> 0) ” 
  &&  “ ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0) ” 
  &&  “ ((time_tick_delay (node)) <> 0) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ” 
  &&  “ (0 <= (time_tick_y (node))) ” 
  &&  “ ((time_tick_y (node)) < 8) ” 
  &&  “ (0 <= (time_tick_delay (node))) ” 
  &&  “ ((time_tick_delay (node)) < 4294967296) ” 
  &&  “ ((time_tick_priority (node)) <> 63) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((time_tick_y (node)) * sizeof(UCHAR)))) # UChar  |-> (Znth (time_tick_y (node)) (time_tick_ready_rows (current)) 0))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (time_tick_y (node)) 0 8 (time_tick_ready_rows (current)) )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 1)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((time_tick_ready_group (current))) (8)) (unsigned_last_nbits ((time_tick_bit_y (node))) (8))))
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_26 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))) 8) = 0)) (PreH2 : ((Z.land (time_tick_status (node)) 55) <> 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0)) (PreH4 : ((time_tick_delay (node)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current )) (PreH7 : (time_tick_lookup current tid node )) (PreH8 : (0 <= (time_tick_y (node)))) (PreH9 : ((time_tick_y (node)) < 8)) (PreH10 : (0 <= (time_tick_delay (node)))) (PreH11 : ((time_tick_delay (node)) < 4294967296)) (PreH12 : ((time_tick_priority (node)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH17 : ((time_tick_process_byte (hook_state)) = 1)) (PreH18 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH19 : (UCOS2_state_inv sg current )) (PreH20 : (time_tick_lookup current tid node )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 1)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((time_tick_ready_group (current))) (8)) (unsigned_last_nbits ((time_tick_bit_y (node))) (8))))
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ ((Z.land (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))) 8) = 0) ” 
  &&  “ ((Z.land (time_tick_status (node)) 55) <> 0) ” 
  &&  “ ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0) ” 
  &&  “ ((time_tick_delay (node)) <> 0) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ” 
  &&  “ (0 <= (time_tick_y (node))) ” 
  &&  “ ((time_tick_y (node)) < 8) ” 
  &&  “ (0 <= (time_tick_delay (node))) ” 
  &&  “ ((time_tick_delay (node)) < 4294967296) ” 
  &&  “ ((time_tick_priority (node)) <> 63) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((time_tick_y (node)) * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (time_tick_y (node)) 0 8 (time_tick_ready_rows (current)) )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 1)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((time_tick_ready_group (current))) (8)) (unsigned_last_nbits ((time_tick_bit_y (node))) (8))))
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_27 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (time_tick_status (node)) 8) = 0)) (PreH2 : ((Z.land (time_tick_status (node)) 55) = 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0)) (PreH4 : ((time_tick_delay (node)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current )) (PreH7 : (time_tick_lookup current tid node )) (PreH8 : (0 <= (time_tick_y (node)))) (PreH9 : ((time_tick_y (node)) < 8)) (PreH10 : (0 <= (time_tick_delay (node)))) (PreH11 : ((time_tick_delay (node)) < 4294967296)) (PreH12 : ((time_tick_priority (node)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH17 : ((time_tick_process_byte (hook_state)) = 1)) (PreH18 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH19 : (UCOS2_state_inv sg current )) (PreH20 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((time_tick_ready_group (current))) (8)) (unsigned_last_nbits ((time_tick_bit_y (node))) (8))))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ ((Z.land (time_tick_status (node)) 8) = 0) ” 
  &&  “ ((Z.land (time_tick_status (node)) 55) = 0) ” 
  &&  “ ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0) ” 
  &&  “ ((time_tick_delay (node)) <> 0) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ” 
  &&  “ (0 <= (time_tick_y (node))) ” 
  &&  “ ((time_tick_y (node)) < 8) ” 
  &&  “ (0 <= (time_tick_delay (node))) ” 
  &&  “ ((time_tick_delay (node)) < 4294967296) ” 
  &&  “ ((time_tick_priority (node)) <> 63) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((time_tick_y (node)) * sizeof(UCHAR)))) # UChar  |-> (Znth (time_tick_y (node)) (time_tick_ready_rows (current)) 0))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (time_tick_y (node)) 0 8 (time_tick_ready_rows (current)) )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((time_tick_ready_group (current))) (8)) (unsigned_last_nbits ((time_tick_bit_y (node))) (8))))
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_28 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (time_tick_status (node)) 8) = 0)) (PreH2 : ((Z.land (time_tick_status (node)) 55) = 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0)) (PreH4 : ((time_tick_delay (node)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current )) (PreH7 : (time_tick_lookup current tid node )) (PreH8 : (0 <= (time_tick_y (node)))) (PreH9 : ((time_tick_y (node)) < 8)) (PreH10 : (0 <= (time_tick_delay (node)))) (PreH11 : ((time_tick_delay (node)) < 4294967296)) (PreH12 : ((time_tick_priority (node)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH17 : ((time_tick_process_byte (hook_state)) = 1)) (PreH18 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH19 : (UCOS2_state_inv sg current )) (PreH20 : (time_tick_lookup current tid node )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((time_tick_ready_group (current))) (8)) (unsigned_last_nbits ((time_tick_bit_y (node))) (8))))
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ ((Z.land (time_tick_status (node)) 8) = 0) ” 
  &&  “ ((Z.land (time_tick_status (node)) 55) = 0) ” 
  &&  “ ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0) ” 
  &&  “ ((time_tick_delay (node)) <> 0) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ” 
  &&  “ (0 <= (time_tick_y (node))) ” 
  &&  “ ((time_tick_y (node)) < 8) ” 
  &&  “ (0 <= (time_tick_delay (node))) ” 
  &&  “ ((time_tick_delay (node)) < 4294967296) ” 
  &&  “ ((time_tick_priority (node)) <> 63) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((time_tick_y (node)) * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (time_tick_y (node)) 0 8 (time_tick_ready_rows (current)) )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((time_tick_ready_group (current))) (8)) (unsigned_last_nbits ((time_tick_bit_y (node))) (8))))
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_29_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))) 8) = 0)) (PreH2 : ((Z.land (time_tick_status (node)) 55) <> 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0)) (PreH4 : ((time_tick_delay (node)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current )) (PreH7 : (time_tick_lookup current tid node )) (PreH8 : (0 <= (time_tick_y (node)))) (PreH9 : ((time_tick_y (node)) < 8)) (PreH10 : (0 <= (time_tick_delay (node)))) (PreH11 : ((time_tick_delay (node)) < 4294967296)) (PreH12 : ((time_tick_priority (node)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH17 : ((time_tick_process_byte (hook_state)) = 1)) (PreH18 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH19 : (UCOS2_state_inv sg current )) (PreH20 : (time_tick_lookup current tid node )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((time_tick_y (node))) ((Z.lor (unsigned_last_nbits ((Znth (time_tick_y (node)) (time_tick_ready_rows (current)) 0)) (8)) (unsigned_last_nbits ((time_tick_bit_x (node))) (8)))) ((time_tick_ready_rows (current)))) )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 1)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((time_tick_ready_group (current))) (8)) (unsigned_last_nbits ((time_tick_bit_y (node))) (8))))
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ”
.

Definition OSTimeTick_partial_solve_wit_29_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))) 8) = 0)) (PreH2 : ((Z.land (time_tick_status (node)) 55) <> 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0)) (PreH4 : ((time_tick_delay (node)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current )) (PreH7 : (time_tick_lookup current tid node )) (PreH8 : (0 <= (time_tick_y (node)))) (PreH9 : ((time_tick_y (node)) < 8)) (PreH10 : (0 <= (time_tick_delay (node)))) (PreH11 : ((time_tick_delay (node)) < 4294967296)) (PreH12 : ((time_tick_priority (node)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH17 : ((time_tick_process_byte (hook_state)) = 1)) (PreH18 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH19 : (UCOS2_state_inv sg current )) (PreH20 : (time_tick_lookup current tid node )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((time_tick_y (node))) ((Z.lor (unsigned_last_nbits ((Znth (time_tick_y (node)) (time_tick_ready_rows (current)) 0)) (8)) (unsigned_last_nbits ((time_tick_bit_x (node))) (8)))) ((time_tick_ready_rows (current)))) )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 1)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((time_tick_ready_group (current))) (8)) (unsigned_last_nbits ((time_tick_bit_y (node))) (8))))
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ ((Z.land (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))) 8) = 0) ” 
  &&  “ ((Z.land (time_tick_status (node)) 55) <> 0) ” 
  &&  “ ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0) ” 
  &&  “ ((time_tick_delay (node)) <> 0) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ” 
  &&  “ (0 <= (time_tick_y (node))) ” 
  &&  “ ((time_tick_y (node)) < 8) ” 
  &&  “ (0 <= (time_tick_delay (node))) ” 
  &&  “ ((time_tick_delay (node)) < 4294967296) ” 
  &&  “ ((time_tick_priority (node)) <> 63) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((time_tick_y (node))) ((Z.lor (unsigned_last_nbits ((Znth (time_tick_y (node)) (time_tick_ready_rows (current)) 0)) (8)) (unsigned_last_nbits ((time_tick_bit_x (node))) (8)))) ((time_tick_ready_rows (current)))) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 1)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((time_tick_ready_group (current))) (8)) (unsigned_last_nbits ((time_tick_bit_y (node))) (8))))
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_29 := OSTimeTick_partial_solve_wit_29_pure -> OSTimeTick_partial_solve_wit_29_aux.

Definition OSTimeTick_partial_solve_wit_30_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (time_tick_status (node)) 8) = 0)) (PreH2 : ((Z.land (time_tick_status (node)) 55) = 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0)) (PreH4 : ((time_tick_delay (node)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current )) (PreH7 : (time_tick_lookup current tid node )) (PreH8 : (0 <= (time_tick_y (node)))) (PreH9 : ((time_tick_y (node)) < 8)) (PreH10 : (0 <= (time_tick_delay (node)))) (PreH11 : ((time_tick_delay (node)) < 4294967296)) (PreH12 : ((time_tick_priority (node)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH17 : ((time_tick_process_byte (hook_state)) = 1)) (PreH18 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH19 : (UCOS2_state_inv sg current )) (PreH20 : (time_tick_lookup current tid node )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((time_tick_y (node))) ((Z.lor (unsigned_last_nbits ((Znth (time_tick_y (node)) (time_tick_ready_rows (current)) 0)) (8)) (unsigned_last_nbits ((time_tick_bit_x (node))) (8)))) ((time_tick_ready_rows (current)))) )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((time_tick_ready_group (current))) (8)) (unsigned_last_nbits ((time_tick_bit_y (node))) (8))))
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ”
.

Definition OSTimeTick_partial_solve_wit_30_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (time_tick_status (node)) 8) = 0)) (PreH2 : ((Z.land (time_tick_status (node)) 55) = 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0)) (PreH4 : ((time_tick_delay (node)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current )) (PreH7 : (time_tick_lookup current tid node )) (PreH8 : (0 <= (time_tick_y (node)))) (PreH9 : ((time_tick_y (node)) < 8)) (PreH10 : (0 <= (time_tick_delay (node)))) (PreH11 : ((time_tick_delay (node)) < 4294967296)) (PreH12 : ((time_tick_priority (node)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH17 : ((time_tick_process_byte (hook_state)) = 1)) (PreH18 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH19 : (UCOS2_state_inv sg current )) (PreH20 : (time_tick_lookup current tid node )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((time_tick_y (node))) ((Z.lor (unsigned_last_nbits ((Znth (time_tick_y (node)) (time_tick_ready_rows (current)) 0)) (8)) (unsigned_last_nbits ((time_tick_bit_x (node))) (8)))) ((time_tick_ready_rows (current)))) )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((time_tick_ready_group (current))) (8)) (unsigned_last_nbits ((time_tick_bit_y (node))) (8))))
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ ((Z.land (time_tick_status (node)) 8) = 0) ” 
  &&  “ ((Z.land (time_tick_status (node)) 55) = 0) ” 
  &&  “ ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0) ” 
  &&  “ ((time_tick_delay (node)) <> 0) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ” 
  &&  “ (0 <= (time_tick_y (node))) ” 
  &&  “ ((time_tick_y (node)) < 8) ” 
  &&  “ (0 <= (time_tick_delay (node))) ” 
  &&  “ ((time_tick_delay (node)) < 4294967296) ” 
  &&  “ ((time_tick_priority (node)) <> 63) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((time_tick_y (node))) ((Z.lor (unsigned_last_nbits ((Znth (time_tick_y (node)) (time_tick_ready_rows (current)) 0)) (8)) (unsigned_last_nbits ((time_tick_bit_x (node))) (8)))) ((time_tick_ready_rows (current)))) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((time_tick_ready_group (current))) (8)) (unsigned_last_nbits ((time_tick_bit_y (node))) (8))))
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_30 := OSTimeTick_partial_solve_wit_30_pure -> OSTimeTick_partial_solve_wit_30_aux.

Definition OSTimeTick_partial_solve_wit_31_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (time_tick_status (node)) 8) <> 0)) (PreH2 : ((Z.land (time_tick_status (node)) 55) = 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0)) (PreH4 : ((time_tick_delay (node)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current )) (PreH7 : (time_tick_lookup current tid node )) (PreH8 : (0 <= (time_tick_y (node)))) (PreH9 : ((time_tick_y (node)) < 8)) (PreH10 : (0 <= (time_tick_delay (node)))) (PreH11 : ((time_tick_delay (node)) < 4294967296)) (PreH12 : ((time_tick_priority (node)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH17 : ((time_tick_process_byte (hook_state)) = 1)) (PreH18 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH19 : (UCOS2_state_inv sg current )) (PreH20 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ”
.

Definition OSTimeTick_partial_solve_wit_31_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (time_tick_status (node)) 8) <> 0)) (PreH2 : ((Z.land (time_tick_status (node)) 55) = 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0)) (PreH4 : ((time_tick_delay (node)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current )) (PreH7 : (time_tick_lookup current tid node )) (PreH8 : (0 <= (time_tick_y (node)))) (PreH9 : ((time_tick_y (node)) < 8)) (PreH10 : (0 <= (time_tick_delay (node)))) (PreH11 : ((time_tick_delay (node)) < 4294967296)) (PreH12 : ((time_tick_priority (node)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH17 : ((time_tick_process_byte (hook_state)) = 1)) (PreH18 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH19 : (UCOS2_state_inv sg current )) (PreH20 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ ((Z.land (time_tick_status (node)) 8) <> 0) ” 
  &&  “ ((Z.land (time_tick_status (node)) 55) = 0) ” 
  &&  “ ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0) ” 
  &&  “ ((time_tick_delay (node)) <> 0) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ” 
  &&  “ (0 <= (time_tick_y (node))) ” 
  &&  “ ((time_tick_y (node)) < 8) ” 
  &&  “ (0 <= (time_tick_delay (node))) ” 
  &&  “ ((time_tick_delay (node)) < 4294967296) ” 
  &&  “ ((time_tick_priority (node)) <> 63) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_31 := OSTimeTick_partial_solve_wit_31_pure -> OSTimeTick_partial_solve_wit_31_aux.

Definition OSTimeTick_partial_solve_wit_32_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))) 8) <> 0)) (PreH2 : ((Z.land (time_tick_status (node)) 55) <> 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0)) (PreH4 : ((time_tick_delay (node)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current )) (PreH7 : (time_tick_lookup current tid node )) (PreH8 : (0 <= (time_tick_y (node)))) (PreH9 : ((time_tick_y (node)) < 8)) (PreH10 : (0 <= (time_tick_delay (node)))) (PreH11 : ((time_tick_delay (node)) < 4294967296)) (PreH12 : ((time_tick_priority (node)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH17 : ((time_tick_process_byte (hook_state)) = 1)) (PreH18 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH19 : (UCOS2_state_inv sg current )) (PreH20 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 1)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ”
.

Definition OSTimeTick_partial_solve_wit_32_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((Z.land (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))) 8) <> 0)) (PreH2 : ((Z.land (time_tick_status (node)) 55) <> 0)) (PreH3 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0)) (PreH4 : ((time_tick_delay (node)) <> 0)) (PreH5 : (interrupt_saved_value 192 retval )) (PreH6 : (UCOS2_state_inv sg current )) (PreH7 : (time_tick_lookup current tid node )) (PreH8 : (0 <= (time_tick_y (node)))) (PreH9 : ((time_tick_y (node)) < 8)) (PreH10 : (0 <= (time_tick_delay (node)))) (PreH11 : ((time_tick_delay (node)) < 4294967296)) (PreH12 : ((time_tick_priority (node)) <> 63)) (PreH13 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (time_tick_entry sg invocation origin initial )) (PreH15 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH16 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH17 : ((time_tick_process_byte (hook_state)) = 1)) (PreH18 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH19 : (UCOS2_state_inv sg current )) (PreH20 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 1)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ ((Z.land (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))) 8) <> 0) ” 
  &&  “ ((Z.land (time_tick_status (node)) 55) <> 0) ” 
  &&  “ ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) = 0) ” 
  &&  “ ((time_tick_delay (node)) <> 0) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ” 
  &&  “ (0 <= (time_tick_y (node))) ” 
  &&  “ ((time_tick_y (node)) < 8) ” 
  &&  “ (0 <= (time_tick_delay (node))) ” 
  &&  “ ((time_tick_delay (node)) < 4294967296) ” 
  &&  “ ((time_tick_priority (node)) <> 63) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (time_tick_status (node)) (unsigned_last_nbits ((Z.lnot 55)) (8))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 1)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_32 := OSTimeTick_partial_solve_wit_32_pure -> OSTimeTick_partial_solve_wit_32_aux.

Definition OSTimeTick_partial_solve_wit_33_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) <> 0)) (PreH2 : ((time_tick_delay (node)) <> 0)) (PreH3 : (interrupt_saved_value 192 retval )) (PreH4 : (UCOS2_state_inv sg current )) (PreH5 : (time_tick_lookup current tid node )) (PreH6 : (0 <= (time_tick_y (node)))) (PreH7 : ((time_tick_y (node)) < 8)) (PreH8 : (0 <= (time_tick_delay (node)))) (PreH9 : ((time_tick_delay (node)) < 4294967296)) (PreH10 : ((time_tick_priority (node)) <> 63)) (PreH11 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (time_tick_entry sg invocation origin initial )) (PreH13 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH14 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH15 : ((time_tick_process_byte (hook_state)) = 1)) (PreH16 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH17 : (UCOS2_state_inv sg current )) (PreH18 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (time_tick_pend_result (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ”
.

Definition OSTimeTick_partial_solve_wit_33_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) <> 0)) (PreH2 : ((time_tick_delay (node)) <> 0)) (PreH3 : (interrupt_saved_value 192 retval )) (PreH4 : (UCOS2_state_inv sg current )) (PreH5 : (time_tick_lookup current tid node )) (PreH6 : (0 <= (time_tick_y (node)))) (PreH7 : ((time_tick_y (node)) < 8)) (PreH8 : (0 <= (time_tick_delay (node)))) (PreH9 : ((time_tick_delay (node)) < 4294967296)) (PreH10 : ((time_tick_priority (node)) <> 63)) (PreH11 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (time_tick_entry sg invocation origin initial )) (PreH13 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH14 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH15 : ((time_tick_process_byte (hook_state)) = 1)) (PreH16 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH17 : (UCOS2_state_inv sg current )) (PreH18 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (time_tick_pend_result (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ ((unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)) <> 0) ” 
  &&  “ ((time_tick_delay (node)) <> 0) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ” 
  &&  “ (0 <= (time_tick_y (node))) ” 
  &&  “ ((time_tick_y (node)) < 8) ” 
  &&  “ (0 <= (time_tick_delay (node))) ” 
  &&  “ ((time_tick_delay (node)) < 4294967296) ” 
  &&  “ ((time_tick_priority (node)) <> 63) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (unsigned_last_nbits (((time_tick_delay (node)) - 1 )) (32)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (time_tick_pend_result (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_33 := OSTimeTick_partial_solve_wit_33_pure -> OSTimeTick_partial_solve_wit_33_aux.

Definition OSTimeTick_partial_solve_wit_34_pure := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((time_tick_delay (node)) = 0)) (PreH2 : (interrupt_saved_value 192 retval )) (PreH3 : (UCOS2_state_inv sg current )) (PreH4 : (time_tick_lookup current tid node )) (PreH5 : (0 <= (time_tick_y (node)))) (PreH6 : ((time_tick_y (node)) < 8)) (PreH7 : (0 <= (time_tick_delay (node)))) (PreH8 : ((time_tick_delay (node)) < 4294967296)) (PreH9 : ((time_tick_priority (node)) <> 63)) (PreH10 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (time_tick_entry sg invocation origin initial )) (PreH12 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : ((time_tick_process_byte (hook_state)) = 1)) (PreH15 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH16 : (UCOS2_state_inv sg current )) (PreH17 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (time_tick_delay (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (time_tick_pend_result (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  ((( &( "step" ) )) # UChar  |-> 1)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ”
.

Definition OSTimeTick_partial_solve_wit_34_aux := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (visited: (@list Z)) (remaining: (@list Z)) (current: UCOS2_Verify_State) (tid: Z) (node: TaskAbstractState) (app_after: Z) (counter_after: Z) (hook_state: UCOS2_Verify_State) (retval: Z) (PreH1 : ((time_tick_delay (node)) = 0)) (PreH2 : (interrupt_saved_value 192 retval )) (PreH3 : (UCOS2_state_inv sg current )) (PreH4 : (time_tick_lookup current tid node )) (PreH5 : (0 <= (time_tick_y (node)))) (PreH6 : ((time_tick_y (node)) < 8)) (PreH7 : (0 <= (time_tick_delay (node)))) (PreH8 : ((time_tick_delay (node)) < 4294967296)) (PreH9 : ((time_tick_priority (node)) <> 63)) (PreH10 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (time_tick_entry sg invocation origin initial )) (PreH12 : (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X )) (PreH13 : (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state )) (PreH14 : ((time_tick_process_byte (hook_state)) = 1)) (PreH15 : (time_tick_cursor sg hook_state visited remaining current tid node )) (PreH16 : (UCOS2_state_inv sg current )) (PreH17 : (time_tick_lookup current tid node )) ,
  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (time_tick_delay (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (time_tick_pend_result (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
|--
  “ (retval = retval) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ ((time_tick_delay (node)) = 0) ” 
  &&  “ (interrupt_saved_value 192 retval ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ” 
  &&  “ (0 <= (time_tick_y (node))) ” 
  &&  “ ((time_tick_y (node)) < 8) ” 
  &&  “ (0 <= (time_tick_delay (node))) ” 
  &&  “ ((time_tick_delay (node)) < 4294967296) ” 
  &&  “ ((time_tick_priority (node)) <> 63) ” 
  &&  “ (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ” 
  &&  “ ((time_tick_process_byte (hook_state)) = 1) ” 
  &&  “ (time_tick_cursor sg hook_state visited remaining current tid node ) ” 
  &&  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ”
  &&  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (time_tick_delay (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (time_tick_pend_result (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
.

Definition OSTimeTick_partial_solve_wit_34 := OSTimeTick_partial_solve_wit_34_pure -> OSTimeTick_partial_solve_wit_34_aux.

Definition OSTimeTick_which_implies_wit_1 := 
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (time_tick_pre platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
|--
  “ (time_tick_entry sg invocation origin initial ) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (counter <= 65535) ”
  &&  (time_tick_owned platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry app_value counter_address counter initial )
) \/
(
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (time_tick_pre platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
|--
  “ (counter <= 65535) ” 
  &&  “ (0 <= counter) ” 
  &&  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ” 
  &&  “ (time_tick_entry sg invocation origin initial ) ”
  &&  (time_tick_owned platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry app_value counter_address counter initial )
).

Definition OSTimeTick_which_implies_wit_1_split_goal_1 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (time_tick_pre platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
|--
  “ (counter <= 65535) ”
.

Definition OSTimeTick_which_implies_wit_1_split_goal_2 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (time_tick_pre platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
|--
  “ (0 <= counter) ”
.

Definition OSTimeTick_which_implies_wit_1_split_goal_3 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (time_tick_pre platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
|--
  “ (time_tick_continuation (time_tick_fixed_application (sg) (application)) sg app_value counter initial X ) ”
.

Definition OSTimeTick_which_implies_wit_1_split_goal_4 := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (time_tick_pre platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
|--
  “ (time_tick_entry sg invocation origin initial ) ”
.

Definition OSTimeTick_which_implies_wit_1_split_goal_spatial := 
forall (X: (UCOS2_Verify_State -> Prop)) (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (time_tick_pre platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry initial app_value counter_address counter X )
|--
  (time_tick_owned platform critical (time_tick_fixed_application (sg) (application)) sg invocation origin region_entry app_value counter_address counter initial )
.

Definition OSTimeTick_which_implies_wit_2 := 
(
forall (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (( &( "OSTmrCtr" ) ) = counter_address)) ,
  (time_tick_hook_isr_post platform critical application sg invocation origin region_entry initial app_value ( &( "OSTmrCtr" ) ) counter )
|--
  EX (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  (UCOS2_inv sg hook_state )
) \/
(
forall (counter: Z) (counter_address: Z) (app_value: Z) (initial: UCOS2_Verify_State) (region_entry: UCOS2_Verify_State) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (application: TimeTickApplicationResources) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (( &( "OSTmrCtr" ) ) = counter_address)) ,
  (time_tick_hook_isr_post platform critical application sg invocation origin region_entry initial app_value ( &( "OSTmrCtr" ) ) counter )
|--
  EX (app_after: Z)  (counter_after: Z)  (hook_state: UCOS2_Verify_State) ,
  “ (time_tick_hook_result (time_tick_fixed_application (sg) (application)) sg app_value counter initial app_after counter_after hook_state ) ”
  &&  (interrupt_platform_running platform invocation origin 192 )
  **  (time_tick_client_frame critical (time_tick_fixed_application (sg) (application)) sg invocation region_entry app_after counter_address counter_after )
  **  (UCOS2_inv sg hook_state )
).

Definition OSTimeTick_which_implies_wit_3 := 
(
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg hook_state )
|--
  “ (UCOS2_state_inv sg hook_state ) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ ((time_tick_step (hook_state)) < 256) ”
  &&  ((( &( "OSTime" ) )) # UInt  |-> (time_tick_time (hook_state)))
  **  (time_tick_without_time sg hook_state )
) \/
(
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg hook_state )
|--
  “ ((time_tick_step (hook_state)) < 256) ” 
  &&  “ (0 <= (time_tick_step (hook_state))) ” 
  &&  “ (0 <= (time_tick_time (hook_state))) ” 
  &&  “ (UCOS2_state_inv sg hook_state ) ”
  &&  ((( &( "OSTime" ) )) # UInt  |-> (time_tick_time (hook_state)))
  **  (time_tick_without_time sg hook_state )
).

Definition OSTimeTick_which_implies_wit_3_split_goal_1 := 
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg hook_state )
|--
  “ ((time_tick_step (hook_state)) < 256) ”
.

Definition OSTimeTick_which_implies_wit_3_split_goal_2 := 
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg hook_state )
|--
  “ (0 <= (time_tick_step (hook_state))) ”
.

Definition OSTimeTick_which_implies_wit_3_split_goal_3 := 
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg hook_state )
|--
  “ (0 <= (time_tick_time (hook_state))) ”
.

Definition OSTimeTick_which_implies_wit_3_split_goal_4 := 
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg hook_state )
|--
  “ (UCOS2_state_inv sg hook_state ) ”
.

Definition OSTimeTick_which_implies_wit_3_split_goal_spatial := 
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg hook_state )
|--
  ((( &( "OSTime" ) )) # UInt  |-> (time_tick_time (hook_state)))
  **  (time_tick_without_time sg hook_state )
.

Definition OSTimeTick_which_implies_wit_4 := 
(
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (UCOS2_state_inv sg hook_state )) (PreH3 : (0 <= (time_tick_time (hook_state)))) (PreH4 : (0 <= (time_tick_step (hook_state)))) (PreH5 : ((time_tick_step (hook_state)) < 256)) ,
  ((( &( "OSTime" ) )) # UInt  |-> (((time_tick_time (hook_state)) + 1 ) % ( 4294967296 ) ))
  **  (time_tick_without_time sg hook_state )
|--
  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
) \/
(
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : ((((time_tick_time (hook_state)) + 1 ) % ( 4294967296 ) ) <= UINT_MAX)) (PreH2 : ((((time_tick_time (hook_state)) + 1 ) % ( 4294967296 ) ) >= 0)) (PreH3 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (UCOS2_state_inv sg hook_state )) (PreH5 : (0 <= (time_tick_time (hook_state)))) (PreH6 : (0 <= (time_tick_step (hook_state)))) (PreH7 : ((time_tick_step (hook_state)) < 256)) ,
  ((( &( "OSTime" ) )) # UInt  |-> (((time_tick_time (hook_state)) + 1 ) % ( 4294967296 ) ))
  **  (time_tick_without_time sg hook_state )
|--
  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
).

Definition OSTimeTick_which_implies_wit_4_split_goal_spatial := 
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : ((((time_tick_time (hook_state)) + 1 ) % ( 4294967296 ) ) <= UINT_MAX)) (PreH2 : ((((time_tick_time (hook_state)) + 1 ) % ( 4294967296 ) ) >= 0)) (PreH3 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (UCOS2_state_inv sg hook_state )) (PreH5 : (0 <= (time_tick_time (hook_state)))) (PreH6 : (0 <= (time_tick_step (hook_state)))) (PreH7 : ((time_tick_step (hook_state)) < 256)) ,
  ((( &( "OSTime" ) )) # UInt  |-> (((time_tick_time (hook_state)) + 1 ) % ( 4294967296 ) ))
  **  (time_tick_without_time sg hook_state )
|--
  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
.

Definition OSTimeTick_which_implies_wit_5 := 
(
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
|--
  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ”
  &&  ((( &( "OSRunning" ) )) # UChar  |-> (time_tick_running (hook_state)))
  **  (time_tick_sched_without_running sg (time_tick_counted_state (hook_state)) )
) \/
(
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
|--
  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ”
  &&  ((( &( "OSRunning" ) )) # UChar  |-> (time_tick_running (hook_state)))
  **  (time_tick_sched_without_running sg (time_tick_counted_state (hook_state)) )
).

Definition OSTimeTick_which_implies_wit_5_split_goal_1 := 
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
|--
  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ”
.

Definition OSTimeTick_which_implies_wit_5_split_goal_spatial := 
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
|--
  ((( &( "OSRunning" ) )) # UChar  |-> (time_tick_running (hook_state)))
  **  (time_tick_sched_without_running sg (time_tick_counted_state (hook_state)) )
.

Definition OSTimeTick_which_implies_wit_6 := 
(
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (time_tick_running (hook_state)))
  **  (time_tick_sched_without_running sg (time_tick_counted_state (hook_state)) )
|--
  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
) \/
(
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (time_tick_running (hook_state)))
  **  (time_tick_sched_without_running sg (time_tick_counted_state (hook_state)) )
|--
  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
).

Definition OSTimeTick_which_implies_wit_6_split_goal_spatial := 
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (time_tick_running (hook_state)))
  **  (time_tick_sched_without_running sg (time_tick_counted_state (hook_state)) )
|--
  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
.

Definition OSTimeTick_which_implies_wit_7 := 
(
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
|--
  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ”
  &&  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step (hook_state)))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
) \/
(
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
|--
  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ” 
  &&  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ” 
  &&  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ”
  &&  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step (hook_state)))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
).

Definition OSTimeTick_which_implies_wit_7_split_goal_1 := 
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
|--
  “ ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296) ”
.

Definition OSTimeTick_which_implies_wit_7_split_goal_2 := 
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
|--
  “ (0 <= (time_tick_time ((time_tick_counted_state (hook_state))))) ”
.

Definition OSTimeTick_which_implies_wit_7_split_goal_3 := 
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
|--
  “ (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) ) ”
.

Definition OSTimeTick_which_implies_wit_7_split_goal_spatial := 
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg (time_tick_counted_state (hook_state)) )
|--
  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step (hook_state)))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
.

Definition OSTimeTick_which_implies_wit_8 := 
(
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (step: Z) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : ((time_tick_running (hook_state)) = 1)) (PreH3 : (step = (time_tick_process_byte (hook_state)))) (PreH4 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH5 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH6 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step ((time_tick_clock_step_state (hook_state)))))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
|--
  “ (step = (time_tick_process_byte (hook_state))) ”
  &&  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
) \/
(
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (step: Z) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : ((time_tick_running (hook_state)) = 1)) (PreH3 : (step = (time_tick_process_byte (hook_state)))) (PreH4 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH5 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH6 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step ((time_tick_clock_step_state (hook_state)))))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
|--
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
).

Definition OSTimeTick_which_implies_wit_8_split_goal_spatial := 
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (step: Z) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : ((time_tick_running (hook_state)) = 1)) (PreH3 : (step = (time_tick_process_byte (hook_state)))) (PreH4 : (UCOS2_state_inv sg (time_tick_counted_state (hook_state)) )) (PreH5 : (0 <= (time_tick_time ((time_tick_counted_state (hook_state)))))) (PreH6 : ((time_tick_time ((time_tick_counted_state (hook_state)))) < 4294967296)) ,
  ((( &( "OSTickStepState" ) )) # UChar  |-> (time_tick_step ((time_tick_clock_step_state (hook_state)))))
  **  (time_tick_without_step sg (time_tick_counted_state (hook_state)) )
|--
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
.

Definition OSTimeTick_which_implies_wit_9 := 
(
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
|--
  “ (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) ) ”
  &&  ((( &( "OSTCBList" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
  **  (time_tick_task_without_head sg (time_tick_clock_step_state (hook_state)) )
) \/
(
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
|--
  “ (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) ) ”
  &&  ((( &( "OSTCBList" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
  **  (time_tick_task_without_head sg (time_tick_clock_step_state (hook_state)) )
).

Definition OSTimeTick_which_implies_wit_9_split_goal_1 := 
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
|--
  “ (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) ) ”
.

Definition OSTimeTick_which_implies_wit_9_split_goal_spatial := 
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
|--
  ((( &( "OSTCBList" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
  **  (time_tick_task_without_head sg (time_tick_clock_step_state (hook_state)) )
.

Definition OSTimeTick_which_implies_wit_10 := 
(
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) )) ,
  ((( &( "OSTCBList" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
  **  (time_tick_task_without_head sg (time_tick_clock_step_state (hook_state)) )
|--
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
) \/
(
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) )) ,
  ((( &( "OSTCBList" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
  **  (time_tick_task_without_head sg (time_tick_clock_step_state (hook_state)) )
|--
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
).

Definition OSTimeTick_which_implies_wit_10_split_goal_spatial := 
forall (sg: StableGlobVars) (hook_state: UCOS2_Verify_State) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (UCOS2_state_inv sg (time_tick_clock_step_state (hook_state)) )) ,
  ((( &( "OSTCBList" ) )) # Ptr  |-> (time_tick_list_head (sg) (hook_state)))
  **  (time_tick_task_without_head sg (time_tick_clock_step_state (hook_state)) )
|--
  (UCOS2_inv sg (time_tick_clock_step_state (hook_state)) )
.

Definition OSTimeTick_which_implies_wit_11 := 
(
forall (sg: StableGlobVars) (node: TaskAbstractState) (tid: Z) (current: UCOS2_Verify_State) (ptcb: Z) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH3 : (time_tick_lookup current tid node )) (PreH4 : (UCOS2_state_inv sg current )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
|--
  “ (UCOS2_state_inv sg current ) ” 
  &&  “ (time_tick_lookup current tid node ) ” 
  &&  “ (0 <= (time_tick_y (node))) ” 
  &&  “ ((time_tick_y (node)) < 8) ” 
  &&  “ (0 <= (time_tick_delay (node))) ” 
  &&  “ ((time_tick_delay (node)) < 4294967296) ”
  &&  ((( &( "ptcb" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (time_tick_delay (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (time_tick_pend_result (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
) \/
(
forall (sg: StableGlobVars) (node: TaskAbstractState) (tid: Z) (current: UCOS2_Verify_State) (ptcb: Z) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH3 : (time_tick_lookup current tid node )) (PreH4 : (UCOS2_state_inv sg current )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
|--
  “ ((time_tick_delay (node)) < 4294967296) ” 
  &&  “ (0 <= (time_tick_delay (node))) ” 
  &&  “ ((time_tick_y (node)) < 8) ” 
  &&  “ (0 <= (time_tick_y (node))) ”
  &&  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (time_tick_delay (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (time_tick_pend_result (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
).

Definition OSTimeTick_which_implies_wit_11_split_goal_1 := 
forall (sg: StableGlobVars) (node: TaskAbstractState) (tid: Z) (current: UCOS2_Verify_State) (ptcb: Z) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH3 : (time_tick_lookup current tid node )) (PreH4 : (UCOS2_state_inv sg current )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
|--
  “ ((time_tick_delay (node)) < 4294967296) ”
.

Definition OSTimeTick_which_implies_wit_11_split_goal_2 := 
forall (sg: StableGlobVars) (node: TaskAbstractState) (tid: Z) (current: UCOS2_Verify_State) (ptcb: Z) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH3 : (time_tick_lookup current tid node )) (PreH4 : (UCOS2_state_inv sg current )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
|--
  “ (0 <= (time_tick_delay (node))) ”
.

Definition OSTimeTick_which_implies_wit_11_split_goal_3 := 
forall (sg: StableGlobVars) (node: TaskAbstractState) (tid: Z) (current: UCOS2_Verify_State) (ptcb: Z) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH3 : (time_tick_lookup current tid node )) (PreH4 : (UCOS2_state_inv sg current )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
|--
  “ ((time_tick_y (node)) < 8) ”
.

Definition OSTimeTick_which_implies_wit_11_split_goal_4 := 
forall (sg: StableGlobVars) (node: TaskAbstractState) (tid: Z) (current: UCOS2_Verify_State) (ptcb: Z) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH3 : (time_tick_lookup current tid node )) (PreH4 : (UCOS2_state_inv sg current )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
|--
  “ (0 <= (time_tick_y (node))) ”
.

Definition OSTimeTick_which_implies_wit_11_split_goal_spatial := 
forall (sg: StableGlobVars) (node: TaskAbstractState) (tid: Z) (current: UCOS2_Verify_State) (ptcb: Z) (PreH1 : (time_tick_global_addresses sg ( &( "OSTime" ) ) ( &( "OSTickStepState" ) ) ( &( "OSRunning" ) ) ( &( "OSTCBList" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (ptcb = (task_slot_addr (sg) (tid)))) (PreH3 : (time_tick_lookup current tid node )) (PreH4 : (UCOS2_state_inv sg current )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  (time_tick_cursor_residual sg current tid node )
|--
  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (time_tick_delay (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (time_tick_status (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (time_tick_pend_result (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (time_tick_priority (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (time_tick_next (sg) (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (time_tick_y (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (time_tick_bit_x (node)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (time_tick_bit_y (node)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_tick_ready_group (current)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (time_tick_ready_rows (current)) )
  **  (time_tick_body_residual sg current tid node )
.

Module Type VC_Correct.


Axiom proof_of_OSTimeTick_safety_wit_1 : OSTimeTick_safety_wit_1.
Axiom proof_of_OSTimeTick_safety_wit_2 : OSTimeTick_safety_wit_2.
Axiom proof_of_OSTimeTick_safety_wit_3 : OSTimeTick_safety_wit_3.
Axiom proof_of_OSTimeTick_safety_wit_4 : OSTimeTick_safety_wit_4.
Axiom proof_of_OSTimeTick_safety_wit_5 : OSTimeTick_safety_wit_5.
Axiom proof_of_OSTimeTick_safety_wit_6 : OSTimeTick_safety_wit_6.
Axiom proof_of_OSTimeTick_safety_wit_7 : OSTimeTick_safety_wit_7.
Axiom proof_of_OSTimeTick_safety_wit_8 : OSTimeTick_safety_wit_8.
Axiom proof_of_OSTimeTick_safety_wit_9 : OSTimeTick_safety_wit_9.
Axiom proof_of_OSTimeTick_safety_wit_10 : OSTimeTick_safety_wit_10.
Axiom proof_of_OSTimeTick_safety_wit_11 : OSTimeTick_safety_wit_11.
Axiom proof_of_OSTimeTick_safety_wit_12 : OSTimeTick_safety_wit_12.
Axiom proof_of_OSTimeTick_entail_wit_1_1 : OSTimeTick_entail_wit_1_1.
Axiom proof_of_OSTimeTick_entail_wit_1_2 : OSTimeTick_entail_wit_1_2.
Axiom proof_of_OSTimeTick_entail_wit_1_3 : OSTimeTick_entail_wit_1_3.
Axiom proof_of_OSTimeTick_entail_wit_1_4 : OSTimeTick_entail_wit_1_4.
Axiom proof_of_OSTimeTick_entail_wit_2_1 : OSTimeTick_entail_wit_2_1.
Axiom proof_of_OSTimeTick_entail_wit_2_2 : OSTimeTick_entail_wit_2_2.
Axiom proof_of_OSTimeTick_entail_wit_2_3 : OSTimeTick_entail_wit_2_3.
Axiom proof_of_OSTimeTick_entail_wit_2_4 : OSTimeTick_entail_wit_2_4.
Axiom proof_of_OSTimeTick_entail_wit_2_5 : OSTimeTick_entail_wit_2_5.
Axiom proof_of_OSTimeTick_entail_wit_2_6 : OSTimeTick_entail_wit_2_6.
Axiom proof_of_OSTimeTick_return_wit_1 : OSTimeTick_return_wit_1.
Axiom proof_of_OSTimeTick_return_wit_2 : OSTimeTick_return_wit_2.
Axiom proof_of_OSTimeTick_return_wit_3 : OSTimeTick_return_wit_3.
Axiom proof_of_OSTimeTick_return_wit_4 : OSTimeTick_return_wit_4.
Axiom proof_of_OSTimeTick_return_wit_5 : OSTimeTick_return_wit_5.
Axiom proof_of_OSTimeTick_return_wit_6 : OSTimeTick_return_wit_6.
Axiom proof_of_OSTimeTick_partial_solve_wit_1 : OSTimeTick_partial_solve_wit_1.
Axiom proof_of_OSTimeTick_partial_solve_wit_2_pure : OSTimeTick_partial_solve_wit_2_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_2 : OSTimeTick_partial_solve_wit_2.
Axiom proof_of_OSTimeTick_partial_solve_wit_3_pure : OSTimeTick_partial_solve_wit_3_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_3 : OSTimeTick_partial_solve_wit_3.
Axiom proof_of_OSTimeTick_partial_solve_wit_4 : OSTimeTick_partial_solve_wit_4.
Axiom proof_of_OSTimeTick_partial_solve_wit_5_pure : OSTimeTick_partial_solve_wit_5_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_5 : OSTimeTick_partial_solve_wit_5.
Axiom proof_of_OSTimeTick_partial_solve_wit_6_pure : OSTimeTick_partial_solve_wit_6_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_6 : OSTimeTick_partial_solve_wit_6.
Axiom proof_of_OSTimeTick_partial_solve_wit_7_pure : OSTimeTick_partial_solve_wit_7_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_7 : OSTimeTick_partial_solve_wit_7.
Axiom proof_of_OSTimeTick_partial_solve_wit_8_pure : OSTimeTick_partial_solve_wit_8_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_8 : OSTimeTick_partial_solve_wit_8.
Axiom proof_of_OSTimeTick_partial_solve_wit_9_pure : OSTimeTick_partial_solve_wit_9_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_9 : OSTimeTick_partial_solve_wit_9.
Axiom proof_of_OSTimeTick_partial_solve_wit_10_pure : OSTimeTick_partial_solve_wit_10_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_10 : OSTimeTick_partial_solve_wit_10.
Axiom proof_of_OSTimeTick_partial_solve_wit_11_pure : OSTimeTick_partial_solve_wit_11_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_11 : OSTimeTick_partial_solve_wit_11.
Axiom proof_of_OSTimeTick_partial_solve_wit_12_pure : OSTimeTick_partial_solve_wit_12_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_12 : OSTimeTick_partial_solve_wit_12.
Axiom proof_of_OSTimeTick_partial_solve_wit_13_pure : OSTimeTick_partial_solve_wit_13_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_13 : OSTimeTick_partial_solve_wit_13.
Axiom proof_of_OSTimeTick_partial_solve_wit_14_pure : OSTimeTick_partial_solve_wit_14_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_14 : OSTimeTick_partial_solve_wit_14.
Axiom proof_of_OSTimeTick_partial_solve_wit_15_pure : OSTimeTick_partial_solve_wit_15_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_15 : OSTimeTick_partial_solve_wit_15.
Axiom proof_of_OSTimeTick_partial_solve_wit_16_pure : OSTimeTick_partial_solve_wit_16_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_16 : OSTimeTick_partial_solve_wit_16.
Axiom proof_of_OSTimeTick_partial_solve_wit_17_pure : OSTimeTick_partial_solve_wit_17_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_17 : OSTimeTick_partial_solve_wit_17.
Axiom proof_of_OSTimeTick_partial_solve_wit_18_pure : OSTimeTick_partial_solve_wit_18_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_18 : OSTimeTick_partial_solve_wit_18.
Axiom proof_of_OSTimeTick_partial_solve_wit_19_pure : OSTimeTick_partial_solve_wit_19_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_19 : OSTimeTick_partial_solve_wit_19.
Axiom proof_of_OSTimeTick_partial_solve_wit_20_pure : OSTimeTick_partial_solve_wit_20_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_20 : OSTimeTick_partial_solve_wit_20.
Axiom proof_of_OSTimeTick_partial_solve_wit_21_pure : OSTimeTick_partial_solve_wit_21_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_21 : OSTimeTick_partial_solve_wit_21.
Axiom proof_of_OSTimeTick_partial_solve_wit_22_pure : OSTimeTick_partial_solve_wit_22_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_22 : OSTimeTick_partial_solve_wit_22.
Axiom proof_of_OSTimeTick_partial_solve_wit_23_pure : OSTimeTick_partial_solve_wit_23_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_23 : OSTimeTick_partial_solve_wit_23.
Axiom proof_of_OSTimeTick_partial_solve_wit_24 : OSTimeTick_partial_solve_wit_24.
Axiom proof_of_OSTimeTick_partial_solve_wit_25 : OSTimeTick_partial_solve_wit_25.
Axiom proof_of_OSTimeTick_partial_solve_wit_26 : OSTimeTick_partial_solve_wit_26.
Axiom proof_of_OSTimeTick_partial_solve_wit_27 : OSTimeTick_partial_solve_wit_27.
Axiom proof_of_OSTimeTick_partial_solve_wit_28 : OSTimeTick_partial_solve_wit_28.
Axiom proof_of_OSTimeTick_partial_solve_wit_29_pure : OSTimeTick_partial_solve_wit_29_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_29 : OSTimeTick_partial_solve_wit_29.
Axiom proof_of_OSTimeTick_partial_solve_wit_30_pure : OSTimeTick_partial_solve_wit_30_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_30 : OSTimeTick_partial_solve_wit_30.
Axiom proof_of_OSTimeTick_partial_solve_wit_31_pure : OSTimeTick_partial_solve_wit_31_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_31 : OSTimeTick_partial_solve_wit_31.
Axiom proof_of_OSTimeTick_partial_solve_wit_32_pure : OSTimeTick_partial_solve_wit_32_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_32 : OSTimeTick_partial_solve_wit_32.
Axiom proof_of_OSTimeTick_partial_solve_wit_33_pure : OSTimeTick_partial_solve_wit_33_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_33 : OSTimeTick_partial_solve_wit_33.
Axiom proof_of_OSTimeTick_partial_solve_wit_34_pure : OSTimeTick_partial_solve_wit_34_pure.
Axiom proof_of_OSTimeTick_partial_solve_wit_34 : OSTimeTick_partial_solve_wit_34.
Axiom proof_of_OSTimeTick_which_implies_wit_1 : OSTimeTick_which_implies_wit_1.
Axiom proof_of_OSTimeTick_which_implies_wit_2 : OSTimeTick_which_implies_wit_2.
Axiom proof_of_OSTimeTick_which_implies_wit_3 : OSTimeTick_which_implies_wit_3.
Axiom proof_of_OSTimeTick_which_implies_wit_4 : OSTimeTick_which_implies_wit_4.
Axiom proof_of_OSTimeTick_which_implies_wit_5 : OSTimeTick_which_implies_wit_5.
Axiom proof_of_OSTimeTick_which_implies_wit_6 : OSTimeTick_which_implies_wit_6.
Axiom proof_of_OSTimeTick_which_implies_wit_7 : OSTimeTick_which_implies_wit_7.
Axiom proof_of_OSTimeTick_which_implies_wit_8 : OSTimeTick_which_implies_wit_8.
Axiom proof_of_OSTimeTick_which_implies_wit_9 : OSTimeTick_which_implies_wit_9.
Axiom proof_of_OSTimeTick_which_implies_wit_10 : OSTimeTick_which_implies_wit_10.
Axiom proof_of_OSTimeTick_which_implies_wit_11 : OSTimeTick_which_implies_wit_11.

End VC_Correct.
