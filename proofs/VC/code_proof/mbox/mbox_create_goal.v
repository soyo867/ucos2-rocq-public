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
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_create_api_spec.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.event_pool Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSMboxCreate -----*)

Definition OSMboxCreate_safety_wit_1 := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((intNesting ((IntrState (initial)))) > 0)) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (0 <= (intNesting ((IntrState (initial)))))) (PreH4 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  (mbox_create_call_pre environment critical sg call mask initial pmsg_pre X )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxCreate_safety_wit_2 := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH2 : ((intNesting ((IntrState (initial)))) <= 0)) (PreH3 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH4 : (0 <= (intNesting ((IntrState (initial)))))) (PreH5 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  (q_create_save_output environment critical QCreateNoPrivate mbox_create_call_frame sg call mask retval initial )
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxCreate_safety_wit_3 := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH2 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) ,
  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_create_masked_control environment critical sg first_call cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  (sem_create_pool_frame sg entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxCreate_safety_wit_4 := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (allocation_result: (@option (Z * EventStorage))) (allocated: UCOS2_Verify_State) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (PreH1 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) (PreH2 : (event_create_allocate_critical entry allocation_result allocated )) (PreH3 : (pevent = (event_create_return_ptr (sg) (allocation_result)))) (PreH4 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) ,
  (q_create_restore_output environment critical (q_create_allocated_owner (entry) (allocation_result)) mbox_create_call_frame sg first_call cpu_sr allocated )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxCreate_safety_wit_5 := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (pevent: Z) (PreH1 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH2 : (interrupt_saved_value mask cpu_sr )) ,
  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (mbox_create_allocation_return environment critical sg call initial mask pevent )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxCreate_entail_wit_1 := 
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH2 : ((intNesting ((IntrState (initial)))) <= 0)) (PreH3 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH4 : (0 <= (intNesting ((IntrState (initial)))))) (PreH5 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  (q_create_save_output environment critical QCreateNoPrivate mbox_create_call_frame sg call mask retval initial )
|--
  EX (first_call: OsSchedCallContext)  (entry: UCOS2_Verify_State) ,
  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ” 
  &&  “ (q_create_first_facts critical sg call initial mask retval first_call entry ) ”
  &&  (q_create_masked_control environment critical sg first_call retval entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  (sem_create_pool_frame sg entry )
) \/
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH2 : ((intNesting ((IntrState (initial)))) <= 0)) (PreH3 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH4 : (0 <= (intNesting ((IntrState (initial)))))) (PreH5 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  (q_create_save_output environment critical QCreateNoPrivate mbox_create_call_frame sg call mask retval initial )
|--
  EX (first_call: OsSchedCallContext)  (entry: UCOS2_Verify_State) ,
  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ” 
  &&  “ (q_create_first_facts critical sg call initial mask retval first_call entry ) ”
  &&  (q_create_masked_control environment critical sg first_call retval entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  (sem_create_pool_frame sg entry )
).

Definition OSMboxCreate_entail_wit_2 := 
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_call_2: OsSchedCallContext) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((sem_create_pool_head (sg) (entry)) <> 0)) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (q_create_first_facts critical sg call initial mask cpu_sr first_call_2 entry )) ,
  (q_create_masked_control environment critical sg first_call_2 cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  (sem_create_pool_frame sg entry )
|--
  EX (eid: Z)  (rest: (@list Z))  (image: EventStorage)  (first_call: OsSchedCallContext)  (entry_2: UCOS2_Verify_State) ,
  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ” 
  &&  “ (q_create_first_facts critical sg call initial mask cpu_sr first_call entry_2 ) ” 
  &&  “ (sem_create_head_facts sg entry_2 eid rest image ) ” 
  &&  “ ((sem_create_pool_head (sg) (entry)) = (event_pool_addr (sg) (eid))) ”
  &&  (q_create_masked_control environment critical sg first_call cpu_sr entry_2 entry_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  ((&(((sem_create_pool_head (sg) (entry)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (sem_create_node_frame sg entry_2 eid image )
) \/
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_call_2: OsSchedCallContext) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((sem_create_pool_head (sg) (entry)) <> 0)) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (q_create_first_facts critical sg call initial mask cpu_sr first_call_2 entry )) ,
  (q_create_masked_control environment critical sg first_call_2 cpu_sr entry entry )
  **  (sem_create_pool_frame sg entry )
|--
  EX (eid: Z)  (rest: (@list Z))  (image: EventStorage)  (first_call: OsSchedCallContext)  (entry_2: UCOS2_Verify_State) ,
  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ” 
  &&  “ (q_create_first_facts critical sg call initial mask cpu_sr first_call entry_2 ) ” 
  &&  “ (sem_create_head_facts sg entry_2 eid rest image ) ” 
  &&  “ ((sem_create_pool_head (sg) (entry)) = (event_pool_addr (sg) (eid))) ”
  &&  (q_create_masked_control environment critical sg first_call cpu_sr entry_2 entry_2 )
  **  ((&(((sem_create_pool_head (sg) (entry)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (sem_create_node_frame sg entry_2 eid image )
).

Definition OSMboxCreate_entail_wit_3_1 := 
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (cpu_sr: Z) (pevent: Z) (PreH1 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH2 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) (PreH3 : (sem_create_head_facts sg entry eid rest image )) (PreH4 : (pevent = (event_pool_addr (sg) (eid)))) ,
  (q_create_masked_control environment critical sg first_call cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (sem_create_node_frame sg entry eid image )
|--
  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ”
  &&  (mbox_create_allocation_cut environment critical sg call initial mask cpu_sr pevent )
) \/
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (cpu_sr: Z) (pevent: Z) (PreH1 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH2 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) (PreH3 : (sem_create_head_facts sg entry eid rest image )) (PreH4 : (pevent = (event_pool_addr (sg) (eid)))) ,
  (q_create_masked_control environment critical sg first_call cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (sem_create_node_frame sg entry eid image )
|--
  (mbox_create_allocation_cut environment critical sg call initial mask cpu_sr pevent )
).

Definition OSMboxCreate_entail_wit_3_1_split_goal_spatial := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (cpu_sr: Z) (pevent: Z) (PreH1 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH2 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) (PreH3 : (sem_create_head_facts sg entry eid rest image )) (PreH4 : (pevent = (event_pool_addr (sg) (eid)))) ,
  (q_create_masked_control environment critical sg first_call cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (sem_create_node_frame sg entry eid image )
|--
  (mbox_create_allocation_cut environment critical sg call initial mask cpu_sr pevent )
.

Definition OSMboxCreate_entail_wit_3_2 := 
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((sem_create_pool_head (sg) (entry)) = 0)) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) ,
  (q_create_masked_control environment critical sg first_call cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  (sem_create_pool_frame sg entry )
|--
  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ”
  &&  (mbox_create_allocation_cut environment critical sg call initial mask cpu_sr (sem_create_pool_head (sg) (entry)) )
) \/
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((sem_create_pool_head (sg) (entry)) = 0)) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) ,
  (q_create_masked_control environment critical sg first_call cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  (sem_create_pool_frame sg entry )
|--
  (mbox_create_allocation_cut environment critical sg call initial mask cpu_sr (sem_create_pool_head (sg) (entry)) )
).

Definition OSMboxCreate_entail_wit_3_2_split_goal_spatial := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((sem_create_pool_head (sg) (entry)) = 0)) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) ,
  (q_create_masked_control environment critical sg first_call cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  (sem_create_pool_frame sg entry )
|--
  (mbox_create_allocation_cut environment critical sg call initial mask cpu_sr (sem_create_pool_head (sg) (entry)) )
.

Definition OSMboxCreate_entail_wit_4 := 
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (allocation_result: (@option (Z * EventStorage))) (allocated: UCOS2_Verify_State) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (PreH1 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) (PreH2 : (event_create_allocate_critical entry allocation_result allocated )) (PreH3 : (pevent = (event_create_return_ptr (sg) (allocation_result)))) (PreH4 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) ,
  (q_create_restore_output environment critical (q_create_allocated_owner (entry) (allocation_result)) mbox_create_call_frame sg first_call cpu_sr allocated )
|--
  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  (mbox_create_allocation_return environment critical sg call initial mask pevent )
) \/
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (allocation_result: (@option (Z * EventStorage))) (allocated: UCOS2_Verify_State) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (PreH1 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) (PreH2 : (event_create_allocate_critical entry allocation_result allocated )) (PreH3 : (pevent = (event_create_return_ptr (sg) (allocation_result)))) (PreH4 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) ,
  (q_create_restore_output environment critical (q_create_allocated_owner (entry) (allocation_result)) mbox_create_call_frame sg first_call cpu_sr allocated )
|--
  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  (mbox_create_allocation_return environment critical sg call initial mask pevent )
).

Definition OSMboxCreate_entail_wit_4_split_goal_1 := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (allocation_result: (@option (Z * EventStorage))) (allocated: UCOS2_Verify_State) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (PreH1 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) (PreH2 : (event_create_allocate_critical entry allocation_result allocated )) (PreH3 : (pevent = (event_create_return_ptr (sg) (allocation_result)))) (PreH4 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) ,
  (q_create_restore_output environment critical (q_create_allocated_owner (entry) (allocation_result)) mbox_create_call_frame sg first_call cpu_sr allocated )
|--
  “ (interrupt_saved_value mask cpu_sr ) ”
.

Definition OSMboxCreate_entail_wit_4_split_goal_spatial := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (allocation_result: (@option (Z * EventStorage))) (allocated: UCOS2_Verify_State) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (PreH1 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) (PreH2 : (event_create_allocate_critical entry allocation_result allocated )) (PreH3 : (pevent = (event_create_return_ptr (sg) (allocation_result)))) (PreH4 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) ,
  (q_create_restore_output environment critical (q_create_allocated_owner (entry) (allocation_result)) mbox_create_call_frame sg first_call cpu_sr allocated )
|--
  (mbox_create_allocation_return environment critical sg call initial mask pevent )
.

Definition OSMboxCreate_entail_wit_5 := 
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (pevent: Z) (allocation: EventPrivateAllocation) (current: UCOS2_Verify_State) (eid: Z) (PreH1 : (pevent = (event_pool_addr (sg) (eid)))) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (pevent <> 0)) (PreH4 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH5 : (interrupt_saved_value mask cpu_sr )) ,
  (event_wait_list_init_post &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  (mbox_create_initialization_context environment critical sg call initial mask eid allocation current )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 1)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pmsg_pre)
  **  (mbox_create_initialization_frame pevent (eventPrivateStorage (allocation)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  (mbox_create_call_post environment critical sg call mask pevent X )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (pevent: Z) (allocation: EventPrivateAllocation) (current: UCOS2_Verify_State) (eid: Z) (PreH1 : (pevent = (event_pool_addr (sg) (eid)))) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (pevent <> 0)) (PreH4 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH5 : (interrupt_saved_value mask cpu_sr )) ,
  (event_wait_list_init_post &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  (mbox_create_initialization_context environment critical sg call initial mask eid allocation current )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 1)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pmsg_pre)
  **  (mbox_create_initialization_frame pevent (eventPrivateStorage (allocation)) )
|--
  (mbox_create_call_post environment critical sg call mask pevent X )
).

Definition OSMboxCreate_entail_wit_5_split_goal_spatial := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (pevent: Z) (allocation: EventPrivateAllocation) (current: UCOS2_Verify_State) (eid: Z) (PreH1 : (pevent = (event_pool_addr (sg) (eid)))) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (pevent <> 0)) (PreH4 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH5 : (interrupt_saved_value mask cpu_sr )) ,
  (event_wait_list_init_post &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  (mbox_create_initialization_context environment critical sg call initial mask eid allocation current )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 1)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pmsg_pre)
  **  (mbox_create_initialization_frame pevent (eventPrivateStorage (allocation)) )
|--
  (mbox_create_call_post environment critical sg call mask pevent X )
.

Definition OSMboxCreate_entail_wit_6_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) ,
  (mbox_create_call_post environment critical sg call mask pevent X )
|--
  (mbox_create_call_post environment critical sg call mask pevent X )
.

Definition OSMboxCreate_entail_wit_6_2 := 
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (pevent: Z) (PreH1 : (pevent = 0)) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (interrupt_saved_value mask cpu_sr )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_create_allocation_return environment critical sg call initial mask pevent )
|--
  (mbox_create_call_post environment critical sg call mask pevent X )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (pevent: Z) (PreH1 : (pevent = 0)) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (interrupt_saved_value mask cpu_sr )) ,
  (mbox_create_allocation_return environment critical sg call initial mask pevent )
|--
  (mbox_create_call_post environment critical sg call mask pevent X )
).

Definition OSMboxCreate_entail_wit_6_2_split_goal_spatial := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (pevent: Z) (PreH1 : (pevent = 0)) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (interrupt_saved_value mask cpu_sr )) ,
  (mbox_create_allocation_return environment critical sg call initial mask pevent )
|--
  (mbox_create_call_post environment critical sg call mask pevent X )
.

Definition OSMboxCreate_return_wit_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) ,
  (mbox_create_call_post environment critical sg call mask pevent X )
|--
  (mbox_create_call_post environment critical sg call mask pevent X )
.

Definition OSMboxCreate_return_wit_2 := 
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((intNesting ((IntrState (initial)))) > 0)) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (0 <= (intNesting ((IntrState (initial)))))) (PreH4 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  (mbox_create_call_pre environment critical sg call mask initial pmsg_pre X )
|--
  (mbox_create_call_post environment critical sg call mask 0 X )
) \/
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((intNesting ((IntrState (initial)))) > 0)) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (0 <= (intNesting ((IntrState (initial)))))) (PreH4 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  (mbox_create_call_pre environment critical sg call mask initial pmsg_pre X )
|--
  (mbox_create_call_post environment critical sg call mask 0 X )
).

Definition OSMboxCreate_return_wit_2_split_goal_spatial := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((intNesting ((IntrState (initial)))) > 0)) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (0 <= (intNesting ((IntrState (initial)))))) (PreH4 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  (mbox_create_call_pre environment critical sg call mask initial pmsg_pre X )
|--
  (mbox_create_call_post environment critical sg call mask 0 X )
.

Definition OSMboxCreate_partial_solve_wit_1 := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) ,
  (mbox_create_call_pre environment critical sg call mask initial pmsg_pre X )
|--
  (mbox_create_call_pre environment critical sg call mask initial pmsg_pre X )
.

Definition OSMboxCreate_partial_solve_wit_2_pure := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((intNesting ((IntrState (initial)))) > 0)) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (0 <= (intNesting ((IntrState (initial)))))) (PreH4 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate mbox_create_call_frame sg call mask initial )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
|--
  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ”
.

Definition OSMboxCreate_partial_solve_wit_2_aux := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((intNesting ((IntrState (initial)))) > 0)) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (0 <= (intNesting ((IntrState (initial)))))) (PreH4 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate mbox_create_call_frame sg call mask initial )
|--
  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ” 
  &&  “ ((intNesting ((IntrState (initial)))) > 0) ” 
  &&  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ” 
  &&  “ (0 <= (intNesting ((IntrState (initial))))) ” 
  &&  “ ((intNesting ((IntrState (initial)))) <= 255) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate mbox_create_call_frame sg call mask initial )
.

Definition OSMboxCreate_partial_solve_wit_2 := OSMboxCreate_partial_solve_wit_2_pure -> OSMboxCreate_partial_solve_wit_2_aux.

Definition OSMboxCreate_partial_solve_wit_3_pure := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((intNesting ((IntrState (initial)))) <= 0)) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (0 <= (intNesting ((IntrState (initial)))))) (PreH4 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate mbox_create_call_frame sg call mask initial )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
|--
  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ”
.

Definition OSMboxCreate_partial_solve_wit_3_aux := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((intNesting ((IntrState (initial)))) <= 0)) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (0 <= (intNesting ((IntrState (initial)))))) (PreH4 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate mbox_create_call_frame sg call mask initial )
|--
  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ” 
  &&  “ ((intNesting ((IntrState (initial)))) <= 0) ” 
  &&  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ” 
  &&  “ (0 <= (intNesting ((IntrState (initial))))) ” 
  &&  “ ((intNesting ((IntrState (initial)))) <= 255) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate mbox_create_call_frame sg call mask initial )
.

Definition OSMboxCreate_partial_solve_wit_3 := OSMboxCreate_partial_solve_wit_3_pure -> OSMboxCreate_partial_solve_wit_3_aux.

Definition OSMboxCreate_partial_solve_wit_4 := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH2 : ((intNesting ((IntrState (initial)))) <= 0)) (PreH3 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH4 : (0 <= (intNesting ((IntrState (initial)))))) (PreH5 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  (q_create_save_input environment critical QCreateNoPrivate mbox_create_call_frame sg call mask initial )
|--
  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ” 
  &&  “ ((intNesting ((IntrState (initial)))) <= 0) ” 
  &&  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ” 
  &&  “ (0 <= (intNesting ((IntrState (initial))))) ” 
  &&  “ ((intNesting ((IntrState (initial)))) <= 255) ”
  &&  (q_create_save_input environment critical QCreateNoPrivate mbox_create_call_frame sg call mask initial )
.

Definition OSMboxCreate_partial_solve_wit_5 := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (PreH1 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) ,
  (mbox_create_allocation_cut environment critical sg call initial mask cpu_sr pevent )
|--
  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ”
  &&  (mbox_create_allocation_cut environment critical sg call initial mask cpu_sr pevent )
.

Definition OSMboxCreate_partial_solve_wit_6_pure := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (allocation_result: (@option (Z * EventStorage))) (allocated: UCOS2_Verify_State) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (PreH1 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) (PreH2 : (event_create_allocate_critical entry allocation_result allocated )) (PreH3 : (pevent = (event_create_return_ptr (sg) (allocation_result)))) (PreH4 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (q_create_restore_input environment critical (q_create_allocated_owner (entry) (allocation_result)) mbox_create_call_frame sg first_call cpu_sr entry allocated )
  **  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSMboxCreate_partial_solve_wit_6_aux := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (allocation_result: (@option (Z * EventStorage))) (allocated: UCOS2_Verify_State) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (PreH1 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) (PreH2 : (event_create_allocate_critical entry allocation_result allocated )) (PreH3 : (pevent = (event_create_return_ptr (sg) (allocation_result)))) (PreH4 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) ,
  (q_create_restore_input environment critical (q_create_allocated_owner (entry) (allocation_result)) mbox_create_call_frame sg first_call cpu_sr entry allocated )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (q_create_first_facts critical sg call initial mask cpu_sr first_call entry ) ” 
  &&  “ (event_create_allocate_critical entry allocation_result allocated ) ” 
  &&  “ (pevent = (event_create_return_ptr (sg) (allocation_result))) ” 
  &&  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ”
  &&  (q_create_restore_input environment critical (q_create_allocated_owner (entry) (allocation_result)) mbox_create_call_frame sg first_call cpu_sr entry allocated )
.

Definition OSMboxCreate_partial_solve_wit_6 := OSMboxCreate_partial_solve_wit_6_pure -> OSMboxCreate_partial_solve_wit_6_aux.

Definition OSMboxCreate_partial_solve_wit_7_pure := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (pevent: Z) (PreH1 : (pevent <> 0)) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (interrupt_saved_value mask cpu_sr )) ,
  ((( &( "pmsg" ) )) # Ptr  |-> pmsg_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (mbox_create_allocation_return environment critical sg call initial mask pevent )
|--
  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ” 
  &&  “ (pevent <> 0) ”
.

Definition OSMboxCreate_partial_solve_wit_7_aux := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (pevent: Z) (PreH1 : (pevent <> 0)) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (interrupt_saved_value mask cpu_sr )) ,
  (mbox_create_allocation_return environment critical sg call initial mask pevent )
|--
  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ” 
  &&  “ (pevent <> 0) ” 
  &&  “ (pevent <> 0) ” 
  &&  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  (mbox_create_allocation_return environment critical sg call initial mask pevent )
.

Definition OSMboxCreate_partial_solve_wit_7 := OSMboxCreate_partial_solve_wit_7_pure -> OSMboxCreate_partial_solve_wit_7_aux.

Definition OSMboxCreate_partial_solve_wit_8 := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (pevent: Z) (allocation: EventPrivateAllocation) (current: UCOS2_Verify_State) (eid: Z) (PreH1 : (pevent = (event_pool_addr (sg) (eid)))) (PreH2 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH3 : (pevent <> 0)) (PreH4 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH5 : (interrupt_saved_value mask cpu_sr )) ,
  (mbox_create_initialization_context environment critical sg call initial mask eid allocation current )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 1)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pmsg_pre)
  **  (event_wait_list_init_pre &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  (mbox_create_initialization_frame pevent (eventPrivateStorage (allocation)) )
|--
  “ (pevent = (event_pool_addr (sg) (eid))) ” 
  &&  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ” 
  &&  “ (pevent <> 0) ” 
  &&  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  (event_wait_list_init_pre &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  (mbox_create_initialization_context environment critical sg call initial mask eid allocation current )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 1)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pmsg_pre)
  **  (mbox_create_initialization_frame pevent (eventPrivateStorage (allocation)) )
.

Definition OSMboxCreate_which_implies_wit_1 := 
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) ,
  (mbox_create_call_pre environment critical sg call mask initial pmsg_pre X )
|--
  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ” 
  &&  “ (0 <= (intNesting ((IntrState (initial))))) ” 
  &&  “ ((intNesting ((IntrState (initial)))) <= 255) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate mbox_create_call_frame sg call mask initial )
) \/
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) ,
  (mbox_create_call_pre environment critical sg call mask initial pmsg_pre X )
|--
  “ ((intNesting ((IntrState (initial)))) <= 255) ” 
  &&  “ (0 <= (intNesting ((IntrState (initial))))) ” 
  &&  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate mbox_create_call_frame sg call mask initial )
).

Definition OSMboxCreate_which_implies_wit_1_split_goal_1 := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) ,
  (mbox_create_call_pre environment critical sg call mask initial pmsg_pre X )
|--
  “ ((intNesting ((IntrState (initial)))) <= 255) ”
.

Definition OSMboxCreate_which_implies_wit_1_split_goal_2 := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) ,
  (mbox_create_call_pre environment critical sg call mask initial pmsg_pre X )
|--
  “ (0 <= (intNesting ((IntrState (initial))))) ”
.

Definition OSMboxCreate_which_implies_wit_1_split_goal_3 := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) ,
  (mbox_create_call_pre environment critical sg call mask initial pmsg_pre X )
|--
  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ”
.

Definition OSMboxCreate_which_implies_wit_1_split_goal_spatial := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) ,
  (mbox_create_call_pre environment critical sg call mask initial pmsg_pre X )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate mbox_create_call_frame sg call mask initial )
.

Definition OSMboxCreate_which_implies_wit_2 := 
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate mbox_create_call_frame sg call mask initial )
|--
  (mbox_create_call_pre environment critical sg call mask initial pmsg_pre X )
) \/
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate mbox_create_call_frame sg call mask initial )
|--
  (mbox_create_call_pre environment critical sg call mask initial pmsg_pre X )
).

Definition OSMboxCreate_which_implies_wit_2_split_goal_spatial := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate mbox_create_call_frame sg call mask initial )
|--
  (mbox_create_call_pre environment critical sg call mask initial pmsg_pre X )
.

Definition OSMboxCreate_which_implies_wit_3 := 
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate mbox_create_call_frame sg call mask initial )
|--
  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ”
  &&  (q_create_save_input environment critical QCreateNoPrivate mbox_create_call_frame sg call mask initial )
) \/
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate mbox_create_call_frame sg call mask initial )
|--
  (q_create_save_input environment critical QCreateNoPrivate mbox_create_call_frame sg call mask initial )
).

Definition OSMboxCreate_which_implies_wit_3_split_goal_spatial := 
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate mbox_create_call_frame sg call mask initial )
|--
  (q_create_save_input environment critical QCreateNoPrivate mbox_create_call_frame sg call mask initial )
.

Definition OSMboxCreate_which_implies_wit_4 := 
(
forall (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) ,
  (mbox_create_allocation_cut environment critical sg call initial mask cpu_sr pevent )
|--
  EX (allocation_result: (@option (Z * EventStorage)))  (allocated: UCOS2_Verify_State)  (first_call: OsSchedCallContext)  (entry: UCOS2_Verify_State) ,
  “ (q_create_first_facts critical sg call initial mask cpu_sr first_call entry ) ” 
  &&  “ (event_create_allocate_critical entry allocation_result allocated ) ” 
  &&  “ (pevent = (event_create_return_ptr (sg) (allocation_result))) ”
  &&  (q_create_restore_input environment critical (q_create_allocated_owner (entry) (allocation_result)) mbox_create_call_frame sg first_call cpu_sr entry allocated )
) \/
(
forall (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) ,
  (mbox_create_allocation_cut environment critical sg call initial mask cpu_sr pevent )
|--
  EX (allocation_result: (@option (Z * EventStorage)))  (allocated: UCOS2_Verify_State)  (first_call: OsSchedCallContext)  (entry: UCOS2_Verify_State) ,
  “ (q_create_first_facts critical sg call initial mask cpu_sr first_call entry ) ” 
  &&  “ (event_create_allocate_critical entry allocation_result allocated ) ” 
  &&  “ (pevent = (event_create_return_ptr (sg) (allocation_result))) ”
  &&  (q_create_restore_input environment critical (q_create_allocated_owner (entry) (allocation_result)) mbox_create_call_frame sg first_call cpu_sr entry allocated )
).

Definition OSMboxCreate_which_implies_wit_5 := 
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (PreH1 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH2 : (pevent <> 0)) ,
  (mbox_create_allocation_return environment critical sg call initial mask pevent )
|--
  EX (allocation: EventPrivateAllocation)  (current: UCOS2_Verify_State)  (eid: Z) ,
  “ (pevent = (event_pool_addr (sg) (eid))) ” 
  &&  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ”
  &&  (mbox_create_initialization_context environment critical sg call initial mask eid allocation current )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (event_wait_list_init_pre &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  (mbox_create_initialization_frame pevent (eventPrivateStorage (allocation)) )
) \/
(
forall (pmsg_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (PreH1 : (mbox_create_input_facts critical sg call initial pmsg_pre X )) (PreH2 : (pevent <> 0)) ,
  (mbox_create_allocation_return environment critical sg call initial mask pevent )
|--
  EX (x_3: Z)  (x_2: Z)  (x: Z)  (allocation: EventPrivateAllocation)  (current: UCOS2_Verify_State)  (eid: Z) ,
  “ (pevent = (event_pool_addr (sg) (eid))) ” 
  &&  “ (mbox_create_input_facts critical sg call initial pmsg_pre X ) ”
  &&  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> x_3)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> x_2)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> x)
  **  (mbox_create_initialization_context environment critical sg call initial mask eid allocation current )
  **  (event_wait_list_init_pre &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  (mbox_create_initialization_frame pevent (eventPrivateStorage (allocation)) )
).

Module Type VC_Correct.


Axiom proof_of_OSMboxCreate_safety_wit_1 : OSMboxCreate_safety_wit_1.
Axiom proof_of_OSMboxCreate_safety_wit_2 : OSMboxCreate_safety_wit_2.
Axiom proof_of_OSMboxCreate_safety_wit_3 : OSMboxCreate_safety_wit_3.
Axiom proof_of_OSMboxCreate_safety_wit_4 : OSMboxCreate_safety_wit_4.
Axiom proof_of_OSMboxCreate_safety_wit_5 : OSMboxCreate_safety_wit_5.
Axiom proof_of_OSMboxCreate_entail_wit_1 : OSMboxCreate_entail_wit_1.
Axiom proof_of_OSMboxCreate_entail_wit_2 : OSMboxCreate_entail_wit_2.
Axiom proof_of_OSMboxCreate_entail_wit_3_1 : OSMboxCreate_entail_wit_3_1.
Axiom proof_of_OSMboxCreate_entail_wit_3_2 : OSMboxCreate_entail_wit_3_2.
Axiom proof_of_OSMboxCreate_entail_wit_4 : OSMboxCreate_entail_wit_4.
Axiom proof_of_OSMboxCreate_entail_wit_5 : OSMboxCreate_entail_wit_5.
Axiom proof_of_OSMboxCreate_entail_wit_6_1 : OSMboxCreate_entail_wit_6_1.
Axiom proof_of_OSMboxCreate_entail_wit_6_2 : OSMboxCreate_entail_wit_6_2.
Axiom proof_of_OSMboxCreate_return_wit_1 : OSMboxCreate_return_wit_1.
Axiom proof_of_OSMboxCreate_return_wit_2 : OSMboxCreate_return_wit_2.
Axiom proof_of_OSMboxCreate_partial_solve_wit_1 : OSMboxCreate_partial_solve_wit_1.
Axiom proof_of_OSMboxCreate_partial_solve_wit_2_pure : OSMboxCreate_partial_solve_wit_2_pure.
Axiom proof_of_OSMboxCreate_partial_solve_wit_2 : OSMboxCreate_partial_solve_wit_2.
Axiom proof_of_OSMboxCreate_partial_solve_wit_3_pure : OSMboxCreate_partial_solve_wit_3_pure.
Axiom proof_of_OSMboxCreate_partial_solve_wit_3 : OSMboxCreate_partial_solve_wit_3.
Axiom proof_of_OSMboxCreate_partial_solve_wit_4 : OSMboxCreate_partial_solve_wit_4.
Axiom proof_of_OSMboxCreate_partial_solve_wit_5 : OSMboxCreate_partial_solve_wit_5.
Axiom proof_of_OSMboxCreate_partial_solve_wit_6_pure : OSMboxCreate_partial_solve_wit_6_pure.
Axiom proof_of_OSMboxCreate_partial_solve_wit_6 : OSMboxCreate_partial_solve_wit_6.
Axiom proof_of_OSMboxCreate_partial_solve_wit_7_pure : OSMboxCreate_partial_solve_wit_7_pure.
Axiom proof_of_OSMboxCreate_partial_solve_wit_7 : OSMboxCreate_partial_solve_wit_7.
Axiom proof_of_OSMboxCreate_partial_solve_wit_8 : OSMboxCreate_partial_solve_wit_8.
Axiom proof_of_OSMboxCreate_which_implies_wit_1 : OSMboxCreate_which_implies_wit_1.
Axiom proof_of_OSMboxCreate_which_implies_wit_2 : OSMboxCreate_which_implies_wit_2.
Axiom proof_of_OSMboxCreate_which_implies_wit_3 : OSMboxCreate_which_implies_wit_3.
Axiom proof_of_OSMboxCreate_which_implies_wit_4 : OSMboxCreate_which_implies_wit_4.
Axiom proof_of_OSMboxCreate_which_implies_wit_5 : OSMboxCreate_which_implies_wit_5.

End VC_Correct.
