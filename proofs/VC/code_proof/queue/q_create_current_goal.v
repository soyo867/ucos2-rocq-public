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
Require Import Ucos2Verify.VC.code.queue.spec.q_create_proof_helpers.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.event_pool Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wait_list_init_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSQCreate -----*)

Definition OSQCreate_safety_wit_1 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((intNesting ((IntrState (initial)))) > 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (0 <= (intNesting ((IntrState (initial)))))) (PreH4 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  ((( &( "size" ) )) # UShort  |-> size_pre)
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  (q_create_call_pre environment critical sg call mask initial start_pre size_pre slots X )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQCreate_safety_wit_2 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH2 : ((intNesting ((IntrState (initial)))) <= 0)) (PreH3 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH4 : (0 <= (intNesting ((IntrState (initial)))))) (PreH5 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  (q_create_save_output environment critical QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask retval initial )
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQCreate_safety_wit_3 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH2 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) ,
  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_create_masked_control environment critical sg first_call cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  (sem_create_pool_frame sg entry )
  **  (q_create_buffer start_pre size_pre slots )
  **  ((( &( "pevent" ) )) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQCreate_safety_wit_4 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (allocation_result: (@option (Z * EventStorage))) (allocated: UCOS2_Verify_State) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (PreH1 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) (PreH2 : (event_create_allocate_critical entry allocation_result allocated )) (PreH3 : (pevent = (event_create_return_ptr (sg) (allocation_result)))) (PreH4 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  (q_create_restore_output environment critical (q_create_allocated_owner (entry) (allocation_result)) (q_create_buffer (start_pre) (size_pre) (slots)) sg first_call cpu_sr allocated )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQCreate_safety_wit_5 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (pevent: Z) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH2 : (interrupt_saved_value mask cpu_sr )) ,
  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (q_create_allocation_return environment critical sg call initial mask start_pre size_pre slots pevent )
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQCreate_safety_wit_6 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (pevent: Z) (allocation: EventPrivateAllocation) (resumed: UCOS2_Verify_State) (eid: Z) (resumed_call: OsSchedCallContext) (retval: Z) (PreH1 : (task_tcb_init_stack_same_call resumed_call call )) (PreH2 : (pevent = (event_pool_addr (sg) (eid)))) (PreH3 : (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid allocation resumed )) (PreH4 : (pevent <> 0)) (PreH5 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH6 : (interrupt_saved_value mask cpu_sr )) ,
  (q_create_save_output environment critical (QCreatePrivateEvent (eid) (allocation)) (q_create_buffer (start_pre) (size_pre) (slots)) sg resumed_call mask retval resumed )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQCreate_safety_wit_7 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (second_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (eid: Z) (allocation: EventPrivateAllocation) (free: (@list Z)) (cpu_sr: Z) (pevent: Z) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH2 : (task_tcb_init_stack_same_call second_call call )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (pevent = (event_pool_addr (sg) (eid)))) (PreH5 : (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid allocation entry )) (PreH6 : (UCOS2_state_inv sg entry )) (PreH7 : (queue_pool_partition sg (EventState (entry)) free )) (PreH8 : (q_create_private_lookup entry eid allocation )) ,
  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (q_create_masked_control environment critical sg second_call cpu_sr entry entry )
  **  (event_private_storage_rep sg eid allocation )
  **  (q_create_queue_pool_frame sg entry )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (free)))
  **  (store_free_queue_nodes sg free )
  **  (q_create_buffer start_pre size_pre slots )
  **  ((( &( "pq" ) )) # Ptr  |-> (queue_free_head (sg) (free)))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQCreate_safety_wit_8 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pq: Z) (pevent: Z) (cpu_sr: Z) (image: QCBStorage) (allocation: EventPrivateAllocation) (reserved: UCOS2_Verify_State) (qid: Z) (eid: Z) (second_call: OsSchedCallContext) (PreH1 : (task_tcb_init_stack_same_call second_call call )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (pevent = (event_pool_addr (sg) (eid)))) (PreH4 : (pq = (qcb_addr (sg) (qid)))) (PreH5 : (q_create_success_history critical sg (os_sched_call_invocation (call)) initial eid allocation qid reserved )) (PreH6 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  (q_create_restore_output environment critical (QCreatePrivateQueue (eid) (allocation) (qid) (image)) (q_create_buffer (start_pre) (size_pre) (slots)) sg second_call cpu_sr reserved )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "pq" ) )) # Ptr  |-> pq)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQCreate_safety_wit_9 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (rolled_back: UCOS2_Verify_State) (second_call: OsSchedCallContext) (PreH1 : (task_tcb_init_stack_same_call second_call call )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (q_create_error_history critical sg (os_sched_call_invocation (call)) initial rolled_back )) (PreH4 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  (q_create_restore_output environment critical QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg second_call cpu_sr rolled_back )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQCreate_safety_wit_10 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (rolled_back: UCOS2_Verify_State) (second_call: OsSchedCallContext) (PreH1 : (task_tcb_init_stack_same_call second_call call )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (q_create_error_history critical sg (os_sched_call_invocation (call)) initial rolled_back )) (PreH4 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  (q_create_restore_output environment critical QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg second_call cpu_sr rolled_back )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQCreate_entail_wit_1 := 
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH2 : ((intNesting ((IntrState (initial)))) <= 0)) (PreH3 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH4 : (0 <= (intNesting ((IntrState (initial)))))) (PreH5 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  (q_create_save_output environment critical QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask retval initial )
|--
  EX (first_call: OsSchedCallContext)  (entry: UCOS2_Verify_State) ,
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (q_create_first_facts critical sg call initial mask retval first_call entry ) ”
  &&  (q_create_masked_control environment critical sg first_call retval entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  (sem_create_pool_frame sg entry )
  **  (q_create_buffer start_pre size_pre slots )
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH2 : ((intNesting ((IntrState (initial)))) <= 0)) (PreH3 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH4 : (0 <= (intNesting ((IntrState (initial)))))) (PreH5 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  (q_create_save_output environment critical QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask retval initial )
|--
  EX (first_call: OsSchedCallContext)  (entry: UCOS2_Verify_State) ,
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (q_create_first_facts critical sg call initial mask retval first_call entry ) ”
  &&  (q_create_masked_control environment critical sg first_call retval entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  (sem_create_pool_frame sg entry )
  **  (q_create_buffer start_pre size_pre slots )
).

Definition OSQCreate_entail_wit_2 := 
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_call_2: OsSchedCallContext) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((sem_create_pool_head (sg) (entry)) <> 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (q_create_first_facts critical sg call initial mask cpu_sr first_call_2 entry )) ,
  (q_create_masked_control environment critical sg first_call_2 cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  (sem_create_pool_frame sg entry )
  **  (q_create_buffer start_pre size_pre slots )
|--
  EX (eid: Z)  (rest: (@list Z))  (image: EventStorage)  (first_call: OsSchedCallContext)  (entry_2: UCOS2_Verify_State) ,
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (q_create_first_facts critical sg call initial mask cpu_sr first_call entry_2 ) ” 
  &&  “ (sem_create_head_facts sg entry_2 eid rest image ) ” 
  &&  “ ((sem_create_pool_head (sg) (entry)) = (event_pool_addr (sg) (eid))) ”
  &&  (q_create_masked_control environment critical sg first_call cpu_sr entry_2 entry_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  ((&(((sem_create_pool_head (sg) (entry)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (sem_create_node_frame sg entry_2 eid image )
  **  (q_create_buffer start_pre size_pre slots )
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_call_2: OsSchedCallContext) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((sem_create_pool_head (sg) (entry)) <> 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (q_create_first_facts critical sg call initial mask cpu_sr first_call_2 entry )) ,
  (q_create_masked_control environment critical sg first_call_2 cpu_sr entry entry )
  **  (sem_create_pool_frame sg entry )
  **  (q_create_buffer start_pre size_pre slots )
|--
  EX (eid: Z)  (rest: (@list Z))  (image: EventStorage)  (first_call: OsSchedCallContext)  (entry_2: UCOS2_Verify_State) ,
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (q_create_first_facts critical sg call initial mask cpu_sr first_call entry_2 ) ” 
  &&  “ (sem_create_head_facts sg entry_2 eid rest image ) ” 
  &&  “ ((sem_create_pool_head (sg) (entry)) = (event_pool_addr (sg) (eid))) ”
  &&  (q_create_masked_control environment critical sg first_call cpu_sr entry_2 entry_2 )
  **  ((&(((sem_create_pool_head (sg) (entry)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (sem_create_node_frame sg entry_2 eid image )
  **  (q_create_buffer start_pre size_pre slots )
).

Definition OSQCreate_entail_wit_3_1 := 
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (cpu_sr: Z) (pevent: Z) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH2 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) (PreH3 : (sem_create_head_facts sg entry eid rest image )) (PreH4 : (pevent = (event_pool_addr (sg) (eid)))) ,
  (q_create_masked_control environment critical sg first_call cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (sem_create_node_frame sg entry eid image )
  **  (q_create_buffer start_pre size_pre slots )
|--
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ”
  &&  (q_create_allocation_cut environment critical sg call initial mask cpu_sr start_pre size_pre slots pevent )
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (cpu_sr: Z) (pevent: Z) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH2 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) (PreH3 : (sem_create_head_facts sg entry eid rest image )) (PreH4 : (pevent = (event_pool_addr (sg) (eid)))) ,
  (q_create_masked_control environment critical sg first_call cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (sem_create_node_frame sg entry eid image )
  **  (q_create_buffer start_pre size_pre slots )
|--
  (q_create_allocation_cut environment critical sg call initial mask cpu_sr start_pre size_pre slots pevent )
).

Definition OSQCreate_entail_wit_3_1_split_goal_spatial := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (eid: Z) (rest: (@list Z)) (image: EventStorage) (cpu_sr: Z) (pevent: Z) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH2 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) (PreH3 : (sem_create_head_facts sg entry eid rest image )) (PreH4 : (pevent = (event_pool_addr (sg) (eid)))) ,
  (q_create_masked_control environment critical sg first_call cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (sem_create_node_frame sg entry eid image )
  **  (q_create_buffer start_pre size_pre slots )
|--
  (q_create_allocation_cut environment critical sg call initial mask cpu_sr start_pre size_pre slots pevent )
.

Definition OSQCreate_entail_wit_3_2 := 
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((sem_create_pool_head (sg) (entry)) = 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) ,
  (q_create_masked_control environment critical sg first_call cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  (sem_create_pool_frame sg entry )
  **  (q_create_buffer start_pre size_pre slots )
|--
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ”
  &&  (q_create_allocation_cut environment critical sg call initial mask cpu_sr start_pre size_pre slots (sem_create_pool_head (sg) (entry)) )
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((sem_create_pool_head (sg) (entry)) = 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) ,
  (q_create_masked_control environment critical sg first_call cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  (sem_create_pool_frame sg entry )
  **  (q_create_buffer start_pre size_pre slots )
|--
  (q_create_allocation_cut environment critical sg call initial mask cpu_sr start_pre size_pre slots (sem_create_pool_head (sg) (entry)) )
).

Definition OSQCreate_entail_wit_3_2_split_goal_spatial := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : ((sem_create_pool_head (sg) (entry)) = 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) ,
  (q_create_masked_control environment critical sg first_call cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  (sem_create_pool_frame sg entry )
  **  (q_create_buffer start_pre size_pre slots )
|--
  (q_create_allocation_cut environment critical sg call initial mask cpu_sr start_pre size_pre slots (sem_create_pool_head (sg) (entry)) )
.

Definition OSQCreate_entail_wit_4 := 
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (allocation_result: (@option (Z * EventStorage))) (allocated: UCOS2_Verify_State) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (PreH1 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) (PreH2 : (event_create_allocate_critical entry allocation_result allocated )) (PreH3 : (pevent = (event_create_return_ptr (sg) (allocation_result)))) (PreH4 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  (q_create_restore_output environment critical (q_create_allocated_owner (entry) (allocation_result)) (q_create_buffer (start_pre) (size_pre) (slots)) sg first_call cpu_sr allocated )
|--
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  (q_create_allocation_return environment critical sg call initial mask start_pre size_pre slots pevent )
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (allocation_result: (@option (Z * EventStorage))) (allocated: UCOS2_Verify_State) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (PreH1 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) (PreH2 : (event_create_allocate_critical entry allocation_result allocated )) (PreH3 : (pevent = (event_create_return_ptr (sg) (allocation_result)))) (PreH4 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  (q_create_restore_output environment critical (q_create_allocated_owner (entry) (allocation_result)) (q_create_buffer (start_pre) (size_pre) (slots)) sg first_call cpu_sr allocated )
|--
  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  (q_create_allocation_return environment critical sg call initial mask start_pre size_pre slots pevent )
).

Definition OSQCreate_entail_wit_4_split_goal_1 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (allocation_result: (@option (Z * EventStorage))) (allocated: UCOS2_Verify_State) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (PreH1 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) (PreH2 : (event_create_allocate_critical entry allocation_result allocated )) (PreH3 : (pevent = (event_create_return_ptr (sg) (allocation_result)))) (PreH4 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  (q_create_restore_output environment critical (q_create_allocated_owner (entry) (allocation_result)) (q_create_buffer (start_pre) (size_pre) (slots)) sg first_call cpu_sr allocated )
|--
  “ (interrupt_saved_value mask cpu_sr ) ”
.

Definition OSQCreate_entail_wit_4_split_goal_spatial := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (allocation_result: (@option (Z * EventStorage))) (allocated: UCOS2_Verify_State) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (PreH1 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) (PreH2 : (event_create_allocate_critical entry allocation_result allocated )) (PreH3 : (pevent = (event_create_return_ptr (sg) (allocation_result)))) (PreH4 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  (q_create_restore_output environment critical (q_create_allocated_owner (entry) (allocation_result)) (q_create_buffer (start_pre) (size_pre) (slots)) sg first_call cpu_sr allocated )
|--
  (q_create_allocation_return environment critical sg call initial mask start_pre size_pre slots pevent )
.

Definition OSQCreate_entail_wit_5 := 
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (pevent: Z) (allocation_2: EventPrivateAllocation) (resumed: UCOS2_Verify_State) (eid_2: Z) (resumed_call: OsSchedCallContext) (retval: Z) (PreH1 : (task_tcb_init_stack_same_call resumed_call call )) (PreH2 : (pevent = (event_pool_addr (sg) (eid_2)))) (PreH3 : (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid_2 allocation_2 resumed )) (PreH4 : (pevent <> 0)) (PreH5 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH6 : (interrupt_saved_value mask cpu_sr )) ,
  (q_create_save_output environment critical (QCreatePrivateEvent (eid_2) (allocation_2)) (q_create_buffer (start_pre) (size_pre) (slots)) sg resumed_call mask retval resumed )
|--
  EX (free: (@list Z))  (allocation: EventPrivateAllocation)  (entry: UCOS2_Verify_State)  (eid: Z)  (second_call: OsSchedCallContext) ,
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (task_tcb_init_stack_same_call second_call call ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (pevent = (event_pool_addr (sg) (eid))) ” 
  &&  “ (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid allocation entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (queue_pool_partition sg (EventState (entry)) free ) ” 
  &&  “ (q_create_private_lookup entry eid allocation ) ”
  &&  (q_create_masked_control environment critical sg second_call retval entry entry )
  **  (event_private_storage_rep sg eid allocation )
  **  (q_create_queue_pool_frame sg entry )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (free)))
  **  (store_free_queue_nodes sg free )
  **  (q_create_buffer start_pre size_pre slots )
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (pevent: Z) (allocation_2: EventPrivateAllocation) (resumed: UCOS2_Verify_State) (eid_2: Z) (resumed_call: OsSchedCallContext) (retval: Z) (PreH1 : (task_tcb_init_stack_same_call resumed_call call )) (PreH2 : (pevent = (event_pool_addr (sg) (eid_2)))) (PreH3 : (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid_2 allocation_2 resumed )) (PreH4 : (pevent <> 0)) (PreH5 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH6 : (interrupt_saved_value mask cpu_sr )) ,
  (q_create_save_output environment critical (QCreatePrivateEvent (eid_2) (allocation_2)) (q_create_buffer (start_pre) (size_pre) (slots)) sg resumed_call mask retval resumed )
|--
  EX (free: (@list Z))  (allocation: EventPrivateAllocation)  (entry: UCOS2_Verify_State)  (eid: Z)  (second_call: OsSchedCallContext) ,
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (task_tcb_init_stack_same_call second_call call ) ” 
  &&  “ (interrupt_saved_value mask retval ) ” 
  &&  “ (pevent = (event_pool_addr (sg) (eid))) ” 
  &&  “ (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid allocation entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (queue_pool_partition sg (EventState (entry)) free ) ” 
  &&  “ (q_create_private_lookup entry eid allocation ) ”
  &&  (q_create_masked_control environment critical sg second_call retval entry entry )
  **  (event_private_storage_rep sg eid allocation )
  **  (q_create_queue_pool_frame sg entry )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (free)))
  **  (store_free_queue_nodes sg free )
  **  (q_create_buffer start_pre size_pre slots )
).

Definition OSQCreate_entail_wit_6 := 
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (second_call_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (eid_2: Z) (allocation_2: EventPrivateAllocation) (free: (@list Z)) (cpu_sr: Z) (pevent: Z) (PreH1 : ((queue_free_head (sg) (free)) <> 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (task_tcb_init_stack_same_call second_call_2 call )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (pevent = (event_pool_addr (sg) (eid_2)))) (PreH6 : (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid_2 allocation_2 entry_2 )) (PreH7 : (UCOS2_state_inv sg entry_2 )) (PreH8 : (queue_pool_partition sg (EventState (entry_2)) free )) (PreH9 : (q_create_private_lookup entry_2 eid_2 allocation_2 )) ,
  (q_create_masked_control environment critical sg second_call_2 cpu_sr entry_2 entry_2 )
  **  (event_private_storage_rep sg eid_2 allocation_2 )
  **  (q_create_queue_pool_frame sg entry_2 )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (free)))
  **  (store_free_queue_nodes sg free )
  **  (q_create_buffer start_pre size_pre slots )
|--
  EX (rest: (@list Z))  (allocation: EventPrivateAllocation)  (entry: UCOS2_Verify_State)  (qid: Z)  (eid: Z)  (second_call: OsSchedCallContext) ,
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (task_tcb_init_stack_same_call second_call call ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (pevent = (event_pool_addr (sg) (eid))) ” 
  &&  “ ((queue_free_head (sg) (free)) = (qcb_addr (sg) (qid))) ” 
  &&  “ (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid allocation entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (queue_pool_partition sg (EventState (entry)) (cons (qid) (rest)) ) ” 
  &&  “ (q_create_private_lookup entry eid allocation ) ”
  &&  (q_create_masked_control environment critical sg second_call cpu_sr entry entry )
  **  (event_private_storage_rep sg eid allocation )
  **  (q_create_queue_pool_frame sg entry )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (free)))
  **  ((&(((queue_free_head (sg) (free)))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (rest)))
  **  (q_create_free_qcb_without_link sg qid (queue_free_head (sg) (rest)) )
  **  (store_free_queue_nodes sg rest )
  **  (q_create_buffer start_pre size_pre slots )
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (second_call_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (eid_2: Z) (allocation_2: EventPrivateAllocation) (free: (@list Z)) (cpu_sr: Z) (pevent: Z) (PreH1 : ((queue_free_head (sg) (free)) <> 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (task_tcb_init_stack_same_call second_call_2 call )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (pevent = (event_pool_addr (sg) (eid_2)))) (PreH6 : (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid_2 allocation_2 entry_2 )) (PreH7 : (UCOS2_state_inv sg entry_2 )) (PreH8 : (queue_pool_partition sg (EventState (entry_2)) free )) (PreH9 : (q_create_private_lookup entry_2 eid_2 allocation_2 )) ,
  (q_create_masked_control environment critical sg second_call_2 cpu_sr entry_2 entry_2 )
  **  (event_private_storage_rep sg eid_2 allocation_2 )
  **  (q_create_queue_pool_frame sg entry_2 )
  **  (store_free_queue_nodes sg free )
  **  (q_create_buffer start_pre size_pre slots )
|--
  EX (rest: (@list Z))  (allocation: EventPrivateAllocation)  (entry: UCOS2_Verify_State)  (qid: Z)  (eid: Z)  (second_call: OsSchedCallContext) ,
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (task_tcb_init_stack_same_call second_call call ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (pevent = (event_pool_addr (sg) (eid))) ” 
  &&  “ ((queue_free_head (sg) (free)) = (qcb_addr (sg) (qid))) ” 
  &&  “ (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid allocation entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (queue_pool_partition sg (EventState (entry)) (cons (qid) (rest)) ) ” 
  &&  “ (q_create_private_lookup entry eid allocation ) ”
  &&  (q_create_masked_control environment critical sg second_call cpu_sr entry entry )
  **  (event_private_storage_rep sg eid allocation )
  **  (q_create_queue_pool_frame sg entry )
  **  ((&(((queue_free_head (sg) (free)))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (rest)))
  **  (q_create_free_qcb_without_link sg qid (queue_free_head (sg) (rest)) )
  **  (store_free_queue_nodes sg rest )
  **  (q_create_buffer start_pre size_pre slots )
).

Definition OSQCreate_entail_wit_7 := 
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (second_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (eid: Z) (allocation: EventPrivateAllocation) (qid: Z) (rest: (@list Z)) (cpu_sr: Z) (pevent: Z) (pq: Z) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH2 : (task_tcb_init_stack_same_call second_call call )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (pevent = (event_pool_addr (sg) (eid)))) (PreH5 : (pq = (qcb_addr (sg) (qid)))) (PreH6 : (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid allocation entry )) (PreH7 : (UCOS2_state_inv sg entry )) (PreH8 : (queue_pool_partition sg (EventState (entry)) (cons (qid) (rest)) )) (PreH9 : (q_create_private_lookup entry eid allocation )) ,
  (q_create_masked_control environment critical sg second_call cpu_sr entry entry )
  **  (event_private_storage_rep sg eid allocation )
  **  (q_create_queue_pool_frame sg entry )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (rest)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (rest)))
  **  (q_create_free_qcb_without_link sg qid (queue_free_head (sg) (rest)) )
  **  (store_free_queue_nodes sg rest )
  **  (q_create_buffer start_pre size_pre slots )
|--
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ”
  &&  (q_create_reservation_cut environment critical sg call initial mask cpu_sr start_pre size_pre slots pevent pq )
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (second_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (eid: Z) (allocation: EventPrivateAllocation) (qid: Z) (rest: (@list Z)) (cpu_sr: Z) (pevent: Z) (pq: Z) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH2 : (task_tcb_init_stack_same_call second_call call )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (pevent = (event_pool_addr (sg) (eid)))) (PreH5 : (pq = (qcb_addr (sg) (qid)))) (PreH6 : (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid allocation entry )) (PreH7 : (UCOS2_state_inv sg entry )) (PreH8 : (queue_pool_partition sg (EventState (entry)) (cons (qid) (rest)) )) (PreH9 : (q_create_private_lookup entry eid allocation )) ,
  (q_create_masked_control environment critical sg second_call cpu_sr entry entry )
  **  (event_private_storage_rep sg eid allocation )
  **  (q_create_queue_pool_frame sg entry )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (rest)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (rest)))
  **  (q_create_free_qcb_without_link sg qid (queue_free_head (sg) (rest)) )
  **  (store_free_queue_nodes sg rest )
  **  (q_create_buffer start_pre size_pre slots )
|--
  (q_create_reservation_cut environment critical sg call initial mask cpu_sr start_pre size_pre slots pevent pq )
).

Definition OSQCreate_entail_wit_7_split_goal_spatial := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (second_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (eid: Z) (allocation: EventPrivateAllocation) (qid: Z) (rest: (@list Z)) (cpu_sr: Z) (pevent: Z) (pq: Z) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH2 : (task_tcb_init_stack_same_call second_call call )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (pevent = (event_pool_addr (sg) (eid)))) (PreH5 : (pq = (qcb_addr (sg) (qid)))) (PreH6 : (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid allocation entry )) (PreH7 : (UCOS2_state_inv sg entry )) (PreH8 : (queue_pool_partition sg (EventState (entry)) (cons (qid) (rest)) )) (PreH9 : (q_create_private_lookup entry eid allocation )) ,
  (q_create_masked_control environment critical sg second_call cpu_sr entry entry )
  **  (event_private_storage_rep sg eid allocation )
  **  (q_create_queue_pool_frame sg entry )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (rest)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (rest)))
  **  (q_create_free_qcb_without_link sg qid (queue_free_head (sg) (rest)) )
  **  (store_free_queue_nodes sg rest )
  **  (q_create_buffer start_pre size_pre slots )
|--
  (q_create_reservation_cut environment critical sg call initial mask cpu_sr start_pre size_pre slots pevent pq )
.

Definition OSQCreate_entail_wit_8 := 
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pq: Z) (pevent: Z) (cpu_sr: Z) (image_2: QCBStorage) (allocation_2: EventPrivateAllocation) (reserved_2: UCOS2_Verify_State) (qid_2: Z) (eid_2: Z) (second_call: OsSchedCallContext) (PreH1 : (task_tcb_init_stack_same_call second_call call )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (pevent = (event_pool_addr (sg) (eid_2)))) (PreH4 : (pq = (qcb_addr (sg) (qid_2)))) (PreH5 : (q_create_success_history critical sg (os_sched_call_invocation (call)) initial eid_2 allocation_2 qid_2 reserved_2 )) (PreH6 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  (q_create_restore_output environment critical (QCreatePrivateQueue (eid_2) (allocation_2) (qid_2) (image_2)) (q_create_buffer (start_pre) (size_pre) (slots)) sg second_call cpu_sr reserved_2 )
|--
  EX (image: QCBStorage)  (allocation: EventPrivateAllocation)  (reserved: UCOS2_Verify_State)  (qid: Z)  (eid: Z) ,
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (pevent = (event_pool_addr (sg) (eid))) ” 
  &&  “ (pq = (qcb_addr (sg) (qid))) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (q_create_buffer_bounds start_pre size_pre ) ”
  &&  (q_create_initialization_context environment critical sg call initial mask eid allocation qid reserved start_pre size_pre slots )
  **  (q_create_qcb_link sg qid image )
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |->_)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (event_wait_list_init_pre &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  (sem_create_initialization_frame pevent (eventPrivateStorage (allocation)) )
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pq: Z) (pevent: Z) (cpu_sr: Z) (image_2: QCBStorage) (allocation_2: EventPrivateAllocation) (reserved_2: UCOS2_Verify_State) (qid_2: Z) (eid_2: Z) (second_call: OsSchedCallContext) (PreH1 : (task_tcb_init_stack_same_call second_call call )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (pevent = (event_pool_addr (sg) (eid_2)))) (PreH4 : (pq = (qcb_addr (sg) (qid_2)))) (PreH5 : (q_create_success_history critical sg (os_sched_call_invocation (call)) initial eid_2 allocation_2 qid_2 reserved_2 )) (PreH6 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  (q_create_restore_output environment critical (QCreatePrivateQueue (eid_2) (allocation_2) (qid_2) (image_2)) (q_create_buffer (start_pre) (size_pre) (slots)) sg second_call cpu_sr reserved_2 )
|--
  EX (x_9: Z)  (x_8: Z)  (x_7: Z)  (x_6: Z)  (x_5: Z)  (x_4: Z)  (x_3: Z)  (x_2: Z)  (x: Z)  (image: QCBStorage)  (allocation: EventPrivateAllocation)  (reserved: UCOS2_Verify_State)  (qid: Z)  (eid: Z) ,
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (pevent = (event_pool_addr (sg) (eid))) ” 
  &&  “ (pq = (qcb_addr (sg) (qid))) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (q_create_buffer_bounds start_pre size_pre ) ”
  &&  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> x_9)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> x_8)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> x_7)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> x_6)
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> x_5)
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> x_4)
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> x_3)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> x_2)
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> x)
  **  (q_create_initialization_context environment critical sg call initial mask eid allocation qid reserved start_pre size_pre slots )
  **  (q_create_qcb_link sg qid image )
  **  (event_wait_list_init_pre &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  (sem_create_initialization_frame pevent (eventPrivateStorage (allocation)) )
).

Definition OSQCreate_entail_wit_9 := 
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (eid: Z) (allocation: EventPrivateAllocation) (qid: Z) (reserved: UCOS2_Verify_State) (image: QCBStorage) (pevent: Z) (pq: Z) (cpu_sr: Z) (PreH1 : (q_create_buffer_bounds start_pre size_pre )) (PreH2 : (0 <= (start_pre + (size_pre * sizeof(PTR))))) (PreH3 : ((start_pre + (size_pre * sizeof(PTR))) <= UINT_MAX)) (PreH4 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH5 : (pevent = (event_pool_addr (sg) (eid)))) (PreH6 : (pq = (qcb_addr (sg) (qid)))) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (q_create_buffer_bounds start_pre size_pre )) ,
  (event_wait_list_init_post &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  ((( &( "pq" ) )) # Ptr  |-> pq)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_create_initialization_context environment critical sg call initial mask eid allocation qid reserved start_pre size_pre slots )
  **  (q_create_qcb_link sg qid image )
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> start_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (start_pre + (size_pre * sizeof(PTR))))
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> start_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> start_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> size_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 2)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pq)
  **  (sem_create_initialization_frame pevent (eventPrivateStorage (allocation)) )
|--
  (q_create_call_post environment critical sg call mask start_pre size_pre slots pevent X )
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (eid: Z) (allocation: EventPrivateAllocation) (qid: Z) (reserved: UCOS2_Verify_State) (image: QCBStorage) (pevent: Z) (pq: Z) (cpu_sr: Z) (PreH1 : (q_create_buffer_bounds start_pre size_pre )) (PreH2 : (0 <= (start_pre + (size_pre * sizeof(PTR))))) (PreH3 : ((start_pre + (size_pre * sizeof(PTR))) <= UINT_MAX)) (PreH4 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH5 : (pevent = (event_pool_addr (sg) (eid)))) (PreH6 : (pq = (qcb_addr (sg) (qid)))) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (q_create_buffer_bounds start_pre size_pre )) ,
  (event_wait_list_init_post &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  (q_create_initialization_context environment critical sg call initial mask eid allocation qid reserved start_pre size_pre slots )
  **  (q_create_qcb_link sg qid image )
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> start_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (start_pre + (size_pre * sizeof(PTR))))
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> start_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> start_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> size_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 2)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pq)
  **  (sem_create_initialization_frame pevent (eventPrivateStorage (allocation)) )
|--
  (q_create_call_post environment critical sg call mask start_pre size_pre slots pevent X )
).

Definition OSQCreate_entail_wit_9_split_goal_spatial := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (eid: Z) (allocation: EventPrivateAllocation) (qid: Z) (reserved: UCOS2_Verify_State) (image: QCBStorage) (pevent: Z) (pq: Z) (cpu_sr: Z) (PreH1 : (q_create_buffer_bounds start_pre size_pre )) (PreH2 : (0 <= (start_pre + (size_pre * sizeof(PTR))))) (PreH3 : ((start_pre + (size_pre * sizeof(PTR))) <= UINT_MAX)) (PreH4 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH5 : (pevent = (event_pool_addr (sg) (eid)))) (PreH6 : (pq = (qcb_addr (sg) (qid)))) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (q_create_buffer_bounds start_pre size_pre )) ,
  (event_wait_list_init_post &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  (q_create_initialization_context environment critical sg call initial mask eid allocation qid reserved start_pre size_pre slots )
  **  (q_create_qcb_link sg qid image )
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> start_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (start_pre + (size_pre * sizeof(PTR))))
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> start_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> start_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> size_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 2)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pq)
  **  (sem_create_initialization_frame pevent (eventPrivateStorage (allocation)) )
|--
  (q_create_call_post environment critical sg call mask start_pre size_pre slots pevent X )
.

Definition OSQCreate_entail_wit_10 := 
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (second_call_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (eid_2: Z) (allocation_2: EventPrivateAllocation) (free: (@list Z)) (cpu_sr: Z) (pevent: Z) (PreH1 : ((queue_free_head (sg) (free)) = 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (task_tcb_init_stack_same_call second_call_2 call )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (pevent = (event_pool_addr (sg) (eid_2)))) (PreH6 : (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid_2 allocation_2 entry_2 )) (PreH7 : (UCOS2_state_inv sg entry_2 )) (PreH8 : (queue_pool_partition sg (EventState (entry_2)) free )) (PreH9 : (q_create_private_lookup entry_2 eid_2 allocation_2 )) ,
  (q_create_masked_control environment critical sg second_call_2 cpu_sr entry_2 entry_2 )
  **  (event_private_storage_rep sg eid_2 allocation_2 )
  **  (q_create_queue_pool_frame sg entry_2 )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (free)))
  **  (store_free_queue_nodes sg free )
  **  (q_create_buffer start_pre size_pre slots )
|--
  EX (allocation: EventPrivateAllocation)  (entry: UCOS2_Verify_State)  (eid: Z)  (second_call: OsSchedCallContext) ,
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (task_tcb_init_stack_same_call second_call call ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ ((queue_free_head (sg) (free)) = 0) ” 
  &&  “ (pevent = (event_pool_addr (sg) (eid))) ” 
  &&  “ (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid allocation entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (queue_pool_partition sg (EventState (entry)) (@nil Z) ) ” 
  &&  “ (q_create_private_lookup entry eid allocation ) ”
  &&  (q_create_masked_control environment critical sg second_call cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (q_create_rollback_frame sg entry eid allocation )
  **  (q_create_buffer start_pre size_pre slots )
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (second_call_2: OsSchedCallContext) (entry_2: UCOS2_Verify_State) (eid_2: Z) (allocation_2: EventPrivateAllocation) (free: (@list Z)) (cpu_sr: Z) (pevent: Z) (PreH1 : ((queue_free_head (sg) (free)) = 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (task_tcb_init_stack_same_call second_call_2 call )) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (pevent = (event_pool_addr (sg) (eid_2)))) (PreH6 : (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid_2 allocation_2 entry_2 )) (PreH7 : (UCOS2_state_inv sg entry_2 )) (PreH8 : (queue_pool_partition sg (EventState (entry_2)) free )) (PreH9 : (q_create_private_lookup entry_2 eid_2 allocation_2 )) ,
  (q_create_masked_control environment critical sg second_call_2 cpu_sr entry_2 entry_2 )
  **  (event_private_storage_rep sg eid_2 allocation_2 )
  **  (q_create_queue_pool_frame sg entry_2 )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (free)))
  **  (store_free_queue_nodes sg free )
  **  (q_create_buffer start_pre size_pre slots )
|--
  EX (x: Z)  (allocation: EventPrivateAllocation)  (entry: UCOS2_Verify_State)  (eid: Z)  (second_call: OsSchedCallContext) ,
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (task_tcb_init_stack_same_call second_call call ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ ((queue_free_head (sg) (free)) = 0) ” 
  &&  “ (pevent = (event_pool_addr (sg) (eid))) ” 
  &&  “ (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid allocation entry ) ” 
  &&  “ (UCOS2_state_inv sg entry ) ” 
  &&  “ (queue_pool_partition sg (EventState (entry)) (@nil Z) ) ” 
  &&  “ (q_create_private_lookup entry eid allocation ) ”
  &&  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> x)
  **  (q_create_masked_control environment critical sg second_call cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  (q_create_rollback_frame sg entry eid allocation )
  **  (q_create_buffer start_pre size_pre slots )
).

Definition OSQCreate_entail_wit_11 := 
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (second_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (eid: Z) (allocation: EventPrivateAllocation) (cpu_sr: Z) (pq: Z) (pevent: Z) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH2 : (task_tcb_init_stack_same_call second_call call )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (pq = 0)) (PreH5 : (pevent = (event_pool_addr (sg) (eid)))) (PreH6 : (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid allocation entry )) (PreH7 : (UCOS2_state_inv sg entry )) (PreH8 : (queue_pool_partition sg (EventState (entry)) (@nil Z) )) (PreH9 : (q_create_private_lookup entry eid allocation )) ,
  ((( &( "pq" ) )) # Ptr  |-> pq)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (q_create_masked_control environment critical sg second_call cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pevent)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  (q_create_rollback_frame sg entry eid allocation )
  **  (q_create_buffer start_pre size_pre slots )
|--
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ”
  &&  (q_create_rollback_cut environment critical sg call initial mask cpu_sr start_pre size_pre slots )
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (second_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (eid: Z) (allocation: EventPrivateAllocation) (cpu_sr: Z) (pq: Z) (pevent: Z) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH2 : (task_tcb_init_stack_same_call second_call call )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (pq = 0)) (PreH5 : (pevent = (event_pool_addr (sg) (eid)))) (PreH6 : (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid allocation entry )) (PreH7 : (UCOS2_state_inv sg entry )) (PreH8 : (queue_pool_partition sg (EventState (entry)) (@nil Z) )) (PreH9 : (q_create_private_lookup entry eid allocation )) ,
  (q_create_masked_control environment critical sg second_call cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pevent)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  (q_create_rollback_frame sg entry eid allocation )
  **  (q_create_buffer start_pre size_pre slots )
|--
  (q_create_rollback_cut environment critical sg call initial mask cpu_sr start_pre size_pre slots )
).

Definition OSQCreate_entail_wit_11_split_goal_spatial := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (second_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (eid: Z) (allocation: EventPrivateAllocation) (cpu_sr: Z) (pq: Z) (pevent: Z) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH2 : (task_tcb_init_stack_same_call second_call call )) (PreH3 : (interrupt_saved_value mask cpu_sr )) (PreH4 : (pq = 0)) (PreH5 : (pevent = (event_pool_addr (sg) (eid)))) (PreH6 : (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid allocation entry )) (PreH7 : (UCOS2_state_inv sg entry )) (PreH8 : (queue_pool_partition sg (EventState (entry)) (@nil Z) )) (PreH9 : (q_create_private_lookup entry eid allocation )) ,
  (q_create_masked_control environment critical sg second_call cpu_sr entry entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pevent)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (sem_create_pool_head (sg) (entry)))
  **  (q_create_rollback_frame sg entry eid allocation )
  **  (q_create_buffer start_pre size_pre slots )
|--
  (q_create_rollback_cut environment critical sg call initial mask cpu_sr start_pre size_pre slots )
.

Definition OSQCreate_entail_wit_12 := 
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (rolled_back: UCOS2_Verify_State) (second_call: OsSchedCallContext) (PreH1 : (task_tcb_init_stack_same_call second_call call )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (q_create_error_history critical sg (os_sched_call_invocation (call)) initial rolled_back )) (PreH4 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  (q_create_restore_output environment critical QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg second_call cpu_sr rolled_back )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
|--
  (q_create_call_post environment critical sg call mask start_pre size_pre slots 0 X )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (rolled_back: UCOS2_Verify_State) (second_call: OsSchedCallContext) (PreH1 : (task_tcb_init_stack_same_call second_call call )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (q_create_error_history critical sg (os_sched_call_invocation (call)) initial rolled_back )) (PreH4 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  (q_create_restore_output environment critical QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg second_call cpu_sr rolled_back )
|--
  (q_create_call_post environment critical sg call mask start_pre size_pre slots 0 X )
).

Definition OSQCreate_entail_wit_12_split_goal_spatial := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (rolled_back: UCOS2_Verify_State) (second_call: OsSchedCallContext) (PreH1 : (task_tcb_init_stack_same_call second_call call )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (q_create_error_history critical sg (os_sched_call_invocation (call)) initial rolled_back )) (PreH4 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  (q_create_restore_output environment critical QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg second_call cpu_sr rolled_back )
|--
  (q_create_call_post environment critical sg call mask start_pre size_pre slots 0 X )
.

Definition OSQCreate_entail_wit_13_1 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) ,
  (q_create_call_post environment critical sg call mask start_pre size_pre slots pevent X )
|--
  (q_create_call_post environment critical sg call mask start_pre size_pre slots pevent X )
.

Definition OSQCreate_entail_wit_13_2 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) ,
  (q_create_call_post environment critical sg call mask start_pre size_pre slots pevent X )
|--
  (q_create_call_post environment critical sg call mask start_pre size_pre slots pevent X )
.

Definition OSQCreate_entail_wit_13_3 := 
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (pevent: Z) (PreH1 : (pevent = 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (interrupt_saved_value mask cpu_sr )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_create_allocation_return environment critical sg call initial mask start_pre size_pre slots pevent )
|--
  (q_create_call_post environment critical sg call mask start_pre size_pre slots pevent X )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (pevent: Z) (PreH1 : (pevent = 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (interrupt_saved_value mask cpu_sr )) ,
  (q_create_allocation_return environment critical sg call initial mask start_pre size_pre slots pevent )
|--
  (q_create_call_post environment critical sg call mask start_pre size_pre slots pevent X )
).

Definition OSQCreate_entail_wit_13_3_split_goal_spatial := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (pevent: Z) (PreH1 : (pevent = 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (interrupt_saved_value mask cpu_sr )) ,
  (q_create_allocation_return environment critical sg call initial mask start_pre size_pre slots pevent )
|--
  (q_create_call_post environment critical sg call mask start_pre size_pre slots pevent X )
.

Definition OSQCreate_return_wit_1 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) ,
  (q_create_call_post environment critical sg call mask start_pre size_pre slots pevent X )
|--
  (q_create_call_post environment critical sg call mask start_pre size_pre slots pevent X )
.

Definition OSQCreate_return_wit_2 := 
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((intNesting ((IntrState (initial)))) > 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (0 <= (intNesting ((IntrState (initial)))))) (PreH4 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  (q_create_call_pre environment critical sg call mask initial start_pre size_pre slots X )
|--
  (q_create_call_post environment critical sg call mask start_pre size_pre slots 0 X )
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((intNesting ((IntrState (initial)))) > 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (0 <= (intNesting ((IntrState (initial)))))) (PreH4 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  (q_create_call_pre environment critical sg call mask initial start_pre size_pre slots X )
|--
  (q_create_call_post environment critical sg call mask start_pre size_pre slots 0 X )
).

Definition OSQCreate_return_wit_2_split_goal_spatial := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((intNesting ((IntrState (initial)))) > 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (0 <= (intNesting ((IntrState (initial)))))) (PreH4 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  (q_create_call_pre environment critical sg call mask initial start_pre size_pre slots X )
|--
  (q_create_call_post environment critical sg call mask start_pre size_pre slots 0 X )
.

Definition OSQCreate_partial_solve_wit_1 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) ,
  (q_create_call_pre environment critical sg call mask initial start_pre size_pre slots X )
|--
  (q_create_call_pre environment critical sg call mask initial start_pre size_pre slots X )
.

Definition OSQCreate_partial_solve_wit_2_pure := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((intNesting ((IntrState (initial)))) > 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (0 <= (intNesting ((IntrState (initial)))))) (PreH4 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask initial )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
|--
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ”
.

Definition OSQCreate_partial_solve_wit_2_aux := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((intNesting ((IntrState (initial)))) > 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (0 <= (intNesting ((IntrState (initial)))))) (PreH4 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask initial )
|--
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ ((intNesting ((IntrState (initial)))) > 0) ” 
  &&  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (0 <= (intNesting ((IntrState (initial))))) ” 
  &&  “ ((intNesting ((IntrState (initial)))) <= 255) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask initial )
.

Definition OSQCreate_partial_solve_wit_2 := OSQCreate_partial_solve_wit_2_pure -> OSQCreate_partial_solve_wit_2_aux.

Definition OSQCreate_partial_solve_wit_3_pure := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((intNesting ((IntrState (initial)))) <= 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (0 <= (intNesting ((IntrState (initial)))))) (PreH4 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask initial )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
|--
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ”
.

Definition OSQCreate_partial_solve_wit_3_aux := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((intNesting ((IntrState (initial)))) <= 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (0 <= (intNesting ((IntrState (initial)))))) (PreH4 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask initial )
|--
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ ((intNesting ((IntrState (initial)))) <= 0) ” 
  &&  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (0 <= (intNesting ((IntrState (initial))))) ” 
  &&  “ ((intNesting ((IntrState (initial)))) <= 255) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask initial )
.

Definition OSQCreate_partial_solve_wit_3 := OSQCreate_partial_solve_wit_3_pure -> OSQCreate_partial_solve_wit_3_aux.

Definition OSQCreate_partial_solve_wit_4 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH2 : ((intNesting ((IntrState (initial)))) <= 0)) (PreH3 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH4 : (0 <= (intNesting ((IntrState (initial)))))) (PreH5 : ((intNesting ((IntrState (initial)))) <= 255)) ,
  (q_create_save_input environment critical QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask initial )
|--
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ ((intNesting ((IntrState (initial)))) <= 0) ” 
  &&  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (0 <= (intNesting ((IntrState (initial))))) ” 
  &&  “ ((intNesting ((IntrState (initial)))) <= 255) ”
  &&  (q_create_save_input environment critical QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask initial )
.

Definition OSQCreate_partial_solve_wit_5 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  (q_create_allocation_cut environment critical sg call initial mask cpu_sr start_pre size_pre slots pevent )
|--
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ”
  &&  (q_create_allocation_cut environment critical sg call initial mask cpu_sr start_pre size_pre slots pevent )
.

Definition OSQCreate_partial_solve_wit_6_pure := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (allocation_result: (@option (Z * EventStorage))) (allocated: UCOS2_Verify_State) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (PreH1 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) (PreH2 : (event_create_allocate_critical entry allocation_result allocated )) (PreH3 : (pevent = (event_create_return_ptr (sg) (allocation_result)))) (PreH4 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  (q_create_restore_input environment critical (q_create_allocated_owner (entry) (allocation_result)) (q_create_buffer (start_pre) (size_pre) (slots)) sg first_call cpu_sr entry allocated )
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSQCreate_partial_solve_wit_6_aux := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (allocation_result: (@option (Z * EventStorage))) (allocated: UCOS2_Verify_State) (first_call: OsSchedCallContext) (entry: UCOS2_Verify_State) (PreH1 : (q_create_first_facts critical sg call initial mask cpu_sr first_call entry )) (PreH2 : (event_create_allocate_critical entry allocation_result allocated )) (PreH3 : (pevent = (event_create_return_ptr (sg) (allocation_result)))) (PreH4 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  (q_create_restore_input environment critical (q_create_allocated_owner (entry) (allocation_result)) (q_create_buffer (start_pre) (size_pre) (slots)) sg first_call cpu_sr entry allocated )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (q_create_first_facts critical sg call initial mask cpu_sr first_call entry ) ” 
  &&  “ (event_create_allocate_critical entry allocation_result allocated ) ” 
  &&  “ (pevent = (event_create_return_ptr (sg) (allocation_result))) ” 
  &&  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ”
  &&  (q_create_restore_input environment critical (q_create_allocated_owner (entry) (allocation_result)) (q_create_buffer (start_pre) (size_pre) (slots)) sg first_call cpu_sr entry allocated )
.

Definition OSQCreate_partial_solve_wit_6 := OSQCreate_partial_solve_wit_6_pure -> OSQCreate_partial_solve_wit_6_aux.

Definition OSQCreate_partial_solve_wit_7_pure := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (pevent: Z) (PreH1 : (pevent <> 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (interrupt_saved_value mask cpu_sr )) ,
  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (q_create_allocation_return environment critical sg call initial mask start_pre size_pre slots pevent )
  **  ((( &( "pq" ) )) # Ptr  |->_)
|--
  “ (pevent <> 0) ”
.

Definition OSQCreate_partial_solve_wit_7_aux := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (pevent: Z) (PreH1 : (pevent <> 0)) (PreH2 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH3 : (interrupt_saved_value mask cpu_sr )) ,
  (q_create_allocation_return environment critical sg call initial mask start_pre size_pre slots pevent )
|--
  “ (pevent <> 0) ” 
  &&  “ (pevent <> 0) ” 
  &&  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  (q_create_allocation_return environment critical sg call initial mask start_pre size_pre slots pevent )
.

Definition OSQCreate_partial_solve_wit_7 := OSQCreate_partial_solve_wit_7_pure -> OSQCreate_partial_solve_wit_7_aux.

Definition OSQCreate_partial_solve_wit_8 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (pevent: Z) (allocation: EventPrivateAllocation) (resumed: UCOS2_Verify_State) (eid: Z) (resumed_call: OsSchedCallContext) (PreH1 : (task_tcb_init_stack_same_call resumed_call call )) (PreH2 : (pevent = (event_pool_addr (sg) (eid)))) (PreH3 : (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid allocation resumed )) (PreH4 : (pevent <> 0)) (PreH5 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH6 : (interrupt_saved_value mask cpu_sr )) ,
  (q_create_save_input environment critical (QCreatePrivateEvent (eid) (allocation)) (q_create_buffer (start_pre) (size_pre) (slots)) sg resumed_call mask resumed )
|--
  “ (task_tcb_init_stack_same_call resumed_call call ) ” 
  &&  “ (pevent = (event_pool_addr (sg) (eid))) ” 
  &&  “ (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid allocation resumed ) ” 
  &&  “ (pevent <> 0) ” 
  &&  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ”
  &&  (q_create_save_input environment critical (QCreatePrivateEvent (eid) (allocation)) (q_create_buffer (start_pre) (size_pre) (slots)) sg resumed_call mask resumed )
.

Definition OSQCreate_partial_solve_wit_9 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pq: Z) (pevent: Z) (cpu_sr: Z) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  (q_create_reservation_cut environment critical sg call initial mask cpu_sr start_pre size_pre slots pevent pq )
|--
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ”
  &&  (q_create_reservation_cut environment critical sg call initial mask cpu_sr start_pre size_pre slots pevent pq )
.

Definition OSQCreate_partial_solve_wit_10_pure := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pq: Z) (pevent: Z) (cpu_sr: Z) (image: QCBStorage) (acquired: UCOS2_Verify_State) (allocation: EventPrivateAllocation) (reserved: UCOS2_Verify_State) (qid: Z) (eid: Z) (second_call: OsSchedCallContext) (PreH1 : (task_tcb_init_stack_same_call second_call call )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (pevent = (event_pool_addr (sg) (eid)))) (PreH4 : (pq = (qcb_addr (sg) (qid)))) (PreH5 : (q_create_success_history critical sg (os_sched_call_invocation (call)) initial eid allocation qid reserved )) (PreH6 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "pq" ) )) # Ptr  |-> pq)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  (q_create_restore_input environment critical (QCreatePrivateQueue (eid) (allocation) (qid) (image)) (q_create_buffer (start_pre) (size_pre) (slots)) sg second_call cpu_sr acquired reserved )
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSQCreate_partial_solve_wit_10_aux := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pq: Z) (pevent: Z) (cpu_sr: Z) (image: QCBStorage) (acquired: UCOS2_Verify_State) (allocation: EventPrivateAllocation) (reserved: UCOS2_Verify_State) (qid: Z) (eid: Z) (second_call: OsSchedCallContext) (PreH1 : (task_tcb_init_stack_same_call second_call call )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (pevent = (event_pool_addr (sg) (eid)))) (PreH4 : (pq = (qcb_addr (sg) (qid)))) (PreH5 : (q_create_success_history critical sg (os_sched_call_invocation (call)) initial eid allocation qid reserved )) (PreH6 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  (q_create_restore_input environment critical (QCreatePrivateQueue (eid) (allocation) (qid) (image)) (q_create_buffer (start_pre) (size_pre) (slots)) sg second_call cpu_sr acquired reserved )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (task_tcb_init_stack_same_call second_call call ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (pevent = (event_pool_addr (sg) (eid))) ” 
  &&  “ (pq = (qcb_addr (sg) (qid))) ” 
  &&  “ (q_create_success_history critical sg (os_sched_call_invocation (call)) initial eid allocation qid reserved ) ” 
  &&  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ”
  &&  (q_create_restore_input environment critical (QCreatePrivateQueue (eid) (allocation) (qid) (image)) (q_create_buffer (start_pre) (size_pre) (slots)) sg second_call cpu_sr acquired reserved )
.

Definition OSQCreate_partial_solve_wit_10 := OSQCreate_partial_solve_wit_10_pure -> OSQCreate_partial_solve_wit_10_aux.

Definition OSQCreate_partial_solve_wit_11_pure := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (eid: Z) (allocation: EventPrivateAllocation) (qid: Z) (reserved: UCOS2_Verify_State) (image: QCBStorage) (pevent: Z) (pq: Z) (cpu_sr: Z) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH2 : (pevent = (event_pool_addr (sg) (eid)))) (PreH3 : (pq = (qcb_addr (sg) (qid)))) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (q_create_buffer_bounds start_pre size_pre )) ,
  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "pq" ) )) # Ptr  |-> pq)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_create_initialization_context environment critical sg call initial mask eid allocation qid reserved start_pre size_pre slots )
  **  (q_create_qcb_link sg qid image )
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> start_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |->_)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (event_wait_list_init_pre &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  (sem_create_initialization_frame pevent (eventPrivateStorage (allocation)) )
|--
  “ (q_create_buffer_bounds start_pre size_pre ) ”
.

Definition OSQCreate_partial_solve_wit_11_aux := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (eid: Z) (allocation: EventPrivateAllocation) (qid: Z) (reserved: UCOS2_Verify_State) (image: QCBStorage) (pevent: Z) (pq: Z) (cpu_sr: Z) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH2 : (pevent = (event_pool_addr (sg) (eid)))) (PreH3 : (pq = (qcb_addr (sg) (qid)))) (PreH4 : (interrupt_saved_value mask cpu_sr )) (PreH5 : (q_create_buffer_bounds start_pre size_pre )) ,
  (q_create_initialization_context environment critical sg call initial mask eid allocation qid reserved start_pre size_pre slots )
  **  (q_create_qcb_link sg qid image )
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> start_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |->_)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (event_wait_list_init_pre &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  (sem_create_initialization_frame pevent (eventPrivateStorage (allocation)) )
|--
  “ (q_create_buffer_bounds start_pre size_pre ) ” 
  &&  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (pevent = (event_pool_addr (sg) (eid))) ” 
  &&  “ (pq = (qcb_addr (sg) (qid))) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (q_create_buffer_bounds start_pre size_pre ) ”
  &&  (q_create_initialization_context environment critical sg call initial mask eid allocation qid reserved start_pre size_pre slots )
  **  (q_create_qcb_link sg qid image )
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> start_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |->_)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (event_wait_list_init_pre &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  (sem_create_initialization_frame pevent (eventPrivateStorage (allocation)) )
.

Definition OSQCreate_partial_solve_wit_11 := OSQCreate_partial_solve_wit_11_pure -> OSQCreate_partial_solve_wit_11_aux.

Definition OSQCreate_partial_solve_wit_12 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (eid: Z) (allocation: EventPrivateAllocation) (qid: Z) (reserved: UCOS2_Verify_State) (image: QCBStorage) (pevent: Z) (pq: Z) (cpu_sr: Z) (PreH1 : (q_create_buffer_bounds start_pre size_pre )) (PreH2 : (0 <= (start_pre + (size_pre * sizeof(PTR))))) (PreH3 : ((start_pre + (size_pre * sizeof(PTR))) <= UINT_MAX)) (PreH4 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) (PreH5 : (pevent = (event_pool_addr (sg) (eid)))) (PreH6 : (pq = (qcb_addr (sg) (qid)))) (PreH7 : (interrupt_saved_value mask cpu_sr )) (PreH8 : (q_create_buffer_bounds start_pre size_pre )) ,
  (q_create_initialization_context environment critical sg call initial mask eid allocation qid reserved start_pre size_pre slots )
  **  (q_create_qcb_link sg qid image )
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> start_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (start_pre + (size_pre * sizeof(PTR))))
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> start_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> start_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> size_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 2)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pq)
  **  (event_wait_list_init_pre &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  (sem_create_initialization_frame pevent (eventPrivateStorage (allocation)) )
|--
  “ (q_create_buffer_bounds start_pre size_pre ) ” 
  &&  “ (0 <= (start_pre + (size_pre * sizeof(PTR)))) ” 
  &&  “ ((start_pre + (size_pre * sizeof(PTR))) <= UINT_MAX) ” 
  &&  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (pevent = (event_pool_addr (sg) (eid))) ” 
  &&  “ (pq = (qcb_addr (sg) (qid))) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (q_create_buffer_bounds start_pre size_pre ) ”
  &&  (event_wait_list_init_pre &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
  **  (q_create_initialization_context environment critical sg call initial mask eid allocation qid reserved start_pre size_pre slots )
  **  (q_create_qcb_link sg qid image )
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> start_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (start_pre + (size_pre * sizeof(PTR))))
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> start_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> start_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> size_pre)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 2)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pq)
  **  (sem_create_initialization_frame pevent (eventPrivateStorage (allocation)) )
.

Definition OSQCreate_partial_solve_wit_13 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  (q_create_rollback_cut environment critical sg call initial mask cpu_sr start_pre size_pre slots )
|--
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ”
  &&  (q_create_rollback_cut environment critical sg call initial mask cpu_sr start_pre size_pre slots )
.

Definition OSQCreate_partial_solve_wit_14_pure := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (rolled_back: UCOS2_Verify_State) (second_call: OsSchedCallContext) (PreH1 : (task_tcb_init_stack_same_call second_call call )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (q_create_error_history critical sg (os_sched_call_invocation (call)) initial rolled_back )) (PreH4 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  (q_create_restore_input environment critical QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg second_call cpu_sr acquired rolled_back )
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSQCreate_partial_solve_wit_14_aux := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (rolled_back: UCOS2_Verify_State) (second_call: OsSchedCallContext) (PreH1 : (task_tcb_init_stack_same_call second_call call )) (PreH2 : (interrupt_saved_value mask cpu_sr )) (PreH3 : (q_create_error_history critical sg (os_sched_call_invocation (call)) initial rolled_back )) (PreH4 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  (q_create_restore_input environment critical QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg second_call cpu_sr acquired rolled_back )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (task_tcb_init_stack_same_call second_call call ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (q_create_error_history critical sg (os_sched_call_invocation (call)) initial rolled_back ) ” 
  &&  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ”
  &&  (q_create_restore_input environment critical QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg second_call cpu_sr acquired rolled_back )
.

Definition OSQCreate_partial_solve_wit_14 := OSQCreate_partial_solve_wit_14_pure -> OSQCreate_partial_solve_wit_14_aux.

Definition OSQCreate_which_implies_wit_1 := 
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) ,
  (q_create_call_pre environment critical sg call mask initial start_pre size_pre slots X )
|--
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ” 
  &&  “ (0 <= (intNesting ((IntrState (initial))))) ” 
  &&  “ ((intNesting ((IntrState (initial)))) <= 255) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask initial )
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) ,
  (q_create_call_pre environment critical sg call mask initial start_pre size_pre slots X )
|--
  “ ((intNesting ((IntrState (initial)))) <= 255) ” 
  &&  “ (0 <= (intNesting ((IntrState (initial))))) ” 
  &&  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask initial )
).

Definition OSQCreate_which_implies_wit_1_split_goal_1 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) ,
  (q_create_call_pre environment critical sg call mask initial start_pre size_pre slots X )
|--
  “ ((intNesting ((IntrState (initial)))) <= 255) ”
.

Definition OSQCreate_which_implies_wit_1_split_goal_2 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) ,
  (q_create_call_pre environment critical sg call mask initial start_pre size_pre slots X )
|--
  “ (0 <= (intNesting ((IntrState (initial))))) ”
.

Definition OSQCreate_which_implies_wit_1_split_goal_3 := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) ,
  (q_create_call_pre environment critical sg call mask initial start_pre size_pre slots X )
|--
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ”
.

Definition OSQCreate_which_implies_wit_1_split_goal_spatial := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) ,
  (q_create_call_pre environment critical sg call mask initial start_pre size_pre slots X )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask initial )
.

Definition OSQCreate_which_implies_wit_2 := 
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask initial )
|--
  (q_create_call_pre environment critical sg call mask initial start_pre size_pre slots X )
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask initial )
|--
  (q_create_call_pre environment critical sg call mask initial start_pre size_pre slots X )
).

Definition OSQCreate_which_implies_wit_2_split_goal_spatial := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask initial )
|--
  (q_create_call_pre environment critical sg call mask initial start_pre size_pre slots X )
.

Definition OSQCreate_which_implies_wit_3 := 
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask initial )
|--
  “ (q_create_input_facts critical sg call initial start_pre size_pre slots X ) ”
  &&  (q_create_save_input environment critical QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask initial )
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask initial )
|--
  (q_create_save_input environment critical QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask initial )
).

Definition OSQCreate_which_implies_wit_3_split_goal_spatial := 
forall (size_pre: Z) (start_pre: Z) (X: (Z -> (UCOS2_Verify_State -> Prop))) (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (q_create_input_facts critical sg call initial start_pre size_pre slots X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((IntrState (initial)))))
  **  (q_create_without_nesting environment QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask initial )
|--
  (q_create_save_input environment critical QCreateNoPrivate (q_create_buffer (start_pre) (size_pre) (slots)) sg call mask initial )
.

Definition OSQCreate_which_implies_wit_4 := 
(
forall (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (size: Z) (start: Z) (cpu_sr: Z) ,
  (q_create_allocation_cut environment critical sg call initial mask cpu_sr start size slots pevent )
|--
  EX (allocation_result: (@option (Z * EventStorage)))  (allocated: UCOS2_Verify_State)  (first_call: OsSchedCallContext)  (entry: UCOS2_Verify_State) ,
  “ (q_create_first_facts critical sg call initial mask cpu_sr first_call entry ) ” 
  &&  “ (event_create_allocate_critical entry allocation_result allocated ) ” 
  &&  “ (pevent = (event_create_return_ptr (sg) (allocation_result))) ”
  &&  (q_create_restore_input environment critical (q_create_allocated_owner (entry) (allocation_result)) (q_create_buffer (start) (size) (slots)) sg first_call cpu_sr entry allocated )
) \/
(
forall (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (size: Z) (start: Z) (cpu_sr: Z) ,
  (q_create_allocation_cut environment critical sg call initial mask cpu_sr start size slots pevent )
|--
  EX (allocation_result: (@option (Z * EventStorage)))  (allocated: UCOS2_Verify_State)  (first_call: OsSchedCallContext)  (entry: UCOS2_Verify_State) ,
  “ (q_create_first_facts critical sg call initial mask cpu_sr first_call entry ) ” 
  &&  “ (event_create_allocate_critical entry allocation_result allocated ) ” 
  &&  “ (pevent = (event_create_return_ptr (sg) (allocation_result))) ”
  &&  (q_create_restore_input environment critical (q_create_allocated_owner (entry) (allocation_result)) (q_create_buffer (start) (size) (slots)) sg first_call cpu_sr entry allocated )
).

Definition OSQCreate_which_implies_wit_5 := 
(
forall (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (size: Z) (start: Z) (PreH1 : (pevent <> 0)) ,
  (q_create_allocation_return environment critical sg call initial mask start size slots pevent )
|--
  EX (allocation: EventPrivateAllocation)  (resumed: UCOS2_Verify_State)  (eid: Z)  (resumed_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call resumed_call call ) ” 
  &&  “ (pevent = (event_pool_addr (sg) (eid))) ” 
  &&  “ (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid allocation resumed ) ”
  &&  (q_create_save_input environment critical (QCreatePrivateEvent (eid) (allocation)) (q_create_buffer (start) (size) (slots)) sg resumed_call mask resumed )
) \/
(
forall (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pevent: Z) (size: Z) (start: Z) (PreH1 : (pevent <> 0)) ,
  (q_create_allocation_return environment critical sg call initial mask start size slots pevent )
|--
  EX (allocation: EventPrivateAllocation)  (resumed: UCOS2_Verify_State)  (eid: Z)  (resumed_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call resumed_call call ) ” 
  &&  “ (pevent = (event_pool_addr (sg) (eid))) ” 
  &&  “ (q_create_event_history critical sg (os_sched_call_invocation (call)) initial eid allocation resumed ) ”
  &&  (q_create_save_input environment critical (QCreatePrivateEvent (eid) (allocation)) (q_create_buffer (start) (size) (slots)) sg resumed_call mask resumed )
).

Definition OSQCreate_which_implies_wit_6 := 
(
forall (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pq: Z) (pevent: Z) (size: Z) (start: Z) (cpu_sr: Z) ,
  (q_create_reservation_cut environment critical sg call initial mask cpu_sr start size slots pevent pq )
|--
  EX (image: QCBStorage)  (acquired: UCOS2_Verify_State)  (allocation: EventPrivateAllocation)  (reserved: UCOS2_Verify_State)  (qid: Z)  (eid: Z)  (second_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call second_call call ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (pevent = (event_pool_addr (sg) (eid))) ” 
  &&  “ (pq = (qcb_addr (sg) (qid))) ” 
  &&  “ (q_create_success_history critical sg (os_sched_call_invocation (call)) initial eid allocation qid reserved ) ”
  &&  (q_create_restore_input environment critical (QCreatePrivateQueue (eid) (allocation) (qid) (image)) (q_create_buffer (start) (size) (slots)) sg second_call cpu_sr acquired reserved )
) \/
(
forall (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (pq: Z) (pevent: Z) (size: Z) (start: Z) (cpu_sr: Z) ,
  (q_create_reservation_cut environment critical sg call initial mask cpu_sr start size slots pevent pq )
|--
  EX (image: QCBStorage)  (acquired: UCOS2_Verify_State)  (allocation: EventPrivateAllocation)  (reserved: UCOS2_Verify_State)  (qid: Z)  (eid: Z)  (second_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call second_call call ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (pevent = (event_pool_addr (sg) (eid))) ” 
  &&  “ (pq = (qcb_addr (sg) (qid))) ” 
  &&  “ (q_create_success_history critical sg (os_sched_call_invocation (call)) initial eid allocation qid reserved ) ”
  &&  (q_create_restore_input environment critical (QCreatePrivateQueue (eid) (allocation) (qid) (image)) (q_create_buffer (start) (size) (slots)) sg second_call cpu_sr acquired reserved )
).

Definition OSQCreate_which_implies_wit_7 := 
(
forall (size: Z) (start: Z) (PreH1 : (q_create_buffer_bounds start size )) ,
  TT && emp 
|--
  “ (q_create_buffer_bounds start size ) ” 
  &&  “ (0 <= (start + (size * sizeof(PTR)))) ” 
  &&  “ ((start + (size * sizeof(PTR))) <= UINT_MAX) ”
  &&  emp
) \/
(
forall (size: Z) (start: Z) (PreH1 : (q_create_buffer_bounds start size )) ,
  TT && emp 
|--
  “ ((start + (size * sizeof(PTR))) <= UINT_MAX) ” 
  &&  “ (0 <= (start + (size * sizeof(PTR)))) ”
  &&  emp
).

Definition OSQCreate_which_implies_wit_7_split_goal_1 := 
forall (size: Z) (start: Z) (PreH1 : (q_create_buffer_bounds start size )) ,
  ((start + (size * sizeof(PTR))) <= UINT_MAX)
.

Definition OSQCreate_which_implies_wit_7_split_goal_2 := 
forall (size: Z) (start: Z) (PreH1 : (q_create_buffer_bounds start size )) ,
  (0 <= (start + (size * sizeof(PTR))))
.

Definition OSQCreate_which_implies_wit_8 := 
(
forall (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (size: Z) (start: Z) (cpu_sr: Z) ,
  (q_create_rollback_cut environment critical sg call initial mask cpu_sr start size slots )
|--
  EX (acquired: UCOS2_Verify_State)  (rolled_back: UCOS2_Verify_State)  (second_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call second_call call ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (q_create_error_history critical sg (os_sched_call_invocation (call)) initial rolled_back ) ”
  &&  (q_create_restore_input environment critical QCreateNoPrivate (q_create_buffer (start) (size) (slots)) sg second_call cpu_sr acquired rolled_back )
) \/
(
forall (slots: (@list (@option Z))) (initial: UCOS2_Verify_State) (mask: Z) (call: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (size: Z) (start: Z) (cpu_sr: Z) ,
  (q_create_rollback_cut environment critical sg call initial mask cpu_sr start size slots )
|--
  EX (acquired: UCOS2_Verify_State)  (rolled_back: UCOS2_Verify_State)  (second_call: OsSchedCallContext) ,
  “ (task_tcb_init_stack_same_call second_call call ) ” 
  &&  “ (interrupt_saved_value mask cpu_sr ) ” 
  &&  “ (q_create_error_history critical sg (os_sched_call_invocation (call)) initial rolled_back ) ”
  &&  (q_create_restore_input environment critical QCreateNoPrivate (q_create_buffer (start) (size) (slots)) sg second_call cpu_sr acquired rolled_back )
).

Module Type VC_Correct.


Axiom proof_of_OSQCreate_safety_wit_1 : OSQCreate_safety_wit_1.
Axiom proof_of_OSQCreate_safety_wit_2 : OSQCreate_safety_wit_2.
Axiom proof_of_OSQCreate_safety_wit_3 : OSQCreate_safety_wit_3.
Axiom proof_of_OSQCreate_safety_wit_4 : OSQCreate_safety_wit_4.
Axiom proof_of_OSQCreate_safety_wit_5 : OSQCreate_safety_wit_5.
Axiom proof_of_OSQCreate_safety_wit_6 : OSQCreate_safety_wit_6.
Axiom proof_of_OSQCreate_safety_wit_7 : OSQCreate_safety_wit_7.
Axiom proof_of_OSQCreate_safety_wit_8 : OSQCreate_safety_wit_8.
Axiom proof_of_OSQCreate_safety_wit_9 : OSQCreate_safety_wit_9.
Axiom proof_of_OSQCreate_safety_wit_10 : OSQCreate_safety_wit_10.
Axiom proof_of_OSQCreate_entail_wit_1 : OSQCreate_entail_wit_1.
Axiom proof_of_OSQCreate_entail_wit_2 : OSQCreate_entail_wit_2.
Axiom proof_of_OSQCreate_entail_wit_3_1 : OSQCreate_entail_wit_3_1.
Axiom proof_of_OSQCreate_entail_wit_3_2 : OSQCreate_entail_wit_3_2.
Axiom proof_of_OSQCreate_entail_wit_4 : OSQCreate_entail_wit_4.
Axiom proof_of_OSQCreate_entail_wit_5 : OSQCreate_entail_wit_5.
Axiom proof_of_OSQCreate_entail_wit_6 : OSQCreate_entail_wit_6.
Axiom proof_of_OSQCreate_entail_wit_7 : OSQCreate_entail_wit_7.
Axiom proof_of_OSQCreate_entail_wit_8 : OSQCreate_entail_wit_8.
Axiom proof_of_OSQCreate_entail_wit_9 : OSQCreate_entail_wit_9.
Axiom proof_of_OSQCreate_entail_wit_10 : OSQCreate_entail_wit_10.
Axiom proof_of_OSQCreate_entail_wit_11 : OSQCreate_entail_wit_11.
Axiom proof_of_OSQCreate_entail_wit_12 : OSQCreate_entail_wit_12.
Axiom proof_of_OSQCreate_entail_wit_13_1 : OSQCreate_entail_wit_13_1.
Axiom proof_of_OSQCreate_entail_wit_13_2 : OSQCreate_entail_wit_13_2.
Axiom proof_of_OSQCreate_entail_wit_13_3 : OSQCreate_entail_wit_13_3.
Axiom proof_of_OSQCreate_return_wit_1 : OSQCreate_return_wit_1.
Axiom proof_of_OSQCreate_return_wit_2 : OSQCreate_return_wit_2.
Axiom proof_of_OSQCreate_partial_solve_wit_1 : OSQCreate_partial_solve_wit_1.
Axiom proof_of_OSQCreate_partial_solve_wit_2_pure : OSQCreate_partial_solve_wit_2_pure.
Axiom proof_of_OSQCreate_partial_solve_wit_2 : OSQCreate_partial_solve_wit_2.
Axiom proof_of_OSQCreate_partial_solve_wit_3_pure : OSQCreate_partial_solve_wit_3_pure.
Axiom proof_of_OSQCreate_partial_solve_wit_3 : OSQCreate_partial_solve_wit_3.
Axiom proof_of_OSQCreate_partial_solve_wit_4 : OSQCreate_partial_solve_wit_4.
Axiom proof_of_OSQCreate_partial_solve_wit_5 : OSQCreate_partial_solve_wit_5.
Axiom proof_of_OSQCreate_partial_solve_wit_6_pure : OSQCreate_partial_solve_wit_6_pure.
Axiom proof_of_OSQCreate_partial_solve_wit_6 : OSQCreate_partial_solve_wit_6.
Axiom proof_of_OSQCreate_partial_solve_wit_7_pure : OSQCreate_partial_solve_wit_7_pure.
Axiom proof_of_OSQCreate_partial_solve_wit_7 : OSQCreate_partial_solve_wit_7.
Axiom proof_of_OSQCreate_partial_solve_wit_8 : OSQCreate_partial_solve_wit_8.
Axiom proof_of_OSQCreate_partial_solve_wit_9 : OSQCreate_partial_solve_wit_9.
Axiom proof_of_OSQCreate_partial_solve_wit_10_pure : OSQCreate_partial_solve_wit_10_pure.
Axiom proof_of_OSQCreate_partial_solve_wit_10 : OSQCreate_partial_solve_wit_10.
Axiom proof_of_OSQCreate_partial_solve_wit_11_pure : OSQCreate_partial_solve_wit_11_pure.
Axiom proof_of_OSQCreate_partial_solve_wit_11 : OSQCreate_partial_solve_wit_11.
Axiom proof_of_OSQCreate_partial_solve_wit_12 : OSQCreate_partial_solve_wit_12.
Axiom proof_of_OSQCreate_partial_solve_wit_13 : OSQCreate_partial_solve_wit_13.
Axiom proof_of_OSQCreate_partial_solve_wit_14_pure : OSQCreate_partial_solve_wit_14_pure.
Axiom proof_of_OSQCreate_partial_solve_wit_14 : OSQCreate_partial_solve_wit_14.
Axiom proof_of_OSQCreate_which_implies_wit_1 : OSQCreate_which_implies_wit_1.
Axiom proof_of_OSQCreate_which_implies_wit_2 : OSQCreate_which_implies_wit_2.
Axiom proof_of_OSQCreate_which_implies_wit_3 : OSQCreate_which_implies_wit_3.
Axiom proof_of_OSQCreate_which_implies_wit_4 : OSQCreate_which_implies_wit_4.
Axiom proof_of_OSQCreate_which_implies_wit_5 : OSQCreate_which_implies_wit_5.
Axiom proof_of_OSQCreate_which_implies_wit_6 : OSQCreate_which_implies_wit_6.
Axiom proof_of_OSQCreate_which_implies_wit_7 : OSQCreate_which_implies_wit_7.
Axiom proof_of_OSQCreate_which_implies_wit_8 : OSQCreate_which_implies_wit_8.

End VC_Correct.
