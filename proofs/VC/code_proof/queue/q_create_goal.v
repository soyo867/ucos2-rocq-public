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
Require Import Ucos2Verify.VC.code.queue.spec.q_create_spec.
Local Open Scope sac.

(*----- Function OSQCreate -----*)

Definition OSQCreate_safety_wit_1 := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) > 0)) (PreH2 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH3 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH4 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH5 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_outside sg lvs )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_no_free_head sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQCreate_safety_wit_2 := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH2 : (q_create_restore_ready critical_entry retval )) (PreH3 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH4 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH5 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH6 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH7 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_inside sg critical_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_no_free_head sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQCreate_safety_wit_3 := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (eid: Z) (event_rest: (@list Z)) (PreH1 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH2 : (valid_event_id sg eid )) (PreH3 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH4 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH5 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH6 : (q_create_restore_ready critical_entry retval )) (PreH7 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH8 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH9 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH10 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH11 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_outside sg critical_entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQCreate_safety_wit_4 := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (PreH1 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = 0)) (PreH2 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH3 : (q_create_restore_ready critical_entry retval )) (PreH4 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH5 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH6 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH7 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH8 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_outside sg critical_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_no_free_head sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQCreate_safety_wit_5 := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (eid: Z) (event_rest: (@list Z)) (PreH1 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = 0)) (PreH2 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH3 : (valid_event_id sg eid )) (PreH4 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH5 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH6 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH7 : (q_create_restore_ready critical_entry retval )) (PreH8 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH9 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH10 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH11 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH12 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_outside sg critical_entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
|--
  “ False ”
.

Definition OSQCreate_safety_wit_6 := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (PreH1 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH2 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = 0)) (PreH3 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH4 : (q_create_restore_ready critical_entry retval )) (PreH5 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH6 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH7 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH8 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH9 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_outside sg critical_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_no_free_head sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
|--
  “ False ”
.

Definition OSQCreate_safety_wit_7 := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (eid: Z) (event_rest: (@list Z)) (critical_entry_2: UCOS2_Verify_State) (retval_2: Z) (PreH1 : (interrupt_saved_cpu_sr critical_entry critical_entry_2 retval_2 )) (PreH2 : (q_create_restore_ready critical_entry_2 retval_2 )) (PreH3 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH4 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH5 : (valid_event_id sg eid )) (PreH6 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH7 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH8 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH9 : (q_create_restore_ready critical_entry retval )) (PreH10 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH11 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH12 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH13 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH14 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_inside sg critical_entry_2 )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  ((( &( "pq" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQCreate_safety_wit_8 := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (eid: Z) (event_rest: (@list Z)) (critical_entry_2: UCOS2_Verify_State) (retval_2: Z) (PreH1 : ((queue_free_head (sg) (queue_free_ids)) = 0)) (PreH2 : (interrupt_saved_cpu_sr critical_entry critical_entry_2 retval_2 )) (PreH3 : (q_create_restore_ready critical_entry_2 retval_2 )) (PreH4 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH5 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH6 : (valid_event_id sg eid )) (PreH7 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH8 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH9 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH10 : (q_create_restore_ready critical_entry retval )) (PreH11 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH12 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH13 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH14 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH15 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_outside sg critical_entry_2 )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  ((( &( "pq" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQCreate_return_wit_1 := 
(
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (eid: Z) (event_rest: (@list Z)) (critical_entry_2: UCOS2_Verify_State) (retval_2: Z) (qid: Z) (queue_rest: (@list Z)) (PreH1 : (queue_free_ids = (cons (qid) (queue_rest)))) (PreH2 : (valid_queue_id sg qid )) (PreH3 : ((queue_free_head (sg) (queue_free_ids)) = (qcb_addr (sg) (qid)))) (PreH4 : ((queue_free_head (sg) (queue_free_ids)) <> 0)) (PreH5 : (interrupt_saved_cpu_sr critical_entry critical_entry_2 retval_2 )) (PreH6 : (q_create_restore_ready critical_entry_2 retval_2 )) (PreH7 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH8 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH9 : (valid_event_id sg eid )) (PreH10 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH11 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH12 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH13 : (q_create_restore_ready critical_entry retval )) (PreH14 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH15 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH16 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH17 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH18 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |-> 0)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (q_create_outside sg critical_entry_2 )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_rest)))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (queue_rest)))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> start_pre)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (start_pre + (size_pre * sizeof(PTR))))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> start_pre)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> start_pre)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> size_pre)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> 0)
  **  (q_create_queue_free_nodes sg queue_rest )
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 2)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  (q_create_buffer start_pre size_pre buffer )
|--
  EX (lvs2: UCOS2_Verify_State)  (out: QCreateOutcome) ,
  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (q_create_return_ptr (sg) (out))) ” 
  &&  “ (q_create_safe_post lvs2 out X ) ”
  &&  (verification_slice_q_create_post_world sg start_pre size_pre buffer lvs2 out )
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (eid: Z) (event_rest: (@list Z)) (critical_entry_2: UCOS2_Verify_State) (retval_2: Z) (qid: Z) (queue_rest: (@list Z)) (PreH1 : (queue_free_ids = (cons (qid) (queue_rest)))) (PreH2 : (valid_queue_id sg qid )) (PreH3 : ((queue_free_head (sg) (queue_free_ids)) = (qcb_addr (sg) (qid)))) (PreH4 : ((queue_free_head (sg) (queue_free_ids)) <> 0)) (PreH5 : (interrupt_saved_cpu_sr critical_entry critical_entry_2 retval_2 )) (PreH6 : (q_create_restore_ready critical_entry_2 retval_2 )) (PreH7 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH8 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH9 : (valid_event_id sg eid )) (PreH10 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH11 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH12 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH13 : (q_create_restore_ready critical_entry retval )) (PreH14 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH15 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH16 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH17 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH18 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |-> 0)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (q_create_outside sg critical_entry_2 )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_rest)))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (queue_rest)))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> start_pre)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (start_pre + (size_pre * sizeof(PTR))))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> start_pre)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> start_pre)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> size_pre)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> 0)
  **  (q_create_queue_free_nodes sg queue_rest )
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 2)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  (q_create_buffer start_pre size_pre buffer )
|--
  EX (lvs2: UCOS2_Verify_State)  (out: QCreateOutcome) ,
  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (q_create_return_ptr (sg) (out))) ” 
  &&  “ (q_create_safe_post lvs2 out X ) ”
  &&  (verification_slice_q_create_post_world sg start_pre size_pre buffer lvs2 out )
).

Definition OSQCreate_return_wit_2 := 
(
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (eid: Z) (event_rest: (@list Z)) (critical_entry_2: UCOS2_Verify_State) (retval_2: Z) (PreH1 : ((queue_free_head (sg) (queue_free_ids)) = 0)) (PreH2 : (interrupt_saved_cpu_sr critical_entry critical_entry_2 retval_2 )) (PreH3 : (q_create_restore_ready critical_entry_2 retval_2 )) (PreH4 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH5 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH6 : (valid_event_id sg eid )) (PreH7 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH8 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH9 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH10 : (q_create_restore_ready critical_entry retval )) (PreH11 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH12 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH13 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH14 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH15 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_outside sg critical_entry_2 )
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
|--
  EX (lvs2: UCOS2_Verify_State)  (out: QCreateOutcome) ,
  “ (0 = (q_create_return_ptr (sg) (out))) ” 
  &&  “ (q_create_safe_post lvs2 out X ) ”
  &&  (verification_slice_q_create_post_world sg start_pre size_pre buffer lvs2 out )
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (eid: Z) (event_rest: (@list Z)) (critical_entry_2: UCOS2_Verify_State) (retval_2: Z) (PreH1 : ((queue_free_head (sg) (queue_free_ids)) = 0)) (PreH2 : (interrupt_saved_cpu_sr critical_entry critical_entry_2 retval_2 )) (PreH3 : (q_create_restore_ready critical_entry_2 retval_2 )) (PreH4 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH5 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH6 : (valid_event_id sg eid )) (PreH7 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH8 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH9 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH10 : (q_create_restore_ready critical_entry retval )) (PreH11 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH12 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH13 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH14 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH15 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_outside sg critical_entry_2 )
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
|--
  EX (lvs2: UCOS2_Verify_State)  (out: QCreateOutcome) ,
  “ (0 = (q_create_return_ptr (sg) (out))) ” 
  &&  “ (q_create_safe_post lvs2 out X ) ”
  &&  (verification_slice_q_create_post_world sg start_pre size_pre buffer lvs2 out )
).

Definition OSQCreate_return_wit_3 := 
(
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (PreH1 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = 0)) (PreH2 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = 0)) (PreH3 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH4 : (q_create_restore_ready critical_entry retval )) (PreH5 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH6 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH7 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH8 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH9 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_outside sg critical_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_no_free_head sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
|--
  EX (lvs2: UCOS2_Verify_State)  (out: QCreateOutcome) ,
  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (q_create_return_ptr (sg) (out))) ” 
  &&  “ (q_create_safe_post lvs2 out X ) ”
  &&  (verification_slice_q_create_post_world sg start_pre size_pre buffer lvs2 out )
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (PreH1 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = 0)) (PreH2 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = 0)) (PreH3 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH4 : (q_create_restore_ready critical_entry retval )) (PreH5 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH6 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH7 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH8 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH9 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_outside sg critical_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_no_free_head sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
|--
  EX (lvs2: UCOS2_Verify_State)  (out: QCreateOutcome) ,
  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (q_create_return_ptr (sg) (out))) ” 
  &&  “ (q_create_safe_post lvs2 out X ) ”
  &&  (verification_slice_q_create_post_world sg start_pre size_pre buffer lvs2 out )
).

Definition OSQCreate_return_wit_4 := 
(
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) > 0)) (PreH2 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH3 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH4 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH5 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_outside sg lvs )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_no_free_head sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
|--
  EX (lvs2: UCOS2_Verify_State)  (out: QCreateOutcome) ,
  “ (0 = (q_create_return_ptr (sg) (out))) ” 
  &&  “ (q_create_safe_post lvs2 out X ) ”
  &&  (verification_slice_q_create_post_world sg start_pre size_pre buffer lvs2 out )
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) > 0)) (PreH2 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH3 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH4 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH5 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_outside sg lvs )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_no_free_head sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
|--
  EX (lvs2: UCOS2_Verify_State)  (out: QCreateOutcome) ,
  “ (0 = (q_create_return_ptr (sg) (out))) ” 
  &&  “ (q_create_safe_post lvs2 out X ) ”
  &&  (verification_slice_q_create_post_world sg start_pre size_pre buffer lvs2 out )
).

Definition OSQCreate_partial_solve_wit_1_pure := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH2 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
  **  (verification_slice_q_create_world sg start_pre size_pre buffer lvs queue_free_ids )
|--
  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ”
.

Definition OSQCreate_partial_solve_wit_1_aux := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH2 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (verification_slice_q_create_world sg start_pre size_pre buffer lvs queue_free_ids )
|--
  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X ) ”
  &&  (verification_slice_q_create_world sg start_pre size_pre buffer lvs queue_free_ids )
.

Definition OSQCreate_partial_solve_wit_1 := OSQCreate_partial_solve_wit_1_pure -> OSQCreate_partial_solve_wit_1_aux.

Definition OSQCreate_partial_solve_wit_2 := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH2 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH3 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH4 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH5 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_outside sg lvs )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_no_free_head sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
|--
  “ ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids ) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X ) ”
  &&  (q_create_outside sg lvs )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_no_free_head sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
.

Definition OSQCreate_partial_solve_wit_3_pure := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (PreH1 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH2 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH3 : (q_create_restore_ready critical_entry retval )) (PreH4 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH5 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH6 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH7 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH8 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_inside sg critical_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_no_free_head sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
|--
  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0) ” 
  &&  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (free_event_head (sg) ((q_create_unused_events (lvs))))) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ”
.

Definition OSQCreate_partial_solve_wit_3_aux := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (PreH1 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH2 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH3 : (q_create_restore_ready critical_entry retval )) (PreH4 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH5 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH6 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH7 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH8 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_inside sg critical_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_no_free_head sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
|--
  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0) ” 
  &&  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (free_event_head (sg) ((q_create_unused_events (lvs))))) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0) ” 
  &&  “ (interrupt_saved_cpu_sr lvs critical_entry retval ) ” 
  &&  “ (q_create_restore_ready critical_entry retval ) ” 
  &&  “ ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids ) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X ) ”
  &&  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_no_free_head sg lvs )
  **  (q_create_inside sg critical_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
.

Definition OSQCreate_partial_solve_wit_3 := OSQCreate_partial_solve_wit_3_pure -> OSQCreate_partial_solve_wit_3_aux.

Definition OSQCreate_partial_solve_wit_4_pure := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (eid: Z) (event_rest: (@list Z)) (PreH1 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH2 : (valid_event_id sg eid )) (PreH3 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH4 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH5 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH6 : (q_create_restore_ready critical_entry retval )) (PreH7 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH8 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH9 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH10 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH11 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  (q_create_inside sg critical_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
|--
  “ (q_create_restore_ready critical_entry retval ) ”
.

Definition OSQCreate_partial_solve_wit_4_aux := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (eid: Z) (event_rest: (@list Z)) (PreH1 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH2 : (valid_event_id sg eid )) (PreH3 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH4 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH5 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH6 : (q_create_restore_ready critical_entry retval )) (PreH7 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH8 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH9 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH10 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH11 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  (q_create_inside sg critical_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
|--
  “ (q_create_restore_ready critical_entry retval ) ” 
  &&  “ ((q_create_unused_events (lvs)) = (cons (eid) (event_rest))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid))) ” 
  &&  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0) ” 
  &&  “ (interrupt_saved_cpu_sr lvs critical_entry retval ) ” 
  &&  “ (q_create_restore_ready critical_entry retval ) ” 
  &&  “ ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids ) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X ) ”
  &&  (q_create_inside sg critical_entry )
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
.

Definition OSQCreate_partial_solve_wit_4 := OSQCreate_partial_solve_wit_4_pure -> OSQCreate_partial_solve_wit_4_aux.

Definition OSQCreate_partial_solve_wit_5_pure := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (PreH1 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = 0)) (PreH2 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH3 : (q_create_restore_ready critical_entry retval )) (PreH4 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH5 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH6 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH7 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH8 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_inside sg critical_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_no_free_head sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
|--
  “ (q_create_restore_ready critical_entry retval ) ”
.

Definition OSQCreate_partial_solve_wit_5_aux := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (PreH1 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = 0)) (PreH2 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH3 : (q_create_restore_ready critical_entry retval )) (PreH4 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH5 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH6 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH7 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH8 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_inside sg critical_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_no_free_head sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
|--
  “ (q_create_restore_ready critical_entry retval ) ” 
  &&  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) = 0) ” 
  &&  “ (interrupt_saved_cpu_sr lvs critical_entry retval ) ” 
  &&  “ (q_create_restore_ready critical_entry retval ) ” 
  &&  “ ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids ) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X ) ”
  &&  (q_create_inside sg critical_entry )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_no_free_head sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
.

Definition OSQCreate_partial_solve_wit_5 := OSQCreate_partial_solve_wit_5_pure -> OSQCreate_partial_solve_wit_5_aux.

Definition OSQCreate_partial_solve_wit_6 := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (eid: Z) (event_rest: (@list Z)) (PreH1 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH2 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH3 : (valid_event_id sg eid )) (PreH4 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH5 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH6 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH7 : (q_create_restore_ready critical_entry retval )) (PreH8 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH9 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH10 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH11 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH12 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_outside sg critical_entry )
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
|--
  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0) ” 
  &&  “ ((q_create_unused_events (lvs)) = (cons (eid) (event_rest))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid))) ” 
  &&  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0) ” 
  &&  “ (interrupt_saved_cpu_sr lvs critical_entry retval ) ” 
  &&  “ (q_create_restore_ready critical_entry retval ) ” 
  &&  “ ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids ) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X ) ”
  &&  (q_create_outside sg critical_entry )
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
.

Definition OSQCreate_partial_solve_wit_7_pure := 
(
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (eid: Z) (event_rest: (@list Z)) (critical_entry_2: UCOS2_Verify_State) (retval_2: Z) (PreH1 : ((queue_free_head (sg) (queue_free_ids)) <> 0)) (PreH2 : (interrupt_saved_cpu_sr critical_entry critical_entry_2 retval_2 )) (PreH3 : (q_create_restore_ready critical_entry_2 retval_2 )) (PreH4 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH5 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH6 : (valid_event_id sg eid )) (PreH7 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH8 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH9 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH10 : (q_create_restore_ready critical_entry retval )) (PreH11 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH12 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH13 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH14 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH15 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_inside sg critical_entry_2 )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  ((( &( "pq" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
|--
  “ ((queue_free_head (sg) (queue_free_ids)) <> 0) ” 
  &&  “ ((queue_free_head (sg) (queue_free_ids)) = (queue_free_head (sg) (queue_free_ids))) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_free_ids_valid sg queue_free_ids ) ”
) \/
(
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (eid: Z) (event_rest: (@list Z)) (critical_entry_2: UCOS2_Verify_State) (retval_2: Z) (PreH1 : (retval_2 <= UINT_MAX)) (PreH2 : (retval_2 >= 0)) (PreH3 : ((queue_free_head (sg) (queue_free_ids)) <> 0)) (PreH4 : (interrupt_saved_cpu_sr critical_entry critical_entry_2 retval_2 )) (PreH5 : (q_create_restore_ready critical_entry_2 retval_2 )) (PreH6 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH7 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH8 : (valid_event_id sg eid )) (PreH9 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH10 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH11 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH12 : (q_create_restore_ready critical_entry retval )) (PreH13 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH14 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH15 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH16 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH17 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_inside sg critical_entry_2 )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  ((( &( "pq" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
|--
  “ (queue_free_ids_valid sg queue_free_ids ) ”
).

Definition OSQCreate_partial_solve_wit_7_pure_split_goal_1 := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (eid: Z) (event_rest: (@list Z)) (critical_entry_2: UCOS2_Verify_State) (retval_2: Z) (PreH1 : (retval_2 <= UINT_MAX)) (PreH2 : (retval_2 >= 0)) (PreH3 : ((queue_free_head (sg) (queue_free_ids)) <> 0)) (PreH4 : (interrupt_saved_cpu_sr critical_entry critical_entry_2 retval_2 )) (PreH5 : (q_create_restore_ready critical_entry_2 retval_2 )) (PreH6 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH7 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH8 : (valid_event_id sg eid )) (PreH9 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH10 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH11 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH12 : (q_create_restore_ready critical_entry retval )) (PreH13 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH14 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH15 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH16 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH17 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_inside sg critical_entry_2 )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  ((( &( "pq" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
|--
  “ (queue_free_ids_valid sg queue_free_ids ) ”
.

Definition OSQCreate_partial_solve_wit_7_aux := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (eid: Z) (event_rest: (@list Z)) (critical_entry_2: UCOS2_Verify_State) (retval_2: Z) (PreH1 : ((queue_free_head (sg) (queue_free_ids)) <> 0)) (PreH2 : (interrupt_saved_cpu_sr critical_entry critical_entry_2 retval_2 )) (PreH3 : (q_create_restore_ready critical_entry_2 retval_2 )) (PreH4 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH5 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH6 : (valid_event_id sg eid )) (PreH7 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH8 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH9 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH10 : (q_create_restore_ready critical_entry retval )) (PreH11 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH12 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH13 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH14 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH15 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_inside sg critical_entry_2 )
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
|--
  “ ((queue_free_head (sg) (queue_free_ids)) <> 0) ” 
  &&  “ ((queue_free_head (sg) (queue_free_ids)) = (queue_free_head (sg) (queue_free_ids))) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_free_ids_valid sg queue_free_ids ) ” 
  &&  “ ((queue_free_head (sg) (queue_free_ids)) <> 0) ” 
  &&  “ (interrupt_saved_cpu_sr critical_entry critical_entry_2 retval_2 ) ” 
  &&  “ (q_create_restore_ready critical_entry_2 retval_2 ) ” 
  &&  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0) ” 
  &&  “ ((q_create_unused_events (lvs)) = (cons (eid) (event_rest))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid))) ” 
  &&  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0) ” 
  &&  “ (interrupt_saved_cpu_sr lvs critical_entry retval ) ” 
  &&  “ (q_create_restore_ready critical_entry retval ) ” 
  &&  “ ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids ) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X ) ”
  &&  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_inside sg critical_entry_2 )
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  (q_create_buffer start_pre size_pre buffer )
.

Definition OSQCreate_partial_solve_wit_7 := OSQCreate_partial_solve_wit_7_pure -> OSQCreate_partial_solve_wit_7_aux.

Definition OSQCreate_partial_solve_wit_8_pure := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry_2: UCOS2_Verify_State) (retval_2: Z) (eid: Z) (event_rest: (@list Z)) (critical_entry: UCOS2_Verify_State) (retval: Z) (qid: Z) (queue_rest: (@list Z)) (PreH1 : (queue_free_ids = (cons (qid) (queue_rest)))) (PreH2 : (valid_queue_id sg qid )) (PreH3 : ((queue_free_head (sg) (queue_free_ids)) = (qcb_addr (sg) (qid)))) (PreH4 : ((queue_free_head (sg) (queue_free_ids)) <> 0)) (PreH5 : (interrupt_saved_cpu_sr critical_entry_2 critical_entry retval )) (PreH6 : (q_create_restore_ready critical_entry retval )) (PreH7 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH8 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH9 : (valid_event_id sg eid )) (PreH10 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH11 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH12 : (interrupt_saved_cpu_sr lvs critical_entry_2 retval_2 )) (PreH13 : (q_create_restore_ready critical_entry_2 retval_2 )) (PreH14 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH15 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH16 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH17 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH18 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  ((( &( "pq" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_rest)))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (queue_rest)))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQStart")) # Ptr  |->_)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |->_)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQIn")) # Ptr  |->_)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQOut")) # Ptr  |->_)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQEntries")) # UShort  |->_)
  **  (q_create_queue_free_nodes sg queue_rest )
  **  (q_create_inside sg critical_entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  (q_create_buffer start_pre size_pre buffer )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
|--
  “ (q_create_restore_ready critical_entry retval ) ”
.

Definition OSQCreate_partial_solve_wit_8_aux := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry_2: UCOS2_Verify_State) (retval_2: Z) (eid: Z) (event_rest: (@list Z)) (critical_entry: UCOS2_Verify_State) (retval: Z) (qid: Z) (queue_rest: (@list Z)) (PreH1 : (queue_free_ids = (cons (qid) (queue_rest)))) (PreH2 : (valid_queue_id sg qid )) (PreH3 : ((queue_free_head (sg) (queue_free_ids)) = (qcb_addr (sg) (qid)))) (PreH4 : ((queue_free_head (sg) (queue_free_ids)) <> 0)) (PreH5 : (interrupt_saved_cpu_sr critical_entry_2 critical_entry retval )) (PreH6 : (q_create_restore_ready critical_entry retval )) (PreH7 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH8 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH9 : (valid_event_id sg eid )) (PreH10 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH11 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH12 : (interrupt_saved_cpu_sr lvs critical_entry_2 retval_2 )) (PreH13 : (q_create_restore_ready critical_entry_2 retval_2 )) (PreH14 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH15 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH16 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH17 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH18 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_rest)))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (queue_rest)))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQStart")) # Ptr  |->_)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |->_)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQIn")) # Ptr  |->_)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQOut")) # Ptr  |->_)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQEntries")) # UShort  |->_)
  **  (q_create_queue_free_nodes sg queue_rest )
  **  (q_create_inside sg critical_entry )
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  (q_create_buffer start_pre size_pre buffer )
|--
  “ (q_create_restore_ready critical_entry retval ) ” 
  &&  “ (queue_free_ids = (cons (qid) (queue_rest))) ” 
  &&  “ (valid_queue_id sg qid ) ” 
  &&  “ ((queue_free_head (sg) (queue_free_ids)) = (qcb_addr (sg) (qid))) ” 
  &&  “ ((queue_free_head (sg) (queue_free_ids)) <> 0) ” 
  &&  “ (interrupt_saved_cpu_sr critical_entry_2 critical_entry retval ) ” 
  &&  “ (q_create_restore_ready critical_entry retval ) ” 
  &&  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0) ” 
  &&  “ ((q_create_unused_events (lvs)) = (cons (eid) (event_rest))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid))) ” 
  &&  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0) ” 
  &&  “ (interrupt_saved_cpu_sr lvs critical_entry_2 retval_2 ) ” 
  &&  “ (q_create_restore_ready critical_entry_2 retval_2 ) ” 
  &&  “ ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids ) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X ) ”
  &&  (q_create_inside sg critical_entry )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_rest)))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (queue_rest)))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQStart")) # Ptr  |->_)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |->_)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQIn")) # Ptr  |->_)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQOut")) # Ptr  |->_)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQEntries")) # UShort  |->_)
  **  (q_create_queue_free_nodes sg queue_rest )
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  (q_create_buffer start_pre size_pre buffer )
.

Definition OSQCreate_partial_solve_wit_8 := OSQCreate_partial_solve_wit_8_pure -> OSQCreate_partial_solve_wit_8_aux.

Definition OSQCreate_partial_solve_wit_9_pure := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (eid: Z) (event_rest: (@list Z)) (critical_entry_2: UCOS2_Verify_State) (retval_2: Z) (qid: Z) (queue_rest: (@list Z)) (PreH1 : (queue_free_ids = (cons (qid) (queue_rest)))) (PreH2 : (valid_queue_id sg qid )) (PreH3 : ((queue_free_head (sg) (queue_free_ids)) = (qcb_addr (sg) (qid)))) (PreH4 : ((queue_free_head (sg) (queue_free_ids)) <> 0)) (PreH5 : (interrupt_saved_cpu_sr critical_entry critical_entry_2 retval_2 )) (PreH6 : (q_create_restore_ready critical_entry_2 retval_2 )) (PreH7 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH8 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH9 : (valid_event_id sg eid )) (PreH10 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH11 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH12 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH13 : (q_create_restore_ready critical_entry retval )) (PreH14 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH15 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH16 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH17 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH18 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_outside sg critical_entry_2 )
  **  ((( &( "pq" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_rest)))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (queue_rest)))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> start_pre)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (start_pre + (size_pre * sizeof(PTR))))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> start_pre)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> start_pre)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> size_pre)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> 0)
  **  (q_create_queue_free_nodes sg queue_rest )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 2)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  (q_create_buffer start_pre size_pre buffer )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval_2)
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
|--
  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0) ”
.

Definition OSQCreate_partial_solve_wit_9_aux := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry: UCOS2_Verify_State) (retval: Z) (eid: Z) (event_rest: (@list Z)) (critical_entry_2: UCOS2_Verify_State) (retval_2: Z) (qid: Z) (queue_rest: (@list Z)) (PreH1 : (queue_free_ids = (cons (qid) (queue_rest)))) (PreH2 : (valid_queue_id sg qid )) (PreH3 : ((queue_free_head (sg) (queue_free_ids)) = (qcb_addr (sg) (qid)))) (PreH4 : ((queue_free_head (sg) (queue_free_ids)) <> 0)) (PreH5 : (interrupt_saved_cpu_sr critical_entry critical_entry_2 retval_2 )) (PreH6 : (q_create_restore_ready critical_entry_2 retval_2 )) (PreH7 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH8 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH9 : (valid_event_id sg eid )) (PreH10 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH11 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH12 : (interrupt_saved_cpu_sr lvs critical_entry retval )) (PreH13 : (q_create_restore_ready critical_entry retval )) (PreH14 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH15 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH16 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH17 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH18 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_outside sg critical_entry_2 )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_rest)))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (queue_rest)))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> start_pre)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (start_pre + (size_pre * sizeof(PTR))))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> start_pre)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> start_pre)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> size_pre)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> 0)
  **  (q_create_queue_free_nodes sg queue_rest )
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 2)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  (q_create_buffer start_pre size_pre buffer )
|--
  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0) ” 
  &&  “ (queue_free_ids = (cons (qid) (queue_rest))) ” 
  &&  “ (valid_queue_id sg qid ) ” 
  &&  “ ((queue_free_head (sg) (queue_free_ids)) = (qcb_addr (sg) (qid))) ” 
  &&  “ ((queue_free_head (sg) (queue_free_ids)) <> 0) ” 
  &&  “ (interrupt_saved_cpu_sr critical_entry critical_entry_2 retval_2 ) ” 
  &&  “ (q_create_restore_ready critical_entry_2 retval_2 ) ” 
  &&  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0) ” 
  &&  “ ((q_create_unused_events (lvs)) = (cons (eid) (event_rest))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid))) ” 
  &&  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0) ” 
  &&  “ (interrupt_saved_cpu_sr lvs critical_entry retval ) ” 
  &&  “ (q_create_restore_ready critical_entry retval ) ” 
  &&  “ ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids ) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X ) ”
  &&  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  (q_create_outside sg critical_entry_2 )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_rest)))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (queue_rest)))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> start_pre)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> (start_pre + (size_pre * sizeof(PTR))))
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> start_pre)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> start_pre)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQSize")) # UShort  |-> size_pre)
  **  ((&(((queue_free_head (sg) (queue_free_ids)))  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> 0)
  **  (q_create_queue_free_nodes sg queue_rest )
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 2)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  (q_create_buffer start_pre size_pre buffer )
.

Definition OSQCreate_partial_solve_wit_9 := OSQCreate_partial_solve_wit_9_pure -> OSQCreate_partial_solve_wit_9_aux.

Definition OSQCreate_partial_solve_wit_10_pure := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry_2: UCOS2_Verify_State) (retval_2: Z) (eid: Z) (event_rest: (@list Z)) (critical_entry: UCOS2_Verify_State) (retval: Z) (PreH1 : ((queue_free_head (sg) (queue_free_ids)) = 0)) (PreH2 : (interrupt_saved_cpu_sr critical_entry_2 critical_entry retval )) (PreH3 : (q_create_restore_ready critical_entry retval )) (PreH4 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH5 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH6 : (valid_event_id sg eid )) (PreH7 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH8 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH9 : (interrupt_saved_cpu_sr lvs critical_entry_2 retval_2 )) (PreH10 : (q_create_restore_ready critical_entry_2 retval_2 )) (PreH11 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH12 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH13 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH14 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH15 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_inside sg critical_entry )
  **  ((( &( "pevent" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  ((( &( "start" ) )) # Ptr  |-> start_pre)
  **  ((( &( "size" ) )) # UShort  |-> size_pre)
|--
  “ (q_create_restore_ready critical_entry retval ) ”
.

Definition OSQCreate_partial_solve_wit_10_aux := 
forall (size_pre: Z) (start_pre: Z) (X: QCreateContinuation) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (critical_entry_2: UCOS2_Verify_State) (retval_2: Z) (eid: Z) (event_rest: (@list Z)) (critical_entry: UCOS2_Verify_State) (retval: Z) (PreH1 : ((queue_free_head (sg) (queue_free_ids)) = 0)) (PreH2 : (interrupt_saved_cpu_sr critical_entry_2 critical_entry retval )) (PreH3 : (q_create_restore_ready critical_entry retval )) (PreH4 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH5 : ((q_create_unused_events (lvs)) = (cons (eid) (event_rest)))) (PreH6 : (valid_event_id sg eid )) (PreH7 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid)))) (PreH8 : ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0)) (PreH9 : (interrupt_saved_cpu_sr lvs critical_entry_2 retval_2 )) (PreH10 : (q_create_restore_ready critical_entry_2 retval_2 )) (PreH11 : ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0)) (PreH12 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH13 : (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids )) (PreH14 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) (PreH15 : (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X )) ,
  (q_create_inside sg critical_entry )
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
|--
  “ (q_create_restore_ready critical_entry retval ) ” 
  &&  “ ((queue_free_head (sg) (queue_free_ids)) = 0) ” 
  &&  “ (interrupt_saved_cpu_sr critical_entry_2 critical_entry retval ) ” 
  &&  “ (q_create_restore_ready critical_entry retval ) ” 
  &&  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0) ” 
  &&  “ ((q_create_unused_events (lvs)) = (cons (eid) (event_rest))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) = (event_addr (sg) (eid))) ” 
  &&  “ ((free_event_head (sg) ((q_create_unused_events (lvs)))) <> 0) ” 
  &&  “ (interrupt_saved_cpu_sr lvs critical_entry_2 retval_2 ) ” 
  &&  “ (q_create_restore_ready critical_entry_2 retval_2 ) ” 
  &&  “ ((unsigned_last_nbits ((q_create_int_nesting (lvs))) (32)) <= 0) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids ) ” 
  &&  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (verification_slice_q_create_safe_pre sg start_pre size_pre queue_free_ids buffer lvs X ) ”
  &&  (q_create_inside sg critical_entry )
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&(((free_event_head (sg) ((q_create_unused_events (lvs)))))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
.

Definition OSQCreate_partial_solve_wit_10 := OSQCreate_partial_solve_wit_10_pure -> OSQCreate_partial_solve_wit_10_aux.

Definition OSQCreate_which_implies_wit_1 := 
(
forall (size_pre: Z) (start_pre: Z) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) ,
  (verification_slice_q_create_world sg start_pre size_pre buffer lvs queue_free_ids )
|--
  “ (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids ) ”
  &&  (q_create_outside sg lvs )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_no_free_head sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
) \/
(
forall (size_pre: Z) (start_pre: Z) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) ,
  (verification_slice_q_create_world sg start_pre size_pre buffer lvs queue_free_ids )
|--
  “ (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids ) ”
  &&  (q_create_outside sg lvs )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_no_free_head sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
).

Definition OSQCreate_which_implies_wit_1_split_goal_1 := 
forall (size_pre: Z) (start_pre: Z) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) ,
  (verification_slice_q_create_world sg start_pre size_pre buffer lvs queue_free_ids )
|--
  “ (verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs queue_free_ids ) ”
.

Definition OSQCreate_which_implies_wit_1_split_goal_spatial := 
forall (size_pre: Z) (start_pre: Z) (buffer: (@list Z)) (queue_free_ids: (@list Z)) (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) ,
  (verification_slice_q_create_world sg start_pre size_pre buffer lvs queue_free_ids )
|--
  (q_create_outside sg lvs )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_create_int_nesting (lvs)))
  **  (q_create_interrupt_residual sg lvs )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_event_head (sg) ((q_create_unused_events (lvs)))))
  **  (verification_slice_q_create_event_no_free_head sg lvs )
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (queue_free_ids)))
  **  (q_create_queue_free_nodes sg queue_free_ids )
  **  (q_create_buffer start_pre size_pre buffer )
.

Definition OSQCreate_which_implies_wit_2 := 
(
forall (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (pevent: Z) (PreH1 : (pevent <> 0)) (PreH2 : (pevent = (free_event_head (sg) ((q_create_unused_events (lvs)))))) (PreH3 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) ,
  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pevent)
  **  (verification_slice_q_create_event_no_free_head sg lvs )
|--
  EX (eid: Z)  (event_rest: (@list Z)) ,
  “ ((q_create_unused_events (lvs)) = (cons (eid) (event_rest))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pevent)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventTbl")) # UChar  |->_)
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |->_)
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |->_)
) \/
(
forall (lvs: UCOS2_Verify_State) (sg: StableGlobVars) (pevent: Z) (PreH1 : (pevent <> 0)) (PreH2 : (pevent = (free_event_head (sg) ((q_create_unused_events (lvs)))))) (PreH3 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) ,
  (verification_slice_q_create_event_no_free_head sg lvs )
|--
  EX (x_10: Z)  (x_9: Z)  (x_8: Z)  (x_7: Z)  (x_6: Z)  (x_5: Z)  (x_4: Z)  (x_3: Z)  (x_2: Z)  (x: Z)  (eid: Z)  (event_rest: (@list Z)) ,
  “ ((q_create_unused_events (lvs)) = (cons (eid) (event_rest))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> x_10)
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> x_9)
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> x_8)
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> x_7)
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> x_6)
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> x_5)
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> x_4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventTbl")) # UChar  |-> x_3)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> x_2)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> x)
  **  (verification_slice_q_create_event_residual sg lvs event_rest )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (free_event_head (sg) (event_rest)))
).

Definition OSQCreate_which_implies_wit_3 := 
(
forall (queue_free_ids: (@list Z)) (sg: StableGlobVars) (pq: Z) (PreH1 : (pq <> 0)) (PreH2 : (pq = (queue_free_head (sg) (queue_free_ids)))) (PreH3 : (queue_free_ids_valid sg queue_free_ids )) (PreH4 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) ,
  ((( &( "OSQFreeList" ) )) # Ptr  |-> pq)
  **  (q_create_queue_free_nodes sg queue_free_ids )
|--
  EX (qid: Z)  (queue_rest: (@list Z)) ,
  “ (queue_free_ids = (cons (qid) (queue_rest))) ” 
  &&  “ (valid_queue_id sg qid ) ” 
  &&  “ (pq = (qcb_addr (sg) (qid))) ”
  &&  ((( &( "OSQFreeList" ) )) # Ptr  |-> pq)
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (queue_rest)))
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |->_)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |->_)
  **  (q_create_queue_free_nodes sg queue_rest )
) \/
(
forall (queue_free_ids: (@list Z)) (sg: StableGlobVars) (pq: Z) (PreH1 : (pq <> 0)) (PreH2 : (pq = (queue_free_head (sg) (queue_free_ids)))) (PreH3 : (queue_free_ids_valid sg queue_free_ids )) (PreH4 : (q_create_global_layout_prop sg ( &( "OSIntNesting" ) ) ( &( "OSEventFreeList" ) ) ( &( "OSQFreeList" ) ) )) ,
  (q_create_queue_free_nodes sg queue_free_ids )
|--
  EX (x_6: Z)  (x_5: Z)  (x_4: Z)  (x_3: Z)  (x_2: Z)  (x: Z)  (qid: Z)  (queue_rest: (@list Z)) ,
  “ (queue_free_ids = (cons (qid) (queue_rest))) ” 
  &&  “ (valid_queue_id sg qid ) ” 
  &&  “ (pq = (qcb_addr (sg) (qid))) ”
  &&  ((&((pq)  # "os_q" ->ₛ "OSQEntries")) # UShort  |-> x_6)
  **  ((&((pq)  # "os_q" ->ₛ "OSQSize")) # UShort  |-> x_5)
  **  ((&((pq)  # "os_q" ->ₛ "OSQOut")) # Ptr  |-> x_4)
  **  ((&((pq)  # "os_q" ->ₛ "OSQIn")) # Ptr  |-> x_3)
  **  ((&((pq)  # "os_q" ->ₛ "OSQEnd")) # Ptr  |-> x_2)
  **  ((&((pq)  # "os_q" ->ₛ "OSQStart")) # Ptr  |-> x)
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (queue_rest)))
  **  (q_create_queue_free_nodes sg queue_rest )
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
Axiom proof_of_OSQCreate_return_wit_1 : OSQCreate_return_wit_1.
Axiom proof_of_OSQCreate_return_wit_2 : OSQCreate_return_wit_2.
Axiom proof_of_OSQCreate_return_wit_3 : OSQCreate_return_wit_3.
Axiom proof_of_OSQCreate_return_wit_4 : OSQCreate_return_wit_4.
Axiom proof_of_OSQCreate_partial_solve_wit_1_pure : OSQCreate_partial_solve_wit_1_pure.
Axiom proof_of_OSQCreate_partial_solve_wit_1 : OSQCreate_partial_solve_wit_1.
Axiom proof_of_OSQCreate_partial_solve_wit_2 : OSQCreate_partial_solve_wit_2.
Axiom proof_of_OSQCreate_partial_solve_wit_3_pure : OSQCreate_partial_solve_wit_3_pure.
Axiom proof_of_OSQCreate_partial_solve_wit_3 : OSQCreate_partial_solve_wit_3.
Axiom proof_of_OSQCreate_partial_solve_wit_4_pure : OSQCreate_partial_solve_wit_4_pure.
Axiom proof_of_OSQCreate_partial_solve_wit_4 : OSQCreate_partial_solve_wit_4.
Axiom proof_of_OSQCreate_partial_solve_wit_5_pure : OSQCreate_partial_solve_wit_5_pure.
Axiom proof_of_OSQCreate_partial_solve_wit_5 : OSQCreate_partial_solve_wit_5.
Axiom proof_of_OSQCreate_partial_solve_wit_6 : OSQCreate_partial_solve_wit_6.
Axiom proof_of_OSQCreate_partial_solve_wit_7_pure : OSQCreate_partial_solve_wit_7_pure.
Axiom proof_of_OSQCreate_partial_solve_wit_7 : OSQCreate_partial_solve_wit_7.
Axiom proof_of_OSQCreate_partial_solve_wit_8_pure : OSQCreate_partial_solve_wit_8_pure.
Axiom proof_of_OSQCreate_partial_solve_wit_8 : OSQCreate_partial_solve_wit_8.
Axiom proof_of_OSQCreate_partial_solve_wit_9_pure : OSQCreate_partial_solve_wit_9_pure.
Axiom proof_of_OSQCreate_partial_solve_wit_9 : OSQCreate_partial_solve_wit_9.
Axiom proof_of_OSQCreate_partial_solve_wit_10_pure : OSQCreate_partial_solve_wit_10_pure.
Axiom proof_of_OSQCreate_partial_solve_wit_10 : OSQCreate_partial_solve_wit_10.
Axiom proof_of_OSQCreate_which_implies_wit_1 : OSQCreate_which_implies_wit_1.
Axiom proof_of_OSQCreate_which_implies_wit_2 : OSQCreate_which_implies_wit_2.
Axiom proof_of_OSQCreate_which_implies_wit_3 : OSQCreate_which_implies_wit_3.

End VC_Correct.
