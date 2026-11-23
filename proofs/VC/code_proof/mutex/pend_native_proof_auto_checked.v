(* Ordinary proof candidate for the unchanged canonical auto partition. *)
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
From Ucos2Verify.VC.code.mutex Require Import pend_native_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_api_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Local Open Scope sac.

Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_entry_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_wait_proof_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_entry_arithmetic_proof_spec.

Lemma proof_of_OSMutexPend_safety_wit_1 : OSMutexPend_safety_wit_1.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_2 : OSMutexPend_safety_wit_2.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_3 : OSMutexPend_safety_wit_3.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_4 : OSMutexPend_safety_wit_4.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_5 : OSMutexPend_safety_wit_5.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_7 : OSMutexPend_safety_wit_7.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_8 : OSMutexPend_safety_wit_8.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_9 : OSMutexPend_safety_wit_9.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_10 : OSMutexPend_safety_wit_10.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_11 : OSMutexPend_safety_wit_11.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_12 : OSMutexPend_safety_wit_12.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_13 : OSMutexPend_safety_wit_13.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_20 : OSMutexPend_safety_wit_20.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_21 : OSMutexPend_safety_wit_21.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_22 : OSMutexPend_safety_wit_22.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_23 : OSMutexPend_safety_wit_23.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_24 : OSMutexPend_safety_wit_24.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_25 : OSMutexPend_safety_wit_25.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_26 : OSMutexPend_safety_wit_26.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_27 : OSMutexPend_safety_wit_27.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_28 : OSMutexPend_safety_wit_28.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_29 : OSMutexPend_safety_wit_29.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_safety_wit_30 : OSMutexPend_safety_wit_30.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_1 : OSMutexPend_partial_solve_wit_1.
Proof.
  unfold OSMutexPend_partial_solve_wit_1.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external PreH1 PreH2 PreH3 PreH4 PreH5 PreH6.
  intros h Hheap.
  assert (Hspatial :
((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  (sem_pend_error_cell pd )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
|--
((( &( "perr" ) )) # Ptr  |-> pd)
  **  (sem_pend_error_cell pd )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. entailer!. }
  refine (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_2 : OSMutexPend_partial_solve_wit_2.
Proof.
  unfold OSMutexPend_partial_solve_wit_2.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external PreH1 PreH2 PreH3 PreH4 PreH5 PreH6.
  intros h Hheap.
  assert (Hspatial :
((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  (sem_pend_error_cell pd )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
|--
((( &( "perr" ) )) # Ptr  |-> pd)
  **  (sem_pend_error_cell pd )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. entailer!. }
  refine (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_3_pure : OSMutexPend_partial_solve_wit_3_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_3 : OSMutexPend_partial_solve_wit_3.
Proof.
  unfold OSMutexPend_partial_solve_wit_3, OSMutexPend_partial_solve_wit_3_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7.
  intros h Hheap.
  assert (Hspatial :
((pd) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
|--
(mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (sem_pend_continuation_save_input external platform environment critical saved_local sg context mask before )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (unmap_table_rep sg )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_4 : OSMutexPend_partial_solve_wit_4.
Proof.
  unfold OSMutexPend_partial_solve_wit_4.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (unmap_table_rep sg )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
|--
(mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (unmap_table_rep sg )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_5_pure : OSMutexPend_partial_solve_wit_5_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_5 : OSMutexPend_partial_solve_wit_5.
Proof.
  unfold OSMutexPend_partial_solve_wit_5, OSMutexPend_partial_solve_wit_5_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (unmap_table_rep sg )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
|--
(mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (sem_pend_optional_continuation_resources external platform environment saved_local context before )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((before.(IntrState) ).(intNesting) ))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> ((before.(IntrState) ).(lockNesting) ))
  **  (sem_pend_interrupt_frame sg before )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (unmap_table_rep sg )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_6 : OSMutexPend_partial_solve_wit_6.
Proof.
  unfold OSMutexPend_partial_solve_wit_6.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (task_tcb_init_continuation_save_input owned critical saved_local sg context mask before )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (unmap_table_rep sg )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
|--
(task_tcb_init_continuation_save_input owned critical saved_local sg context mask before )
  **  (unmap_table_rep sg )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_7_pure : OSMutexPend_partial_solve_wit_7_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_7 : OSMutexPend_partial_solve_wit_7.
Proof.
  unfold OSMutexPend_partial_solve_wit_7, OSMutexPend_partial_solve_wit_7_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_api_save_output owned critical saved_local sg context mask retval before )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
|--
(mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_api_save_output owned critical saved_local sg context mask retval before )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_8 : OSMutexPend_partial_solve_wit_8.
Proof.
  unfold OSMutexPend_partial_solve_wit_8, OSMutexPend_partial_solve_wit_8_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29.
  unfold mutex_pend_fact; Intros.
  destruct (mutex_pend_acquire_byte_observations owned critical sg idle context entered mask retval
    before entry eid observed current m tid caller ltac:(assumption) ltac:(assumption))
    as [Hnone [Hpcp [Hcast [Hprio [Hdisabled Hstore]]]]].
  rewrite Hcast, Hprio in *.
  entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_9_pure : OSMutexPend_partial_solve_wit_9_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_9 : OSMutexPend_partial_solve_wit_9.
Proof.
  unfold OSMutexPend_partial_solve_wit_9, OSMutexPend_partial_solve_wit_9_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_first_acquired (sg) (eid) (ticks) (entry) (120) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((caller.(curPrio) ))))) )
  **  (mutex_pend_api_restore_input false owned critical saved_local sg entered retval entry (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((caller.(curPrio) ))) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
|--
(mutex_pend_api_restore_input false owned critical saved_local sg entered retval entry (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((caller.(curPrio) ))) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_first_acquired (sg) (eid) (ticks) (entry) (120) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((caller.(curPrio) ))))) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_10 : OSMutexPend_partial_solve_wit_10.
Proof.
  unfold OSMutexPend_partial_solve_wit_10, OSMutexPend_partial_solve_wit_10_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29.
  unfold mutex_pend_fact; Intros.
  destruct (mutex_pend_acquire_byte_observations owned critical sg idle context entered mask retval
    before entry eid observed current m tid caller ltac:(assumption) ltac:(assumption))
    as [Hnone [Hpcp [Hcast [Hprio [Hdisabled Hstore]]]]].
  rewrite Hcast, Hprio in *.
  assert (Hcode : encode_os_err_code (mutex_pend_acquire_error sg
    (Z.shiftr (encode_event_cnt_value current) 8) caller.(curPrio)) = 0).
  { unfold mutex_pend_acquire_error; rewrite Hdisabled.
    destruct (Z.eqb (Z.shiftr (encode_event_cnt_value current) 8) 255) eqn:En; [reflexivity|].
    assert (Hp : Z.leb caller.(curPrio) (Z.shiftr (encode_event_cnt_value current) 8) = false)
      by (apply Z.leb_gt; lia).
    rewrite Hp; reflexivity. }
  entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_11 : OSMutexPend_partial_solve_wit_11.
Proof.
  unfold OSMutexPend_partial_solve_wit_11, OSMutexPend_partial_solve_wit_11_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28.
  unfold mutex_pend_fact; Intros.
  destruct (mutex_pend_acquire_byte_observations owned critical sg idle context entered mask retval
    before entry eid observed current m tid caller ltac:(assumption) ltac:(assumption))
    as [Hnone [Hpcp [Hcast [Hprio [Hdisabled Hstore]]]]].
  rewrite Hcast, Hprio in *.
  assert (Hpcpdisabled : Z.shiftr (encode_event_cnt_value current) 8 = 255) by assumption.
  assert (Hcode : encode_os_err_code (mutex_pend_acquire_error sg
    (Z.shiftr (encode_event_cnt_value current) 8) caller.(curPrio)) = 0).
  { unfold mutex_pend_acquire_error; rewrite Hdisabled, Hpcpdisabled; reflexivity. }
  entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_12_pure : OSMutexPend_partial_solve_wit_12_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_12 : OSMutexPend_partial_solve_wit_12.
Proof.
  unfold OSMutexPend_partial_solve_wit_12, OSMutexPend_partial_solve_wit_12_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_first_acquired (sg) (eid) (ticks) (entry) (0) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((caller.(curPrio) ))))) )
  **  (mutex_pend_api_restore_input false owned critical saved_local sg entered retval entry (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((caller.(curPrio) ))) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
|--
(mutex_pend_api_restore_input false owned critical saved_local sg entered retval entry (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((caller.(curPrio) ))) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_first_acquired (sg) (eid) (ticks) (entry) (0) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((caller.(curPrio) ))))) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_13_pure : OSMutexPend_partial_solve_wit_13_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_13 : OSMutexPend_partial_solve_wit_13.
Proof.
  unfold OSMutexPend_partial_solve_wit_13, OSMutexPend_partial_solve_wit_13_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_first_acquired (sg) (eid) (ticks) (entry) (0) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((caller.(curPrio) ))))) )
  **  (mutex_pend_api_restore_input false owned critical saved_local sg entered retval entry (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((caller.(curPrio) ))) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
|--
(mutex_pend_api_restore_input false owned critical saved_local sg entered retval entry (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((caller.(curPrio) ))) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_first_acquired (sg) (eid) (ticks) (entry) (0) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((caller.(curPrio) ))))) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_14_pure : OSMutexPend_partial_solve_wit_14_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_14 : OSMutexPend_partial_solve_wit_14.
Proof.
  unfold OSMutexPend_partial_solve_wit_14, OSMutexPend_partial_solve_wit_14_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (encode_event_ptr_value (sg) (current)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_accept_current_frame sg entry eid current tid caller )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
|--
(mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (encode_event_ptr_value (sg) (current)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_accept_current_frame sg entry eid current tid caller )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_15_pure : OSMutexPend_partial_solve_wit_15_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_15 : OSMutexPend_partial_solve_wit_15.
Proof.
  unfold OSMutexPend_partial_solve_wit_15, OSMutexPend_partial_solve_wit_15_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (UCOS2_inv sg entry )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
|--
(mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (UCOS2_inv sg entry )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_16_pure : OSMutexPend_partial_solve_wit_16_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_16 : OSMutexPend_partial_solve_wit_16.
Proof.
  unfold OSMutexPend_partial_solve_wit_16, OSMutexPend_partial_solve_wit_16_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (owner)))
  **  (mutex_accept_event_frame sg entry eid current )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
|--
(mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (owner)))
  **  (mutex_accept_event_frame sg entry eid current )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_17 : OSMutexPend_partial_solve_wit_17.
Proof.
  unfold OSMutexPend_partial_solve_wit_17, OSMutexPend_partial_solve_wit_17_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40.
  assert (Hpriority_byte : curPrio node < 256) by lia.
  intros h Hheap.
  match type of Hheap with ?P h =>
    assert (Hfallback : P |-- coq_prop (mutex_priority_fallback (task_tcb64_image sg node) (curPrio node)))
      by (unfold mutex_pend_fact; entailer!)
  end.
  pose proof (Hfallback h Hheap) as Hbase.
  assert (Hspatial :
(mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  (tcb64_storage_rep (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
|--
(tcb64_storage_rep (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    cbn [coq_prop]; first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_18_pure : OSMutexPend_partial_solve_wit_18_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_18 : OSMutexPend_partial_solve_wit_18.
Proof.
  unfold OSMutexPend_partial_solve_wit_18, OSMutexPend_partial_solve_wit_18_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval_2 entered entry current m tid caller owner node retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval_2) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval_2 entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
|--
(mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (tcb64_storage_rep (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval_2) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval_2 entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_19 : OSMutexPend_partial_solve_wit_19.
Proof.
  unfold OSMutexPend_partial_solve_wit_19, OSMutexPend_partial_solve_wit_19_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42.
  unfold mutex_pend_fact; Intros.
  match goal with Hsnap : mutex_pend_owner_snapshot _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof Hsnap as [Hwait [Hm _]] end.
  destruct Hwait as [Hvalid [_ [_ [He [Htype _]]]]].
  destruct (mutex_pend_count_decode__priority_wait _ _ _ _ _ Hvalid He Htype Hm)
    as [_ [_ Hcast]].
  rewrite Hcast in *; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_20 : OSMutexPend_partial_solve_wit_20.
Proof.
  unfold OSMutexPend_partial_solve_wit_20.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (node.(curPrio) ))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((node.(curPrio) ))))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
|--
(((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((node.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((node.(curPrio) ))) 0 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (node.(curPrio) ))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((node.(curPrio) ))))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )).
  { match goal with |- context [UCharArray.full ?address 8 ?values] =>
      sep_apply_l_atomic (UCharArray.full_split_to_missing_i address
        (tcb_y_of_prio (curPrio node)) 8 values 0 ltac:(lia))
    end.
    try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_21 : OSMutexPend_partial_solve_wit_21.
Proof.
  unfold OSMutexPend_partial_solve_wit_21.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47.
  intros h Hheap.
  assert (Hspatial :
(UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (node.(curPrio) ))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((node.(curPrio) ))))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
|--
(((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((node.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((node.(curPrio) ))) 0 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (node.(curPrio) ))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((node.(curPrio) ))))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )).
  { match goal with |- context [UCharArray.full ?address 8 ?values] =>
      sep_apply_l_atomic (UCharArray.full_split_to_missing_i address
        (tcb_y_of_prio (curPrio node)) 8 values 0 ltac:(lia))
    end.
    try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_22 : OSMutexPend_partial_solve_wit_22.
Proof.
  unfold OSMutexPend_partial_solve_wit_22.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47.
  intros h Hheap.
  assert (Hspatial :
(UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (node.(curPrio) ))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((node.(curPrio) ))))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
|--
(((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((node.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((node.(curPrio) ))) 0 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (node.(curPrio) ))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((node.(curPrio) ))))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )).
  { match goal with |- context [UCharArray.full ?address 8 ?values] =>
      sep_apply_l_atomic (UCharArray.full_split_to_missing_i address
        (tcb_y_of_prio (curPrio node)) 8 values 0 ltac:(lia))
    end.
    match goal with |- context [store_uchar ?address ?value] =>
      sep_apply_l_atomic (store_uchar_undef_store_uchar address value)
    end.
    try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_23 : OSMutexPend_partial_solve_wit_23.
Proof.
  unfold OSMutexPend_partial_solve_wit_23.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47.
  intros h Hheap.
  assert (Hspatial :
(UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (node.(curPrio) ))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((node.(curPrio) ))))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
|--
(((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((node.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (Znth (tcb_y_of_prio ((node.(curPrio) ))) (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) 0))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((node.(curPrio) ))) 0 8 (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (node.(curPrio) ))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((node.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((node.(curPrio) ))))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )).
  { match goal with |- context [UCharArray.full ?address 8 ?values] =>
      sep_apply_l_atomic (UCharArray.full_split_to_missing_i address
        (tcb_y_of_prio (curPrio node)) 8 values 0 ltac:(lia))
    end.
    try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_24_pure : OSMutexPend_partial_solve_wit_24_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_24 : OSMutexPend_partial_solve_wit_24.
Proof.
  unfold OSMutexPend_partial_solve_wit_24, OSMutexPend_partial_solve_wit_24_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47.
  intros h Hheap.
  destruct (mutex_pend_priority_native_fields__entry_arithmetic
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [Hy [Hx [Hrow Hcol]]].
  assert (Hspatial :
(UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
|--
(UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )).
  { reflexivity. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_25_pure : OSMutexPend_partial_solve_wit_25_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_25 : OSMutexPend_partial_solve_wit_25.
Proof.
  unfold OSMutexPend_partial_solve_wit_25, OSMutexPend_partial_solve_wit_25_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48.
  intros h Hheap.
  destruct (mutex_pend_priority_native_fields__entry_arithmetic
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [Hy [Hx [Hrow Hcol]]].
  assert (Hspatial :
(UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
|--
(UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )).
  { reflexivity. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_26_pure : OSMutexPend_partial_solve_wit_26_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_26 : OSMutexPend_partial_solve_wit_26.
Proof.
  unfold OSMutexPend_partial_solve_wit_26, OSMutexPend_partial_solve_wit_26_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48.
  intros h Hheap.
  destruct (mutex_pend_priority_native_fields__entry_arithmetic
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [Hy [Hx [Hrow Hcol]]].
  assert (Hspatial :
(UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((node.(curPrio) ))))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
|--
(UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((node.(curPrio) ))))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )).
  { reflexivity. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_27 : OSMutexPend_partial_solve_wit_27.
Proof.
  unfold OSMutexPend_partial_solve_wit_27.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52.
  intros h Hheap.
  destruct (mutex_pend_priority_native_fields__entry_arithmetic
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [Hy [Hx [Hrow Hcol]]].
  assert (Hspatial :
(UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) )))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
|--
(((( &( "OSRdyTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)) * sizeof(UCHAR)))) # UChar  |-> (Znth (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)) (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) 0))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)) 0 8 (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) )))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )).
  { pose proof (proj2 (mutex_pend_shifted_priority_range__entry_arithmetic
      (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia))) as Hindex.
    match goal with |- context [UCharArray.full ?address 8 ?values] =>
      sep_apply_l_atomic (UCharArray.full_split_to_missing_i address
        (unsigned_last_nbits (Z.shiftr (Z.shiftr (encode_event_cnt_value current) 8) 3) 8)
        8 values 0 Hindex)
    end.
    try rewrite Hy. try rewrite Hx. try rewrite Hrow. try rewrite Hcol. try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_28 : OSMutexPend_partial_solve_wit_28.
Proof.
  unfold OSMutexPend_partial_solve_wit_28.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52.
  intros h Hheap.
  destruct (mutex_pend_priority_native_fields__entry_arithmetic
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [Hy [Hx [Hrow Hcol]]].
  assert (Hspatial :
(UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) )))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
|--
(((( &( "OSRdyTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)) * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)) 0 8 (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) )))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )).
  { pose proof (proj2 (mutex_pend_shifted_priority_range__entry_arithmetic
      (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia))) as Hindex.
    match goal with |- context [UCharArray.full ?address 8 ?values] =>
      sep_apply_l_atomic (UCharArray.full_split_to_missing_i address
        (unsigned_last_nbits (Z.shiftr (Z.shiftr (encode_event_cnt_value current) 8) 3) 8)
        8 values 0 Hindex)
    end.
    try rewrite Hy. try rewrite Hx. try rewrite Hrow. try rewrite Hcol. try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. entailer!. all: first [apply store_uchar_undef_store_uchar | apply store_ptr_undef_store_ptr]. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_29 : OSMutexPend_partial_solve_wit_29.
Proof.
  unfold OSMutexPend_partial_solve_wit_29.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52.
  intros h Hheap.
  destruct (mutex_pend_priority_native_fields__entry_arithmetic
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [Hy [Hx [Hrow Hcol]]].
  assert (Hspatial :
(UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((node.(curPrio) ))))) (8))) (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
|--
(((( &( "OSRdyTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)) * sizeof(UCHAR)))) # UChar  |-> (Znth (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)) (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) 0))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)) 0 8 (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((node.(curPrio) ))))) (8))) (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )).
  { pose proof (proj2 (mutex_pend_shifted_priority_range__entry_arithmetic
      (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia))) as Hindex.
    match goal with |- context [UCharArray.full ?address 8 ?values] =>
      sep_apply_l_atomic (UCharArray.full_split_to_missing_i address
        (unsigned_last_nbits (Z.shiftr (Z.shiftr (encode_event_cnt_value current) 8) 3) 8)
        8 values 0 Hindex)
    end.
    try rewrite Hy. try rewrite Hx. try rewrite Hrow. try rewrite Hcol. try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_30 : OSMutexPend_partial_solve_wit_30.
Proof.
  unfold OSMutexPend_partial_solve_wit_30.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52.
  intros h Hheap.
  destruct (mutex_pend_priority_native_fields__entry_arithmetic
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [Hy [Hx [Hrow Hcol]]].
  assert (Hspatial :
(UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((node.(curPrio) ))))) (8))) (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
|--
(((( &( "OSRdyTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)) * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)) 0 8 (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((node.(curPrio) ))))) (8))) (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )).
  { pose proof (proj2 (mutex_pend_shifted_priority_range__entry_arithmetic
      (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia))) as Hindex.
    match goal with |- context [UCharArray.full ?address 8 ?values] =>
      sep_apply_l_atomic (UCharArray.full_split_to_missing_i address
        (unsigned_last_nbits (Z.shiftr (Z.shiftr (encode_event_cnt_value current) 8) 3) 8)
        8 values 0 Hindex)
    end.
    try rewrite Hy. try rewrite Hx. try rewrite Hrow. try rewrite Hcol. try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. entailer!. all: first [apply store_uchar_undef_store_uchar | apply store_ptr_undef_store_ptr]. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_31 : OSMutexPend_partial_solve_wit_31.
Proof.
  unfold OSMutexPend_partial_solve_wit_31.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52.
  intros h Hheap.
  destruct (mutex_pend_priority_native_fields__entry_arithmetic
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [Hy [Hx [Hrow Hcol]]].
  assert (Hspatial :
(UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8))) ((Z.lor (unsigned_last_nbits ((Znth (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)) (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) 0)) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))) ((replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) )))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
|--
(((( &( "OSTCBPrioTbl" ) ) + ((Z.shiftr (encode_event_cnt_value (current)) 8) * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.missing_i ( &( "OSTCBPrioTbl" ) ) (Z.shiftr (encode_event_cnt_value (current)) 8) 0 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8))) ((Z.lor (unsigned_last_nbits ((Znth (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)) (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) 0)) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))) ((replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) )))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )).
  { match goal with |- context [PtrArray.full ?address 64 ?values] =>
      sep_apply_l_atomic (PtrArray.full_split_to_missing_i address
        (Z.shiftr (encode_event_cnt_value current) 8) 64 values 0 ltac:(lia))
    end.
    try rewrite Hy. try rewrite Hx. try rewrite Hrow. try rewrite Hcol. try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. entailer!. all: first [apply store_uchar_undef_store_uchar | apply store_ptr_undef_store_ptr]. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_32 : OSMutexPend_partial_solve_wit_32.
Proof.
  unfold OSMutexPend_partial_solve_wit_32.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52.
  intros h Hheap.
  destruct (mutex_pend_priority_native_fields__entry_arithmetic
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [Hy [Hx [Hrow Hcol]]].
  assert (Hspatial :
(UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8))) ((Z.lor (unsigned_last_nbits ((Znth (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)) (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) 0)) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))) ((replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((node.(curPrio) ))))) (8))) (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
|--
(((( &( "OSTCBPrioTbl" ) ) + ((Z.shiftr (encode_event_cnt_value (current)) 8) * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.missing_i ( &( "OSTCBPrioTbl" ) ) (Z.shiftr (encode_event_cnt_value (current)) 8) 0 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8))) ((Z.lor (unsigned_last_nbits ((Znth (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)) (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) 0)) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))) ((replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((node.(curPrio) ))))) (8))) (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )).
  { match goal with |- context [PtrArray.full ?address 64 ?values] =>
      sep_apply_l_atomic (PtrArray.full_split_to_missing_i address
        (Z.shiftr (encode_event_cnt_value current) 8) 64 values 0 ltac:(lia))
    end.
    try rewrite Hy. try rewrite Hx. try rewrite Hrow. try rewrite Hcol. try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. entailer!. all: first [apply store_uchar_undef_store_uchar | apply store_ptr_undef_store_ptr]. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_33 : OSMutexPend_partial_solve_wit_33.
Proof.
  unfold OSMutexPend_partial_solve_wit_33.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51.
  intros h Hheap.
  destruct (mutex_pend_priority_native_fields__entry_arithmetic
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [Hy [Hx [Hrow Hcol]]].
  assert (Hspatial :
(UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
|--
(((( &( "OSTCBPrioTbl" ) ) + ((Z.shiftr (encode_event_cnt_value (current)) 8) * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.missing_i ( &( "OSTCBPrioTbl" ) ) (Z.shiftr (encode_event_cnt_value (current)) 8) 0 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )).
  { match goal with |- context [PtrArray.full ?address 64 ?values] =>
      sep_apply_l_atomic (PtrArray.full_split_to_missing_i address
        (Z.shiftr (encode_event_cnt_value current) 8) 64 values 0 ltac:(lia))
    end.
    try rewrite Hy. try rewrite Hx. try rewrite Hrow. try rewrite Hcol. try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. entailer!. all: first [apply store_uchar_undef_store_uchar | apply store_ptr_undef_store_ptr]. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_34 : OSMutexPend_partial_solve_wit_34.
Proof.
  unfold OSMutexPend_partial_solve_wit_34, OSMutexPend_partial_solve_wit_34_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51.
  intros h Hheap.
  destruct (mutex_pend_priority_native_fields__entry_arithmetic
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [Hy [Hx [Hrow Hcol]]].
  assert (Hspatial :
(PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth ((Z.shiftr (encode_event_cnt_value (current)) 8)) ((task_slot_addr (sg) (owner))) ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
|--
(mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio ((Z.shiftr (encode_event_cnt_value (current)) 8))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((Z.shiftr (encode_event_cnt_value (current)) 8))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((Z.shiftr (encode_event_cnt_value (current)) 8))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((Z.shiftr (encode_event_cnt_value (current)) 8))))
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth ((Z.shiftr (encode_event_cnt_value (current)) 8)) ((task_slot_addr (sg) (owner))) ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )).
  { try rewrite Hy. try rewrite Hx. try rewrite Hrow. try rewrite Hcol. try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_35 : OSMutexPend_partial_solve_wit_35.
Proof.
  unfold OSMutexPend_partial_solve_wit_35, OSMutexPend_partial_solve_wit_35_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52.
  intros h Hheap.
  destruct (mutex_pend_priority_native_fields__entry_arithmetic
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [Hy [Hx [Hrow Hcol]]].
  assert (Hspatial :
(PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth ((Z.shiftr (encode_event_cnt_value (current)) 8)) ((task_slot_addr (sg) (owner))) ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8))) ((Z.lor (unsigned_last_nbits ((Znth (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)) (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) 0)) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))) ((replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((node.(curPrio) ))))) (8))) (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
|--
(mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio ((Z.shiftr (encode_event_cnt_value (current)) 8))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((Z.shiftr (encode_event_cnt_value (current)) 8))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((Z.shiftr (encode_event_cnt_value (current)) 8))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((Z.shiftr (encode_event_cnt_value (current)) 8))))
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth ((Z.shiftr (encode_event_cnt_value (current)) 8)) ((task_slot_addr (sg) (owner))) ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8))) ((Z.lor (unsigned_last_nbits ((Znth (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)) (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) 0)) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))) ((replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))))) )
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((node.(curPrio) ))))) (8))) (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )).
  { try rewrite Hy. try rewrite Hx. try rewrite Hrow. try rewrite Hcol. try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_36 : OSMutexPend_partial_solve_wit_36.
Proof.
  unfold OSMutexPend_partial_solve_wit_36, OSMutexPend_partial_solve_wit_36_aux.
  intros H_pure.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52.
  intros h Hheap.
  destruct (mutex_pend_priority_native_fields__entry_arithmetic
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [Hy [Hx [Hrow Hcol]]].
  assert (Hspatial :
(PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth ((Z.shiftr (encode_event_cnt_value (current)) 8)) ((task_slot_addr (sg) (owner))) ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8))) ((Z.lor (unsigned_last_nbits ((Znth (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)) (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) 0)) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))) ((replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8)))
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) )))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
|--
(mutex_pend_owner_fields_rest (task_slot_addr (sg) (owner)) (task_tcb64_image (sg) (node)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (Z.shiftr (encode_event_cnt_value (current)) 8))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio ((Z.shiftr (encode_event_cnt_value (current)) 8))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((Z.shiftr (encode_event_cnt_value (current)) 8))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((Z.shiftr (encode_event_cnt_value (current)) 8))))
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((Z.shiftr (encode_event_cnt_value (current)) 8))))
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth ((Z.shiftr (encode_event_cnt_value (current)) 8)) ((task_slot_addr (sg) (owner))) ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8))) ((Z.lor (unsigned_last_nbits ((Znth (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)) (replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))) 0)) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr (encode_event_cnt_value (current)) 8) 7))) (8)))) ((replace_Znth ((tcb_y_of_prio ((node.(curPrio) )))) ((Z.land (Znth (tcb_y_of_prio ((node.(curPrio) ))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((node.(curPrio) ))))) (8)))) ((sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))))))) )
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) )))) (8)) (unsigned_last_nbits ((Z.shiftl 1 (unsigned_last_nbits ((Z.shiftr (Z.shiftr (encode_event_cnt_value (current)) 8) 3)) (8)))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )).
  { try rewrite Hy. try rewrite Hx. try rewrite Hrow. try rewrite Hcol. try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_37 : OSMutexPend_partial_solve_wit_37.
Proof.
  unfold OSMutexPend_partial_solve_wit_37.
  intros perr_pre timeout_pre pevent_pre X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned retval entered entry current m tid caller owner node retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (node.(curPrio) ))
  **  (tcb64_storage_without (task_slot_addr (sg) (owner)) TCBPrio (task_tcb64_image (sg) (node)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
|--
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr (encode_event_cnt_value (current)) 8)) (8)) * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.missing_i ( &( "OSTCBPrioTbl" ) ) (unsigned_last_nbits ((Z.shiftr (encode_event_cnt_value (current)) 8)) (8)) 0 64 (mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) ))) )
  **  (mutex_pend_fact (mutex_pend_owner_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (owner) (node)) )
  **  (mutex_pend_fact (mutex_base_priority_result ((mutex_del_priority_values (sg) (((entry.(TskState) ).(prioTbl) )))) ((task_slot_addr (sg) (owner))) ((node.(curPrio) )) (retval_2)) )
  **  (mutex_pend_fact (task_base_priority (sg) (((entry.(TskState) ).(prioTbl) )) (owner) (retval_2)) )
  **  ((&(((task_slot_addr (sg) (owner)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (node.(curPrio) ))
  **  (tcb64_storage_without (task_slot_addr (sg) (owner)) TCBPrio (task_tcb64_image (sg) (node)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_priority_fallback ((task_tcb64_image (sg) (node))) ((node.(curPrio) ))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (caller.(curPrio) ))
  **  (mutex_pend_caller_priority_frame sg entry owner tid caller )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (entry) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (retval) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_task_entry (idle) (entered) (entry)) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (entry)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered retval entry entry )
  **  (mutex_pend_fact (kernel_call_task_source (context) (before)) )
  **  (mutex_pend_fact (valid_event_id (sg) (eid)) )
  **  (mutex_pend_fact (sem_query_public_slot (before) (eid) (observed)) )
  **  ((pd) # UChar  |->_)
  **  (mutex_pend_fact (sem_pend_profile (sg)) )).
  { match goal with |- context [PtrArray.full ?address 64 ?values] =>
      sep_apply_l_atomic (PtrArray.full_split_to_missing_i address
        (unsigned_last_nbits (Z.shiftr (encode_event_cnt_value current) 8) 8)
        64 values 0 ltac:(lia))
    end.
    match goal with |- context [store_ptr ?address ?value] =>
      sep_apply_l_atomic (store_ptr_undef_store_ptr address value)
    end.
    try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_38_pure : OSMutexPend_partial_solve_wit_38_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_38 : OSMutexPend_partial_solve_wit_38.
Proof.
  unfold OSMutexPend_partial_solve_wit_38, OSMutexPend_partial_solve_wit_38_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr PreH1 PreH2 PreH3 PreH4 PreH5 PreH6.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered cpu_sr entry inherited )
  **  (UCOS2_inv sg inherited )
  **  ((pd) # UChar  |->_)
|--
(mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (UCOS2_inv sg inherited )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered cpu_sr entry inherited )
  **  ((pd) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_39 : OSMutexPend_partial_solve_wit_39.
Proof.
  unfold OSMutexPend_partial_solve_wit_39, OSMutexPend_partial_solve_wit_39_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9.
  intros h Hheap.
  match type of Hheap with ?P h =>
    assert (Haddresses : P |-- coq_prop (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ))
      by (unfold mutex_pend_fact; entailer!)
  end.
  pose proof (Haddresses h Hheap) as Hglobals.
  change (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) in Hglobals.
  unfold os_sched_global_addresses, sched_new_global_addresses in Hglobals.
  decompose [and] Hglobals.
  assert (Hspatial :
(mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((caller.(stat) ))) 16))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> ticks)
  **  (sem_pend_prefix_frame sg inherited tid caller )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered cpu_sr entry inherited )
  **  ((pd) # UChar  |->_)
|--
(mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (encode_task_status ((caller.(stat) ))) 16))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> ticks)
  **  (sem_pend_prefix_frame sg inherited tid caller )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered cpu_sr entry inherited )
  **  ((pd) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_40_pure : OSMutexPend_partial_solve_wit_40_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_40 : OSMutexPend_partial_solve_wit_40.
Proof.
  unfold OSMutexPend_partial_solve_wit_40, OSMutexPend_partial_solve_wit_40_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> ((caller.(curPrio) ) ÷ 8 ))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((caller.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((caller.(curPrio) ))))
  **  (((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (((caller.(curPrio) ) ÷ 8 ) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((current.(waitList) )) ((inherited.(TskState) )) (((caller.(curPrio) ) ÷ 8 ))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((current.(waitList) )) ((inherited.(TskState) ))))
  **  (((( &( "OSRdyTbl" ) ) + (((caller.(curPrio) ) ÷ 8 ) * sizeof(UCHAR)))) # UChar  |-> (encode_ready_tbl_at_or (((inherited.(SchedState) ).(readyList) )) ((inherited.(TskState) )) (((caller.(curPrio) ) ÷ 8 ))))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((inherited.(SchedState) ).(readyList) )) ((inherited.(TskState) ))))
  **  (mutex_pend_wait_call_frame sg inherited eid current tid caller ticks )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered cpu_sr entry inherited )
  **  ((pd) # UChar  |->_)
|--
((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> ((caller.(curPrio) ) ÷ 8 ))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((caller.(curPrio) ))))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((caller.(curPrio) ))))
  **  (((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (((caller.(curPrio) ) ÷ 8 ) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((current.(waitList) )) ((inherited.(TskState) )) (((caller.(curPrio) ) ÷ 8 ))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((current.(waitList) )) ((inherited.(TskState) ))))
  **  (((( &( "OSRdyTbl" ) ) + (((caller.(curPrio) ) ÷ 8 ) * sizeof(UCHAR)))) # UChar  |-> (encode_ready_tbl_at_or (((inherited.(SchedState) ).(readyList) )) ((inherited.(TskState) )) (((caller.(curPrio) ) ÷ 8 ))))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((inherited.(SchedState) ).(readyList) )) ((inherited.(TskState) ))))
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_wait_call_frame sg inherited eid current tid caller ticks )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered cpu_sr entry inherited )
  **  ((pd) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_41 : OSMutexPend_partial_solve_wit_41.
Proof.
  unfold OSMutexPend_partial_solve_wit_41, OSMutexPend_partial_solve_wit_41_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11.
  intros h Hheap.
  match type of Hheap with ?P h =>
    assert (Haddresses : P |-- coq_prop (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ))
      by (unfold mutex_pend_fact; entailer!)
  end.
  pose proof (Haddresses h Hheap) as Hglobals.
  change (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) in Hglobals.
  unfold os_sched_global_addresses, sched_new_global_addresses in Hglobals.
  decompose [and] Hglobals.
  assert (Hspatial :
(event_task_wait_post ( &( "OSTCBCur" ) ) (task_slot_addr (sg) (tid)) pe ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ((caller.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((caller.(curPrio) ))) (tcb_bit_y_of_prio ((caller.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((inherited.(TskState) )) (((caller.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((inherited.(TskState) ))) (encode_ready_tbl_at_or (((inherited.(SchedState) ).(readyList) )) ((inherited.(TskState) )) (((caller.(curPrio) ) ÷ 8 ))) (encode_ready_grp (((inherited.(SchedState) ).(readyList) )) ((inherited.(TskState) ))) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_wait_call_frame sg inherited eid current tid caller ticks )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered cpu_sr entry inherited )
  **  ((pd) # UChar  |->_)
|--
(mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg entered cpu_sr entry inherited )
  **  (event_task_wait_post ( &( "OSTCBCur" ) ) (task_slot_addr (sg) (tid)) pe ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ((caller.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((caller.(curPrio) ))) (tcb_bit_y_of_prio ((caller.(curPrio) ))) (encode_event_wait_tbl_at_or ((current.(waitList) )) ((inherited.(TskState) )) (((caller.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((current.(waitList) )) ((inherited.(TskState) ))) (encode_ready_tbl_at_or (((inherited.(SchedState) ).(readyList) )) ((inherited.(TskState) )) (((caller.(curPrio) ) ÷ 8 ))) (encode_ready_grp (((inherited.(SchedState) ).(readyList) )) ((inherited.(TskState) ))) )
  **  (mutex_pend_wait_call_frame sg inherited eid current tid caller ticks )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_42_pure : OSMutexPend_partial_solve_wit_42_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_42 : OSMutexPend_partial_solve_wit_42.
Proof.
  unfold OSMutexPend_partial_solve_wit_42, OSMutexPend_partial_solve_wit_42_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) (waiting) (entered) (waiting)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) (waiting)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (waiting)) )
  **  (mutex_pend_api_restore_input true owned critical saved_local sg entered cpu_sr entry waiting )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)
|--
(mutex_pend_api_restore_input true owned critical saved_local sg entered cpu_sr entry (event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) (waiting) (entered) (waiting)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) (waiting)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (waiting)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_43_pure : OSMutexPend_partial_solve_wit_43_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_43 : OSMutexPend_partial_solve_wit_43.
Proof.
  unfold OSMutexPend_partial_solve_wit_43, OSMutexPend_partial_solve_wit_43_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_api_restore_output true owned critical saved_local sg entered cpu_sr (event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) (waiting) (entered) (waiting)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) (waiting)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (waiting)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)
|--
(mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_api_restore_output true owned critical saved_local sg entered cpu_sr (event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_44 : OSMutexPend_partial_solve_wit_44.
Proof.
  unfold OSMutexPend_partial_solve_wit_44, OSMutexPend_partial_solve_wit_44_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12.
  intros h Hheap.
  match type of Hheap with ?P h =>
    assert (Haddresses : P |-- coq_prop (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ))
      by (unfold mutex_pend_fact; entailer!)
  end.
  pose proof (Haddresses h Hheap) as Hglobals.
  change (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) in Hglobals.
  assert (Hspatial :
(mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_continuation_phase_sched_input (MutexPendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) external platform environment critical saved_local sg released mask unmasked )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)
|--
(mutex_pend_continuation_phase_sched_input (MutexPendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg released mask unmasked )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_45_pure : OSMutexPend_partial_solve_wit_45_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_45 : OSMutexPend_partial_solve_wit_45.
Proof.
  unfold OSMutexPend_partial_solve_wit_45, OSMutexPend_partial_solve_wit_45_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_continuation_phase_sched_output (MutexPendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) (task_stack_call_external (owned)) (task_stack_call_platform (owned)) (Some (owned)) critical saved_local sg released mask unmasked )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)
|--
(mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_continuation_phase_sched_output (MutexPendWaitPhase (context) (mask) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) external platform environment critical saved_local sg released mask unmasked )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_46 : OSMutexPend_partial_solve_wit_46.
Proof.
  unfold OSMutexPend_partial_solve_wit_46.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (task_tcb_init_continuation_save_input owned critical saved_local sg scheduled mask selected )
  **  (unmap_table_rep sg )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)
|--
(task_tcb_init_continuation_save_input owned critical saved_local sg scheduled mask selected )
  **  (unmap_table_rep sg )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_47_pure : OSMutexPend_partial_solve_wit_47_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_47 : OSMutexPend_partial_solve_wit_47.
Proof.
  unfold OSMutexPend_partial_solve_wit_47, OSMutexPend_partial_solve_wit_47_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_api_save_output owned critical saved_local sg scheduled mask retval selected )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)
|--
(mutex_pend_api_save_output owned critical saved_local sg scheduled mask retval selected )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_48_pure : OSMutexPend_partial_solve_wit_48_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_48 : OSMutexPend_partial_solve_wit_48.
Proof.
  unfold OSMutexPend_partial_solve_wit_48, OSMutexPend_partial_solve_wit_48_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval resume_tid node resumed resume_entry PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  (sem_pend_cleanup_frame sg resume_entry resume_tid node )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |-> 0)
|--
(mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  (sem_pend_cleanup_frame sg resume_entry resume_tid node )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |-> 0)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_49_pure : OSMutexPend_partial_solve_wit_49_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_49 : OSMutexPend_partial_solve_wit_49.
Proof.
  unfold OSMutexPend_partial_solve_wit_49, OSMutexPend_partial_solve_wit_49_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval resume_tid node resumed resume_entry PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  (sem_pend_cleanup_frame sg resume_entry resume_tid node )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |-> 14)
|--
(mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  (sem_pend_cleanup_frame sg resume_entry resume_tid node )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |-> 14)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_50_pure : OSMutexPend_partial_solve_wit_50_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_50 : OSMutexPend_partial_solve_wit_50.
Proof.
  unfold OSMutexPend_partial_solve_wit_50, OSMutexPend_partial_solve_wit_50_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval resume_tid node resumed resume_entry linked PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17.
  intros h Hheap.
  assert (Hspatial :
(event_task_remove_post (task_slot_addr (sg) (resume_tid)) &((pe)  # "os_event" ->ₛ "OSEventGrp") &((pe)  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((linked.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((linked.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_query_lookup (resume_entry) (eid) (linked)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (sem_pend_remove_call_frame sg resume_entry eid linked resume_tid node )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry resume_entry )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)
|--
(mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_query_lookup (resume_entry) (eid) (linked)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (event_task_remove_post (task_slot_addr (sg) (resume_tid)) &((pe)  # "os_event" ->ₛ "OSEventGrp") &((pe)  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((linked.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((linked.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (sem_pend_remove_call_frame sg resume_entry eid linked resume_tid node )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_51_pure : OSMutexPend_partial_solve_wit_51_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_51 : OSMutexPend_partial_solve_wit_51.
Proof.
  unfold OSMutexPend_partial_solve_wit_51, OSMutexPend_partial_solve_wit_51_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval resume_tid node resumed resume_entry linked PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17.
  intros h Hheap.
  assert (Hspatial :
(event_task_remove_post (task_slot_addr (sg) (resume_tid)) &((pe)  # "os_event" ->ₛ "OSEventGrp") &((pe)  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((linked.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((linked.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_query_lookup (resume_entry) (eid) (linked)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (sem_pend_remove_call_frame sg resume_entry eid linked resume_tid node )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry resume_entry )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)
|--
(mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_query_lookup (resume_entry) (eid) (linked)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (event_task_remove_post (task_slot_addr (sg) (resume_tid)) &((pe)  # "os_event" ->ₛ "OSEventGrp") &((pe)  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((linked.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((linked.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (sem_pend_remove_call_frame sg resume_entry eid linked resume_tid node )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_52 : OSMutexPend_partial_solve_wit_52.
Proof.
  unfold OSMutexPend_partial_solve_wit_52.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval resume_tid node resumed resume_entry linked PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_query_lookup (resume_entry) (eid) (linked)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (event_task_remove_pre (task_slot_addr (sg) (resume_tid)) &((pe)  # "os_event" ->ₛ "OSEventGrp") &((pe)  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((linked.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((linked.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (sem_pend_remove_call_frame sg resume_entry eid linked resume_tid node )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry resume_entry )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)
|--
(event_task_remove_pre (task_slot_addr (sg) (resume_tid)) &((pe)  # "os_event" ->ₛ "OSEventGrp") &((pe)  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((linked.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((linked.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_query_lookup (resume_entry) (eid) (linked)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (sem_pend_remove_call_frame sg resume_entry eid linked resume_tid node )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry resume_entry )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_53 : OSMutexPend_partial_solve_wit_53.
Proof.
  unfold OSMutexPend_partial_solve_wit_53.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval resume_tid node resumed resume_entry linked PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_query_lookup (resume_entry) (eid) (linked)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (event_task_remove_pre (task_slot_addr (sg) (resume_tid)) &((pe)  # "os_event" ->ₛ "OSEventGrp") &((pe)  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((linked.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((linked.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (sem_pend_remove_call_frame sg resume_entry eid linked resume_tid node )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry resume_entry )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)
|--
(event_task_remove_pre (task_slot_addr (sg) (resume_tid)) &((pe)  # "os_event" ->ₛ "OSEventGrp") &((pe)  # "os_event" ->ₛ "OSEventTbl") ((node.(curPrio) ) ÷ 8 ) (tcb_bit_x_of_prio ((node.(curPrio) ))) (tcb_bit_y_of_prio ((node.(curPrio) ))) (encode_event_wait_tbl_at_or ((linked.(waitList) )) ((resume_entry.(TskState) )) (((node.(curPrio) ) ÷ 8 ))) (encode_event_wait_grp ((linked.(waitList) )) ((resume_entry.(TskState) ))) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_query_lookup (resume_entry) (eid) (linked)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  (sem_pend_remove_call_frame sg resume_entry eid linked resume_tid node )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry resume_entry )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_54_pure : OSMutexPend_partial_solve_wit_54_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_54 : OSMutexPend_partial_solve_wit_54.
Proof.
  unfold OSMutexPend_partial_solve_wit_54, OSMutexPend_partial_solve_wit_54_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval resume_tid node resumed resume_entry PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  (sem_pend_cleanup_frame sg resume_entry resume_tid node )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)
|--
(mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  (sem_pend_cleanup_frame sg resume_entry resume_tid node )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry resume_entry )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_55_pure : OSMutexPend_partial_solve_wit_55_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_55 : OSMutexPend_partial_solve_wit_55.
Proof.
  unfold OSMutexPend_partial_solve_wit_55, OSMutexPend_partial_solve_wit_55_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval resume_tid node resumed resume_entry PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry resume_entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  (sem_pend_cleanup_frame sg resume_entry resume_tid node )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)
|--
(mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((node.(stat) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((node.(statPend) ))))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> (encode_event_link (sg) ((node.(eventPtr) ))))
  **  (sem_pend_cleanup_frame sg resume_entry resume_tid node )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry resume_entry )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_56_pure : OSMutexPend_partial_solve_wit_56_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_56 : OSMutexPend_partial_solve_wit_56.
Proof.
  unfold OSMutexPend_partial_solve_wit_56, OSMutexPend_partial_solve_wit_56_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval resume_tid node resumed resume_entry linked cleaning clean_node PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_query_lookup (resume_entry) (eid) (linked)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (10) (cleaning) (resume_tid) (clean_node)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry cleaning )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  (sem_pend_cleanup_frame sg cleaning resume_tid clean_node )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |-> 10)
|--
(mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (10) (cleaning) (resume_tid) (clean_node)) )
  **  ((pd) # UChar  |-> 10)
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry cleaning )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  (sem_pend_cleanup_frame sg cleaning resume_tid clean_node )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_query_lookup (resume_entry) (eid) (linked)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_57_pure : OSMutexPend_partial_solve_wit_57_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_57 : OSMutexPend_partial_solve_wit_57.
Proof.
  unfold OSMutexPend_partial_solve_wit_57, OSMutexPend_partial_solve_wit_57_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval resume_tid node resumed resume_entry linked cleaning clean_node PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_query_lookup (resume_entry) (eid) (linked)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (10) (cleaning) (resume_tid) (clean_node)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry cleaning )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  (sem_pend_cleanup_frame sg cleaning resume_tid clean_node )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |-> 10)
|--
(mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (10) (cleaning) (resume_tid) (clean_node)) )
  **  ((pd) # UChar  |-> 10)
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry cleaning )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  (sem_pend_cleanup_frame sg cleaning resume_tid clean_node )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_query_lookup (resume_entry) (eid) (linked)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_58_pure : OSMutexPend_partial_solve_wit_58_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_58 : OSMutexPend_partial_solve_wit_58.
Proof.
  unfold OSMutexPend_partial_solve_wit_58, OSMutexPend_partial_solve_wit_58_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval resume_tid node resumed resume_entry cleaning clean_node PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (14) (cleaning) (resume_tid) (clean_node)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry cleaning )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  (sem_pend_cleanup_frame sg cleaning resume_tid clean_node )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |-> 14)
|--
(mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (14) (cleaning) (resume_tid) (clean_node)) )
  **  ((pd) # UChar  |-> 14)
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry cleaning )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  (sem_pend_cleanup_frame sg cleaning resume_tid clean_node )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_59_pure : OSMutexPend_partial_solve_wit_59_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_59 : OSMutexPend_partial_solve_wit_59.
Proof.
  unfold OSMutexPend_partial_solve_wit_59, OSMutexPend_partial_solve_wit_59_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval resume_tid node resumed resume_entry cleaning clean_node PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (0) (cleaning) (resume_tid) (clean_node)) )
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry cleaning )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  (sem_pend_cleanup_frame sg cleaning resume_tid clean_node )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
  **  ((pd) # UChar  |-> 0)
|--
(mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (0) (cleaning) (resume_tid) (clean_node)) )
  **  ((pd) # UChar  |-> 0)
  **  (mutex_pend_masked_frame owned critical saved_local sg resumed retval resume_entry cleaning )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (resume_tid)))
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((task_slot_addr (sg) (resume_tid)))  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  (sem_pend_cleanup_frame sg cleaning resume_tid clean_node )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_60_pure : OSMutexPend_partial_solve_wit_60_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_60 : OSMutexPend_partial_solve_wit_60.
Proof.
  unfold OSMutexPend_partial_solve_wit_60, OSMutexPend_partial_solve_wit_60_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval resume_tid node resumed resume_entry cleaning clean_node cleaned code PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (code) (cleaning) (resume_tid) (clean_node)) )
  **  (mutex_pend_fact (mutex_pend_resume_result (sg) (eid) (resume_entry) (code) (cleaned)) )
  **  ((pd) # UChar  |-> code)
  **  (mutex_pend_api_restore_input false owned critical saved_local sg resumed retval resume_entry cleaned )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
|--
(mutex_pend_api_restore_input false owned critical saved_local sg resumed retval resume_entry cleaned )
  **  (mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (code) (cleaning) (resume_tid) (clean_node)) )
  **  (mutex_pend_fact (mutex_pend_resume_result (sg) (eid) (resume_entry) (code) (cleaned)) )
  **  ((pd) # UChar  |-> code)
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_61_pure : OSMutexPend_partial_solve_wit_61_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_61 : OSMutexPend_partial_solve_wit_61.
Proof.
  unfold OSMutexPend_partial_solve_wit_61, OSMutexPend_partial_solve_wit_61_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval resume_tid node resumed resume_entry cleaning clean_node cleaned code PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (code) (cleaning) (resume_tid) (clean_node)) )
  **  (mutex_pend_fact (mutex_pend_resume_result (sg) (eid) (resume_entry) (code) (cleaned)) )
  **  ((pd) # UChar  |-> code)
  **  (mutex_pend_api_restore_input false owned critical saved_local sg resumed retval resume_entry cleaned )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
|--
(mutex_pend_api_restore_input false owned critical saved_local sg resumed retval resume_entry cleaned )
  **  (mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (code) (cleaning) (resume_tid) (clean_node)) )
  **  (mutex_pend_fact (mutex_pend_resume_result (sg) (eid) (resume_entry) (code) (cleaned)) )
  **  ((pd) # UChar  |-> code)
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_62_pure : OSMutexPend_partial_solve_wit_62_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_62 : OSMutexPend_partial_solve_wit_62.
Proof.
  unfold OSMutexPend_partial_solve_wit_62, OSMutexPend_partial_solve_wit_62_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval resume_tid node resumed resume_entry linked cleaning clean_node cleaned code PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (code) (cleaning) (resume_tid) (clean_node)) )
  **  (mutex_pend_fact (mutex_pend_resume_result (sg) (eid) (resume_entry) (code) (cleaned)) )
  **  ((pd) # UChar  |-> code)
  **  (mutex_pend_api_restore_input false owned critical saved_local sg resumed retval resume_entry cleaned )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_query_lookup (resume_entry) (eid) (linked)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
|--
(mutex_pend_api_restore_input false owned critical saved_local sg resumed retval resume_entry cleaned )
  **  (mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (code) (cleaning) (resume_tid) (clean_node)) )
  **  (mutex_pend_fact (mutex_pend_resume_result (sg) (eid) (resume_entry) (code) (cleaned)) )
  **  ((pd) # UChar  |-> code)
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_query_lookup (resume_entry) (eid) (linked)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_63_pure : OSMutexPend_partial_solve_wit_63_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_63 : OSMutexPend_partial_solve_wit_63.
Proof.
  unfold OSMutexPend_partial_solve_wit_63, OSMutexPend_partial_solve_wit_63_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval resume_tid node resumed resume_entry linked cleaning clean_node cleaned code PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (code) (cleaning) (resume_tid) (clean_node)) )
  **  (mutex_pend_fact (mutex_pend_resume_result (sg) (eid) (resume_entry) (code) (cleaned)) )
  **  ((pd) # UChar  |-> code)
  **  (mutex_pend_api_restore_input false owned critical saved_local sg resumed retval resume_entry cleaned )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_query_lookup (resume_entry) (eid) (linked)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
|--
(mutex_pend_api_restore_input false owned critical saved_local sg resumed retval resume_entry cleaned )
  **  (mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (code) (cleaning) (resume_tid) (clean_node)) )
  **  (mutex_pend_fact (mutex_pend_resume_result (sg) (eid) (resume_entry) (code) (cleaned)) )
  **  ((pd) # UChar  |-> code)
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_query_lookup (resume_entry) (eid) (linked)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_64_pure : OSMutexPend_partial_solve_wit_64_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_64 : OSMutexPend_partial_solve_wit_64.
Proof.
  unfold OSMutexPend_partial_solve_wit_64, OSMutexPend_partial_solve_wit_64_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval resume_tid node resumed resume_entry linked cleaning clean_node cleaned code PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_api_restore_output false owned critical saved_local sg resumed retval cleaned )
  **  (mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (code) (cleaning) (resume_tid) (clean_node)) )
  **  (mutex_pend_fact (mutex_pend_resume_result (sg) (eid) (resume_entry) (code) (cleaned)) )
  **  ((pd) # UChar  |-> code)
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_query_lookup (resume_entry) (eid) (linked)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
|--
(mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (mutex_pend_resume_result (sg) (eid) (resume_entry) (code) (cleaned)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  ((pd) # UChar  |-> code)
  **  (mutex_pend_api_restore_output false owned critical saved_local sg resumed retval cleaned )
  **  (mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (code) (cleaning) (resume_tid) (clean_node)) )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_query_lookup (resume_entry) (eid) (linked)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_65_pure : OSMutexPend_partial_solve_wit_65_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_65 : OSMutexPend_partial_solve_wit_65.
Proof.
  unfold OSMutexPend_partial_solve_wit_65, OSMutexPend_partial_solve_wit_65_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval resume_tid node resumed resume_entry linked cleaning clean_node cleaned code PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_api_restore_output false owned critical saved_local sg resumed retval cleaned )
  **  (mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (code) (cleaning) (resume_tid) (clean_node)) )
  **  (mutex_pend_fact (mutex_pend_resume_result (sg) (eid) (resume_entry) (code) (cleaned)) )
  **  ((pd) # UChar  |-> code)
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_query_lookup (resume_entry) (eid) (linked)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
|--
(mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (mutex_pend_resume_result (sg) (eid) (resume_entry) (code) (cleaned)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  ((pd) # UChar  |-> code)
  **  (mutex_pend_api_restore_output false owned critical saved_local sg resumed retval cleaned )
  **  (mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (code) (cleaning) (resume_tid) (clean_node)) )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_query_lookup (resume_entry) (eid) (linked)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_66_pure : OSMutexPend_partial_solve_wit_66_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_66 : OSMutexPend_partial_solve_wit_66.
Proof.
  unfold OSMutexPend_partial_solve_wit_66, OSMutexPend_partial_solve_wit_66_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval resume_tid node resumed resume_entry cleaning clean_node cleaned code PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_api_restore_output false owned critical saved_local sg resumed retval cleaned )
  **  (mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (code) (cleaning) (resume_tid) (clean_node)) )
  **  (mutex_pend_fact (mutex_pend_resume_result (sg) (eid) (resume_entry) (code) (cleaned)) )
  **  ((pd) # UChar  |-> code)
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
|--
(mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (mutex_pend_resume_result (sg) (eid) (resume_entry) (code) (cleaned)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  ((pd) # UChar  |-> code)
  **  (mutex_pend_api_restore_output false owned critical saved_local sg resumed retval cleaned )
  **  (mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (code) (cleaning) (resume_tid) (clean_node)) )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_67_pure : OSMutexPend_partial_solve_wit_67_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexPend_partial_solve_wit_67 : OSMutexPend_partial_solve_wit_67.
Proof.
  unfold OSMutexPend_partial_solve_wit_67, OSMutexPend_partial_solve_wit_67_aux.
  intros H_pure.
  intros X ticks pd pe observed eid before mask idle saved_local environment context sg critical platform external owned entered entry inherited current m tid caller cpu_sr waiting released unmasked scheduled selected retval resume_tid node resumed resume_entry cleaning clean_node cleaned code PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14.
  intros h Hheap.
  assert (Hspatial :
(mutex_pend_api_restore_output false owned critical saved_local sg resumed retval cleaned )
  **  (mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (code) (cleaning) (resume_tid) (clean_node)) )
  **  (mutex_pend_fact (mutex_pend_resume_result (sg) (eid) (resume_entry) (code) (cleaned)) )
  **  ((pd) # UChar  |-> code)
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )
|--
(mutex_pend_fact (mutex_pend_api_prefix (pe) (before) (eid)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (context) (before) (entered) (entry)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_sched_return (environment) (critical) (sg) (released) (unmasked) (scheduled) (selected)) )
  **  (mutex_pend_fact (sem_pend_modular_call_history (owned) (critical) (sg) (scheduled) (selected) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (mutex_pend_resume_result (sg) (eid) (resume_entry) (code) (cleaned)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (retval)) )
  **  ((pd) # UChar  |-> code)
  **  (mutex_pend_api_restore_output false owned critical saved_local sg resumed retval cleaned )
  **  (mutex_pend_fact (mutex_pend_cleanup_observation (sg) (resume_entry) (eid) (code) (cleaning) (resume_tid) (clean_node)) )
  **  (mutex_pend_fact (sem_pend_resume_entry (sg) (resume_entry) (eid) (resume_tid) (node)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (scheduled) (selected)) )
  **  (mutex_pend_fact (mutex_pend_api_scope (environment) (critical) (sg) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (mutex_pend_wait_selected_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (resumed) (resume_entry)) )
  **  (mutex_pend_fact (interrupt_saved_value (mask) (cpu_sr)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (entered) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks)))) )
  **  (mutex_pend_fact (kernel_tcb_stack_field_layout (sg)) )
  **  (mutex_pend_fact (mutex_pend_wait_at (sg) (context) (entry) (current) (eid) (ticks) ((event_pend_state (sg) (inherited) (eid) (current) (tid) (caller) (PendMutex) (ticks))) (released) (unmasked)) )
  **  (mutex_pend_fact (sem_pend_wait_sched_entry (sg) (released) (unmasked)) )
  **  (mutex_pend_fact (mutex_pend_first_snapshot (owned) (critical) (sg) (idle) (context) (entered) (mask) (cpu_sr) (before) (entry) (eid) (observed) (current) (m) (tid) (caller)) )
  **  (mutex_pend_fact (mutex_pend_inherited_snapshot (sg) (entry) (eid) (current) (m) (tid) (caller) (inherited)) )
  **  (mutex_pend_fact (kernel_call_task_source (entered) (inherited)) )
  **  (mutex_pend_fact (sched_current_consistency ((inherited.(TskState) )) ((inherited.(SchedState) ))) )
  **  (mutex_pend_fact (sem_pend_blocking_call_stage (sg) (entered) (inherited)) )
  **  (mutex_pend_fact (mutex_pend_wait_entry (sg) (inherited) (eid) (current) (tid) (caller)) )
  **  (mutex_pend_fact (sem_pend_profile (sg)) )
  **  (mutex_pend_fact (mutex_pend_api_input (critical) (sg) ((os_sched_call_invocation (context))) (pe) (before) (eid) (observed)) )
  **  (mutex_pend_fact (mutex_pend_api_admission (environment) (idle) (context) (pe) (before) (eid)) )
  **  (mutex_pend_fact (UCOS2_state_inv (sg) (before)) )
  **  (mutex_pend_fact (event_object_layout_prop (sg) (eid)) )
  **  (mutex_pend_fact (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_pend_fact (os_sched_global_addresses (sg) (( &( "OSIntNesting" ) )) (( &( "OSLockNesting" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSPrioCur" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) )) (( &( "OSCtxSwCtr" ) )) (( &( "OSUnMapTbl" ) )) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) ))) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    match goal with |- coq_prop ?P _ => change P end;
    first [assumption | reflexivity | congruence | lia].
Qed. 

