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
From Ucos2Verify.VC.code.mutex Require Import accept_return_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_accept_return_spec.
Local Open Scope sac.

Lemma proof_of_OSMutexAccept_safety_wit_1 : OSMutexAccept_safety_wit_1.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexAccept_safety_wit_2 : OSMutexAccept_safety_wit_2.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexAccept_safety_wit_3 : OSMutexAccept_safety_wit_3.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexAccept_safety_wit_4 : OSMutexAccept_safety_wit_4.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexAccept_safety_wit_6 : OSMutexAccept_safety_wit_6.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexAccept_safety_wit_7 : OSMutexAccept_safety_wit_7.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexAccept_safety_wit_8 : OSMutexAccept_safety_wit_8.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexAccept_safety_wit_9 : OSMutexAccept_safety_wit_9.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_1_pure : OSMutexAccept_partial_solve_wit_1_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_1 : OSMutexAccept_partial_solve_wit_1.
Proof.
  unfold OSMutexAccept_partial_solve_wit_1, OSMutexAccept_partial_solve_wit_1_aux.
  intros H_pure.
  intros perr_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform context saved_local environment PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7.
  intros h Hheap.
  assert (Hspatial :
((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (mutex_accept_closed platform critical sg invocation origin mask before )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_2 : OSMutexAccept_partial_solve_wit_2.
Proof.
  unfold OSMutexAccept_partial_solve_wit_2.
  intros perr_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform context saved_local environment PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
(coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_3_pure : OSMutexAccept_partial_solve_wit_3_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_3 : OSMutexAccept_partial_solve_wit_3.
Proof.
  unfold OSMutexAccept_partial_solve_wit_3, OSMutexAccept_partial_solve_wit_3_aux.
  intros H_pure.
  intros perr_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform context saved_local environment PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
(coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (sem_query_public_slot (before) (eid) (observed)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_4_pure : OSMutexAccept_partial_solve_wit_4_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_4 : OSMutexAccept_partial_solve_wit_4.
Proof.
  unfold OSMutexAccept_partial_solve_wit_4, OSMutexAccept_partial_solve_wit_4_aux.
  intros H_pure.
  intros perr_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform context saved_local environment PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
(coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_5_pure : OSMutexAccept_partial_solve_wit_5_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_5 : OSMutexAccept_partial_solve_wit_5.
Proof.
  unfold OSMutexAccept_partial_solve_wit_5, OSMutexAccept_partial_solve_wit_5_aux.
  intros H_pure.
  intros perr_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform context saved_local environment PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
(coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_accept_call_admission (context) (pe) (before) (eid)) )
  **  (coq_prop (mutex_accept_public_input (critical) (sg) (invocation) (pe) (before) (eid) (observed)) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (IntrState (before)) )
  **  (mutex_accept_interrupt_frame sg before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_6_pure : OSMutexAccept_partial_solve_wit_6_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_6 : OSMutexAccept_partial_solve_wit_6.
Proof.
  unfold OSMutexAccept_partial_solve_wit_6, OSMutexAccept_partial_solve_wit_6_aux.
  intros H_pure.
  intros perr_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform context saved_local environment PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (kernel_call_task_source (context) (before)) )
  **  (coq_prop (mutex_accept_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  ((perr_pre) # UChar  |->_)
|--
(coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (kernel_call_task_source (context) (before)) )
  **  (coq_prop (mutex_accept_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_accept_lookup (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
  **  (mutex_accept_call_support environment saved_local sg context before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_7_pure : OSMutexAccept_partial_solve_wit_7_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_7 : OSMutexAccept_partial_solve_wit_7.
Proof.
  unfold OSMutexAccept_partial_solve_wit_7, OSMutexAccept_partial_solve_wit_7_aux.
  intros H_pure.
  intros perr_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform context saved_local environment entry current retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
(coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_8 : OSMutexAccept_partial_solve_wit_8.
Proof.
  unfold OSMutexAccept_partial_solve_wit_8, OSMutexAccept_partial_solve_wit_8_aux.
  intros H_pure.
  intros perr_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform context saved_local environment retval m cnt ptr entry current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hcnt_range :
(coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|-- coq_prop (0 <= cnt <= 65535)).
  { prop_apply_p (store_ushort_range (&(pe # "os_event" ->ₛ "OSEventCnt")) cnt).
    Intros; entailer!. }
  pose proof (Hcnt_range h Hheap) as Hcnt.
  assert (Hcast : unsigned_last_nbits (Z.shiftr cnt 8) 8 = Z.shiftr cnt 8)
    by (apply mutex_accept_high_byte_cast; exact Hcnt).
  assert (Hspatial :
(coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
(coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt 8))
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)).
  { try rewrite Hcast. try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_9 : OSMutexAccept_partial_solve_wit_9.
Proof.
  unfold OSMutexAccept_partial_solve_wit_9, OSMutexAccept_partial_solve_wit_9_aux.
  intros H_pure.
  intros perr_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform context saved_local environment retval cnt_2 tid task m cnt ptr entry current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27.
  intros h Hheap.
  assert (Hprio_range :
(coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
|-- coq_prop (0 <= curPrio task <= 255)).
  { prop_apply_p (store_uchar_range (tcb_field_address (task_slot_addr sg tid) TCBPrio) (curPrio task)).
    Intros.
    match goal with Hrange : 0 <= curPrio task <= Byte.max_unsigned |- _ =>
      change (0 <= curPrio task <= 255) in Hrange end.
    entailer!. }
  pose proof (Hprio_range h Hheap) as Hprio_bound.
  assert (Hprio : unsigned_last_nbits (curPrio task) 16 = curPrio task)
    by (apply mutex_accept_u16_of_byte; exact Hprio_bound).
  assert (Hpcp_range :
(coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
|-- coq_prop (0 <= Z.shiftr cnt_2 8 <= 255)).
  { prop_apply_p (store_uchar_range (&("pcp")) (Z.shiftr cnt_2 8)).
    Intros.
    match goal with Hrange : 0 <= Z.shiftr cnt_2 8 <= Byte.max_unsigned |- _ =>
      change (0 <= Z.shiftr cnt_2 8 <= 255) in Hrange end.
    entailer!. }
  pose proof (Hpcp_range h Hheap) as Hpcp_bound.
  assert (Hpcp : unsigned_last_nbits (Z.shiftr cnt_2 8) 32 = Z.shiftr cnt_2 8)
    by (apply mutex_accept_u32_of_byte; exact Hpcp_bound).
  assert (Hspatial :
(coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
|--
(coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt 8))
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (curPrio (task))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)).
  { try rewrite Hprio. try rewrite Hpcp. try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_10_pure : OSMutexAccept_partial_solve_wit_10_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_10 : OSMutexAccept_partial_solve_wit_10.
Proof.
  unfold OSMutexAccept_partial_solve_wit_10, OSMutexAccept_partial_solve_wit_10_aux.
  intros H_pure.
  intros perr_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform context saved_local environment retval cnt tid task m cnt_2 entry current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (120) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
|--
(coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (120) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_11 : OSMutexAccept_partial_solve_wit_11.
Proof.
  unfold OSMutexAccept_partial_solve_wit_11, OSMutexAccept_partial_solve_wit_11_aux.
  intros H_pure.
  intros perr_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform context saved_local environment retval cnt_2 tid task m cnt ptr entry current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30.
  intros h Hheap.
  assert (Hprio_range :
((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
|-- coq_prop (0 <= curPrio task <= 255)).
  { prop_apply_p (store_uchar_range (tcb_field_address (task_slot_addr sg tid) TCBPrio) (curPrio task)).
    Intros.
    match goal with Hrange : 0 <= curPrio task <= Byte.max_unsigned |- _ =>
      change (0 <= curPrio task <= 255) in Hrange end.
    entailer!. }
  pose proof (Hprio_range h Hheap) as Hprio_bound.
  assert (Hprio : unsigned_last_nbits (curPrio task) 16 = curPrio task)
    by (apply mutex_accept_u16_of_byte; exact Hprio_bound).
  assert (Hspatial :
((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
|--
(coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt 8))
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (curPrio (task))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)).
  { try rewrite Hprio. try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_12 : OSMutexAccept_partial_solve_wit_12.
Proof.
  unfold OSMutexAccept_partial_solve_wit_12, OSMutexAccept_partial_solve_wit_12_aux.
  intros H_pure.
  intros perr_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform context saved_local environment retval cnt_2 tid task m cnt ptr entry current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29.
  intros h Hheap.
  assert (Hprio_range :
((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
|-- coq_prop (0 <= curPrio task <= 255)).
  { prop_apply_p (store_uchar_range (tcb_field_address (task_slot_addr sg tid) TCBPrio) (curPrio task)).
    Intros.
    match goal with Hrange : 0 <= curPrio task <= Byte.max_unsigned |- _ =>
      change (0 <= curPrio task <= 255) in Hrange end.
    entailer!. }
  pose proof (Hprio_range h Hheap) as Hprio_bound.
  assert (Hprio : unsigned_last_nbits (curPrio task) 16 = curPrio task)
    by (apply mutex_accept_u16_of_byte; exact Hprio_bound).
  assert (Hspatial :
((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt_2 8))
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (unsigned_last_nbits ((curPrio (task))) (16))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
|--
(coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (mutex_accept_current_task (sg) (entry) (tid) (task)) )
  **  ((( &( "pcp" ) )) # UChar  |-> (Z.shiftr cnt 8))
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land cnt 65280) (curPrio (task))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((&(((task_slot_addr (sg) (tid)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (task)))
  **  (mutex_accept_current_frame sg entry eid current tid task )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)).
  { try rewrite Hprio. try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_13_pure : OSMutexAccept_partial_solve_wit_13_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_13 : OSMutexAccept_partial_solve_wit_13.
Proof.
  unfold OSMutexAccept_partial_solve_wit_13, OSMutexAccept_partial_solve_wit_13_aux.
  intros H_pure.
  intros perr_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform context saved_local environment retval cnt tid task m cnt_2 entry current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
|--
(coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_14_pure : OSMutexAccept_partial_solve_wit_14_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_14 : OSMutexAccept_partial_solve_wit_14.
Proof.
  unfold OSMutexAccept_partial_solve_wit_14, OSMutexAccept_partial_solve_wit_14_aux.
  intros H_pure.
  intros perr_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform context saved_local environment retval cnt tid task m cnt_2 entry current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)
|--
(coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (mutex_accept_call_support environment saved_local sg context (mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (1) ((mutex_accept_owned_state (entry) (eid) (current) (m) (tid) ((curPrio (task)))))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((perr_pre) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_15_pure : OSMutexAccept_partial_solve_wit_15_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_15 : OSMutexAccept_partial_solve_wit_15.
Proof.
  unfold OSMutexAccept_partial_solve_wit_15, OSMutexAccept_partial_solve_wit_15_aux.
  intros H_pure.
  intros perr_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform context saved_local environment retval m cnt ptr entry current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
(coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_event_snapshot (sg) (entry) (eid) (current) (m) (cnt) (ptr)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> ptr)
  **  (mutex_accept_event_frame sg entry eid current )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_16_pure : OSMutexAccept_partial_solve_wit_16_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_16 : OSMutexAccept_partial_solve_wit_16.
Proof.
  unfold OSMutexAccept_partial_solve_wit_16, OSMutexAccept_partial_solve_wit_16_aux.
  intros H_pure.
  intros perr_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform context saved_local environment retval cnt entry current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (0) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)
|--
(coq_prop (mutex_accept_call_binding (environment) (platform) (context) (invocation) (origin)) )
  **  (coq_prop (mutex_accept_call_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (mutex_accept_call_support environment saved_local sg context entry )
  **  (coq_prop (mutex_accept_protected_result (sg) (eid) (entry) (current) (0) (0) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  ((perr_pre) # UChar  |->_)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

