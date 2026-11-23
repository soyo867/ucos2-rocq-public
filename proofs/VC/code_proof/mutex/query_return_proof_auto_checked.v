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
From Ucos2Verify.VC.code.mutex Require Import query_return_goal.
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
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.memory.
Require Import Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.statistics.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.mutex_func_sem.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_query_return_spec.
Local Open Scope sac.

Lemma proof_of_OSMutexQuery_safety_wit_1 : OSMutexQuery_safety_wit_1.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_2 : OSMutexQuery_safety_wit_2.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_3 : OSMutexQuery_safety_wit_3.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_4 : OSMutexQuery_safety_wit_4.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_5 : OSMutexQuery_safety_wit_5.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_6 : OSMutexQuery_safety_wit_6.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_7 : OSMutexQuery_safety_wit_7.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_8 : OSMutexQuery_safety_wit_8.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_9 : OSMutexQuery_safety_wit_9.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_10 : OSMutexQuery_safety_wit_10.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_11 : OSMutexQuery_safety_wit_11.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_12 : OSMutexQuery_safety_wit_12.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_13 : OSMutexQuery_safety_wit_13.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_14 : OSMutexQuery_safety_wit_14.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_15 : OSMutexQuery_safety_wit_15.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_16 : OSMutexQuery_safety_wit_16.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_17 : OSMutexQuery_safety_wit_17.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_18 : OSMutexQuery_safety_wit_18.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_19 : OSMutexQuery_safety_wit_19.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_20 : OSMutexQuery_safety_wit_20.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_21 : OSMutexQuery_safety_wit_21.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_22 : OSMutexQuery_safety_wit_22.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_24 : OSMutexQuery_safety_wit_24.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_25 : OSMutexQuery_safety_wit_25.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_26 : OSMutexQuery_safety_wit_26.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_27 : OSMutexQuery_safety_wit_27.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_28 : OSMutexQuery_safety_wit_28.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_29 : OSMutexQuery_safety_wit_29.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_30 : OSMutexQuery_safety_wit_30.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_safety_wit_31 : OSMutexQuery_safety_wit_31.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_entail_wit_1_1 : OSMutexQuery_entail_wit_1_1.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_entail_wit_1_2 : OSMutexQuery_entail_wit_1_2.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_entail_wit_1_3 : OSMutexQuery_entail_wit_1_3.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_entail_wit_1_4 : OSMutexQuery_entail_wit_1_4.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_entail_wit_2_1 : OSMutexQuery_entail_wit_2_1.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_1_pure : OSMutexQuery_partial_solve_wit_1_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_1 : OSMutexQuery_partial_solve_wit_1.
Proof.
  unfold OSMutexQuery_partial_solve_wit_1, OSMutexQuery_partial_solve_wit_1_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_2_pure : OSMutexQuery_partial_solve_wit_2_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_2 : OSMutexQuery_partial_solve_wit_2.
Proof.
  unfold OSMutexQuery_partial_solve_wit_2, OSMutexQuery_partial_solve_wit_2_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_3_pure : OSMutexQuery_partial_solve_wit_3_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_3 : OSMutexQuery_partial_solve_wit_3.
Proof.
  unfold OSMutexQuery_partial_solve_wit_3, OSMutexQuery_partial_solve_wit_3_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
|--
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_4_pure : OSMutexQuery_partial_solve_wit_4_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_4 : OSMutexQuery_partial_solve_wit_4.
Proof.
  unfold OSMutexQuery_partial_solve_wit_4, OSMutexQuery_partial_solve_wit_4_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
|--
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_5_pure : OSMutexQuery_partial_solve_wit_5_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_5 : OSMutexQuery_partial_solve_wit_5.
Proof.
  unfold OSMutexQuery_partial_solve_wit_5, OSMutexQuery_partial_solve_wit_5_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X outL_in grp_pd_in val_in prio_in pcp_in isr pd pe observed eid before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_6_pure : OSMutexQuery_partial_solve_wit_6_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_6 : OSMutexQuery_partial_solve_wit_6.
Proof.
  unfold OSMutexQuery_partial_solve_wit_6, OSMutexQuery_partial_solve_wit_6_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
|--
(coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_7_pure : OSMutexQuery_partial_solve_wit_7_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_7 : OSMutexQuery_partial_solve_wit_7.
Proof.
  unfold OSMutexQuery_partial_solve_wit_7, OSMutexQuery_partial_solve_wit_7_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X outL_in grp_pd_in val_in prio_in pcp_in isr pd pe observed eid before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
(coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_8_pure : OSMutexQuery_partial_solve_wit_8_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_8 : OSMutexQuery_partial_solve_wit_8.
Proof.
  unfold OSMutexQuery_partial_solve_wit_8, OSMutexQuery_partial_solve_wit_8_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X isr pd pe observed eid before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
|--
(coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (valid_stable_glob_vars (sg)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_9_pure : OSMutexQuery_partial_solve_wit_9_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_9 : OSMutexQuery_partial_solve_wit_9.
Proof.
  unfold OSMutexQuery_partial_solve_wit_9, OSMutexQuery_partial_solve_wit_9_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X outL_in grp_pd_in val_in prio_in pcp_in isr pd pe observed eid before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> p_mutex_data_pre)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
(coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "p_mutex_data" ) )) # Ptr  |-> pd)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_10_pure : OSMutexQuery_partial_solve_wit_10_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_10 : OSMutexQuery_partial_solve_wit_10.
Proof.
  unfold OSMutexQuery_partial_solve_wit_10, OSMutexQuery_partial_solve_wit_10_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X outL_in grp_pd_in val_in prio_in pcp_in isr pd pe observed eid before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (mutex_query_type_frame sg before eid observed )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
(coq_prop (UCOS2_state_inv (sg) (before)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (mutex_query_call_input (critical) (sg) (invocation) (pe) (pd) (before) (eid) (observed)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (encode_event_type ((eventType (observed)))))
  **  (mutex_query_type_frame sg before eid observed )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_11_pure : OSMutexQuery_partial_solve_wit_11_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_11 : OSMutexQuery_partial_solve_wit_11.
Proof.
  unfold OSMutexQuery_partial_solve_wit_11, OSMutexQuery_partial_solve_wit_11_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X outL_in grp_pd_in val_in prio_in pcp_in isr pd pe observed eid before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
(coq_prop (mutex_query_handle_protocol (critical) (sg) (invocation) (eid)) )
  **  (coq_prop (mutex_query_lookup (before) (eid) (observed)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_12_pure : OSMutexQuery_partial_solve_wit_12_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_12 : OSMutexQuery_partial_solve_wit_12.
Proof.
  unfold OSMutexQuery_partial_solve_wit_12, OSMutexQuery_partial_solve_wit_12_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X outL_in grp_pd_in val_in prio_in pcp_in isr pd pe observed eid before mask origin invocation sg critical platform entry current retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
(coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> pcp_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> prio_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> val_in)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_13 : OSMutexQuery_partial_solve_wit_13.
Proof.
  unfold OSMutexQuery_partial_solve_wit_13, OSMutexQuery_partial_solve_wit_13_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X outL_in grp_pd_in isr pd pe observed eid before mask origin invocation sg critical platform retval cnt grp evtL entry current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28.
  intros h Hheap.
  assert (Hbit : Z.eqb (Z.land cnt 255) 255 = false)
    by (apply Z.eqb_neq; exact PreH1).
  unfold decode_OSValue_from_cnt, decode_OwnerPrio_from_cnt, decode_PCP_from_cnt.
  rewrite Hbit.
  assert (Hspatial :
(coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (Z.land cnt 255))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> 0)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
(coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (decode_PCP_from_cnt (cnt)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (decode_OwnerPrio_from_cnt (cnt)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> (decode_OSValue_from_cnt (cnt)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )).
  { unfold decode_OSValue_from_cnt, decode_OwnerPrio_from_cnt, decode_PCP_from_cnt.
    rewrite Hbit. try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. entailer!. }
  unfold decode_OSValue_from_cnt, decode_OwnerPrio_from_cnt, decode_PCP_from_cnt in Hspatial.
  rewrite Hbit in Hspatial.
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_14 : OSMutexQuery_partial_solve_wit_14.
Proof.
  unfold OSMutexQuery_partial_solve_wit_14, OSMutexQuery_partial_solve_wit_14_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X outL_in grp_pd_in isr pd pe observed eid before mask origin invocation sg critical platform retval cnt grp evtL entry current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28.
  intros h Hheap.
  assert (Hbit : Z.eqb (Z.land cnt 255) 255 = true)
    by (apply Z.eqb_eq; exact PreH1).
  unfold decode_OSValue_from_cnt, decode_OwnerPrio_from_cnt, decode_PCP_from_cnt.
  rewrite Hbit.
  assert (Hspatial :
(coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (unsigned_last_nbits ((Z.shiftr cnt 8)) (8)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (Z.land cnt 255))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> 1)
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
(coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt)
  **  (used_event_rest_no_type_cnt_ptr sg (entry.(TskState) ) pe eid current )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (decode_PCP_from_cnt (cnt)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (decode_OwnerPrio_from_cnt (cnt)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> (decode_OSValue_from_cnt (cnt)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp_pd_in)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )).
  { unfold decode_OSValue_from_cnt, decode_OwnerPrio_from_cnt, decode_PCP_from_cnt.
    rewrite Hbit. try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. entailer!. }
  unfold decode_OSValue_from_cnt, decode_OwnerPrio_from_cnt, decode_PCP_from_cnt in Hspatial.
  rewrite Hbit in Hspatial.
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_15_pure : OSMutexQuery_partial_solve_wit_15_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_15 : OSMutexQuery_partial_solve_wit_15.
Proof.
  unfold OSMutexQuery_partial_solve_wit_15, OSMutexQuery_partial_solve_wit_15_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X outL_in isr pd pe observed eid before mask origin invocation sg critical platform retval cnt cnt_2 grp evtL entry current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_oseventtbl sg pe evtL )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (decode_PCP_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (decode_OwnerPrio_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> (decode_OSValue_from_cnt (cnt_2)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
(coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_oseventtbl sg pe evtL )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (decode_PCP_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (decode_OwnerPrio_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> (decode_OSValue_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_16_pure : OSMutexQuery_partial_solve_wit_16_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_16 : OSMutexQuery_partial_solve_wit_16.
Proof.
  unfold OSMutexQuery_partial_solve_wit_16, OSMutexQuery_partial_solve_wit_16_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X outL_in isr pd pe observed eid before mask origin invocation sg critical platform retval cnt cnt_2 grp evtL entry current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_oseventtbl sg pe evtL )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (decode_PCP_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (decode_OwnerPrio_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> (decode_OSValue_from_cnt (cnt_2)))
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
(coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (retval) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (interrupt_inv sg (entry.(IntrState) ) )
  **  (mutex_query_raw_frame sg entry eid )
  **  (mutex_query_event_unread sg (entry.(TskState) ) eid current )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_2)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (store_oseventtbl sg pe evtL )
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar  |-> (decode_PCP_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar  |-> (decode_OwnerPrio_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSValue")) # UChar  |-> (decode_OSValue_from_cnt (cnt_2)))
  **  ((&((pd)  # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar  |-> grp)
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_17 : OSMutexQuery_partial_solve_wit_17.
Proof.
  unfold OSMutexQuery_partial_solve_wit_17.
  intros p_mutex_data_pre pevent_pre X outL_in isr pd pe observed eid before mask origin invocation sg critical platform retval cnt entry current cnt_2 grp evtL PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
(mutex_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_18 : OSMutexQuery_partial_solve_wit_18.
Proof.
  unfold OSMutexQuery_partial_solve_wit_18.
  intros p_mutex_data_pre pevent_pre X outL_in isr pd pe observed eid before mask origin invocation sg critical platform retval cnt entry current cnt_2 grp evtL PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
|--
(mutex_query_copy_frame platform critical sg invocation origin mask retval before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") outL_in )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_19_pure : OSMutexQuery_partial_solve_wit_19_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_19 : OSMutexQuery_partial_solve_wit_19.
Proof.
  unfold OSMutexQuery_partial_solve_wit_19, OSMutexQuery_partial_solve_wit_19_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X outL_in isr pd pe observed eid before mask origin invocation sg critical platform cnt cpu_sr entry current cnt_2 grp evtL pdest psrc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
(coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))
  **  ((( &( "pdest" ) )) # Ptr  |-> (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_20_pure : OSMutexQuery_partial_solve_wit_20_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_20 : OSMutexQuery_partial_solve_wit_20.
Proof.
  unfold OSMutexQuery_partial_solve_wit_20, OSMutexQuery_partial_solve_wit_20_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X outL_in isr pd pe observed eid before mask origin invocation sg critical platform cnt cpu_sr entry current cnt_2 grp evtL pdest psrc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
(coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> (&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))
  **  ((( &( "pdest" ) )) # Ptr  |-> (&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))))
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_21_pure : OSMutexQuery_partial_solve_wit_21_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_21 : OSMutexQuery_partial_solve_wit_21.
Proof.
  unfold OSMutexQuery_partial_solve_wit_21, OSMutexQuery_partial_solve_wit_21_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X outL_in isr pd pe observed eid before mask origin invocation sg critical platform cnt cpu_sr pdest psrc i entry current cnt_2 grp evtL pdest_v psrc_v PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> (psrc_v + (1 * sizeof(UCHAR))))
  **  ((( &( "pdest" ) )) # Ptr  |-> (pdest_v + (1 * sizeof(UCHAR))))
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  ((psrc_v) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL i )
  **  ((pdest_v) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_osprio_array_missing_i &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
(coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) + 1 ))
  **  ((( &( "pdest" ) )) # Ptr  |-> ((&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) + 1 ))
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL i )
  **  (((&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_osprio_array_missing_i &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_22_pure : OSMutexQuery_partial_solve_wit_22_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_22 : OSMutexQuery_partial_solve_wit_22.
Proof.
  unfold OSMutexQuery_partial_solve_wit_22, OSMutexQuery_partial_solve_wit_22_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X outL_in isr pd pe observed eid before mask origin invocation sg critical platform cnt cpu_sr pdest psrc i entry current cnt_2 grp evtL pdest_v psrc_v PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> (psrc_v + (1 * sizeof(UCHAR))))
  **  ((( &( "pdest" ) )) # Ptr  |-> (pdest_v + (1 * sizeof(UCHAR))))
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  ((psrc_v) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL i )
  **  ((pdest_v) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_osprio_array_missing_i &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
(coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  ((( &( "psrc" ) )) # Ptr  |-> ((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) + 1 ))
  **  ((( &( "pdest" ) )) # Ptr  |-> ((&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR))) + 1 ))
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (((&((pe)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_oseventtbl_missing_i sg pe evtL i )
  **  (((&((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> (Znth (i) (evtL) (0)))
  **  (store_osprio_array_missing_i &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) i )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_23_pure : OSMutexQuery_partial_solve_wit_23_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_23 : OSMutexQuery_partial_solve_wit_23.
Proof.
  unfold OSMutexQuery_partial_solve_wit_23, OSMutexQuery_partial_solve_wit_23_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X outL_in isr pd pe observed eid before mask origin invocation sg critical platform cnt cpu_sr entry current cnt_2 grp evtL pdest psrc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
(mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_24_pure : OSMutexQuery_partial_solve_wit_24_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_24 : OSMutexQuery_partial_solve_wit_24.
Proof.
  unfold OSMutexQuery_partial_solve_wit_24, OSMutexQuery_partial_solve_wit_24_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X outL_in isr pd pe observed eid before mask origin invocation sg critical platform cnt cpu_sr entry current cnt_2 grp evtL pdest psrc i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
(mutex_query_copy_frame platform critical sg invocation origin mask cpu_sr before entry eid observed current pd cnt_2 grp evtL )
  **  (store_oseventtbl sg pe evtL )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_25_pure : OSMutexQuery_partial_solve_wit_25_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_25 : OSMutexQuery_partial_solve_wit_25.
Proof.
  unfold OSMutexQuery_partial_solve_wit_25, OSMutexQuery_partial_solve_wit_25_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X outL_in isr pd pe observed eid before mask origin invocation sg critical platform cnt cpu_sr pdest psrc i cnt_2 grp evtL entry current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (mutex_query_output_fields pd cnt_2 grp )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
(coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  (mutex_query_output_fields pd cnt_2 grp )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_26_pure : OSMutexQuery_partial_solve_wit_26_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexQuery_partial_solve_wit_26 : OSMutexQuery_partial_solve_wit_26.
Proof.
  unfold OSMutexQuery_partial_solve_wit_26, OSMutexQuery_partial_solve_wit_26_aux.
  intros H_pure.
  intros p_mutex_data_pre pevent_pre X outL_in isr pd pe observed eid before mask origin invocation sg critical platform cnt cpu_sr pdest psrc i cnt_2 grp evtL entry current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (mutex_query_output_fields pd cnt_2 grp )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
(coq_prop (mutex_query_acquire_facts (critical) (sg) (invocation) (eid) (mask) (cpu_sr) (before) (entry) (observed) (current)) )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (mutex_query_copy_snapshot (entry) (eid) (current) (cnt_2) (grp) (evtL)) )
  **  (mutex_query_output_fields pd cnt_2 grp )
  **  (store_osprio_array &((pd)  # "os_mutex_data" ->ₛ "OSEventTbl") (copy_prefix_list (evtL) (outL_in) (i)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_query_event_wait_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

