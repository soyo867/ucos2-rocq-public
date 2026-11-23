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
From Ucos2Verify.VC.code.mutex Require Import mutex_post_api_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.sched.spec.sched_del_history_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_api_continuation_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_api_callee_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_api_scheduler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_program_spec.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_parent_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
Local Open Scope sac_scope.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_spec.
Local Open Scope sac.

Lemma proof_of_OSMutexPost_safety_wit_1 : OSMutexPost_safety_wit_1.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_safety_wit_2 : OSMutexPost_safety_wit_2.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_safety_wit_4 : OSMutexPost_safety_wit_4.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_safety_wit_5 : OSMutexPost_safety_wit_5.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_safety_wit_6 : OSMutexPost_safety_wit_6.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_safety_wit_7 : OSMutexPost_safety_wit_7.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_safety_wit_8 : OSMutexPost_safety_wit_8.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_safety_wit_9 : OSMutexPost_safety_wit_9.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_safety_wit_10 : OSMutexPost_safety_wit_10.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_safety_wit_11 : OSMutexPost_safety_wit_11.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_safety_wit_12 : OSMutexPost_safety_wit_12.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_safety_wit_13 : OSMutexPost_safety_wit_13.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_safety_wit_14 : OSMutexPost_safety_wit_14.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_safety_wit_15 : OSMutexPost_safety_wit_15.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_safety_wit_16 : OSMutexPost_safety_wit_16.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_safety_wit_17 : OSMutexPost_safety_wit_17.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_safety_wit_18 : OSMutexPost_safety_wit_18.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_safety_wit_19 : OSMutexPost_safety_wit_19.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_safety_wit_20 : OSMutexPost_safety_wit_20.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_safety_wit_21 : OSMutexPost_safety_wit_21.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_safety_wit_22 : OSMutexPost_safety_wit_22.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_1 : OSMutexPost_partial_solve_wit_1.
Proof.
  unfold OSMutexPost_partial_solve_wit_1.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_entry source_env external platform saved_local sg call mask before )
|--
(mutex_del_continuation_entry source_env external platform saved_local sg call mask before )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_2_pure : OSMutexPost_partial_solve_wit_2_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_2 : OSMutexPost_partial_solve_wit_2.
Proof.
  unfold OSMutexPost_partial_solve_wit_2, OSMutexPost_partial_solve_wit_2_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )
  **  (UCOS2_inv sg before )
|--
(UCOS2_inv sg before )
  **  (mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_3_pure : OSMutexPost_partial_solve_wit_3_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_3 : OSMutexPost_partial_solve_wit_3.
Proof.
  unfold OSMutexPost_partial_solve_wit_3, OSMutexPost_partial_solve_wit_3_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15.
  intros h Hheap.
  assert (Hspatial :
((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (mutex_post_nesting_frame sg before )
  **  (mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )
|--
((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (mutex_post_nesting_frame sg before )
  **  (mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_4 : OSMutexPost_partial_solve_wit_4.
Proof.
  unfold OSMutexPost_partial_solve_wit_4.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg before )
  **  (mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )
|--
(mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )
  **  (UCOS2_inv sg before )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_5_pure : OSMutexPost_partial_solve_wit_5_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_5 : OSMutexPost_partial_solve_wit_5.
Proof.
  unfold OSMutexPost_partial_solve_wit_5, OSMutexPost_partial_solve_wit_5_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16.
  intros h Hheap.
  assert (Hspatial :
((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (mutex_post_nesting_frame sg before )
  **  (mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )
|--
((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (mutex_post_nesting_frame sg before )
  **  (mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_6 : OSMutexPost_partial_solve_wit_6.
Proof.
  unfold OSMutexPost_partial_solve_wit_6.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg before )
  **  (mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )
|--
(mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )
  **  (UCOS2_inv sg before )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_7_pure : OSMutexPost_partial_solve_wit_7_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_7 : OSMutexPost_partial_solve_wit_7.
Proof.
  unfold OSMutexPost_partial_solve_wit_7, OSMutexPost_partial_solve_wit_7_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16.
  intros h Hheap.
  assert (Hspatial :
((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (mutex_post_nesting_frame sg before )
  **  (mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )
|--
((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (mutex_post_nesting_frame sg before )
  **  (mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_8_pure : OSMutexPost_partial_solve_wit_8_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_8 : OSMutexPost_partial_solve_wit_8.
Proof.
  unfold OSMutexPost_partial_solve_wit_8, OSMutexPost_partial_solve_wit_8_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg before )
  **  (mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )
|--
(UCOS2_inv sg before )
  **  (mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_9 : OSMutexPost_partial_solve_wit_9.
Proof.
  unfold OSMutexPost_partial_solve_wit_9.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )
|--
((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_10_pure : OSMutexPost_partial_solve_wit_10_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_10 : OSMutexPost_partial_solve_wit_10.
Proof.
  unfold OSMutexPost_partial_solve_wit_10, OSMutexPost_partial_solve_wit_10_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )
|--
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_11 : OSMutexPost_partial_solve_wit_11.
Proof.
  unfold OSMutexPost_partial_solve_wit_11.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg before )
  **  (mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )
|--
(mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )
  **  (UCOS2_inv sg before )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_12_pure : OSMutexPost_partial_solve_wit_12_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_12 : OSMutexPost_partial_solve_wit_12.
Proof.
  unfold OSMutexPost_partial_solve_wit_12, OSMutexPost_partial_solve_wit_12_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )
|--
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_13_pure : OSMutexPost_partial_solve_wit_13_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_13 : OSMutexPost_partial_solve_wit_13.
Proof.
  unfold OSMutexPost_partial_solve_wit_13, OSMutexPost_partial_solve_wit_13_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg before )
  **  (mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )
|--
(mutex_post_api_entry_frame source_env external platform saved_local sg call mask before )
  **  (UCOS2_inv sg before )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_14 : OSMutexPost_partial_solve_wit_14.
Proof.
  unfold OSMutexPost_partial_solve_wit_14.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_save_pre source_env external platform critical saved_local sg call mask before )
|--
(mutex_post_api_save_pre source_env external platform critical saved_local sg call mask before )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_15_pure : OSMutexPost_partial_solve_wit_15_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_15 : OSMutexPost_partial_solve_wit_15.
Proof.
  unfold OSMutexPost_partial_solve_wit_15, OSMutexPost_partial_solve_wit_15_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_save_post source_env external platform critical saved_local sg call mask retval before )
|--
(mutex_post_api_save_post source_env external platform critical saved_local sg call mask retval before )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_16_pure : OSMutexPost_partial_solve_wit_16_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_16 : OSMutexPost_partial_solve_wit_16.
Proof.
  unfold OSMutexPost_partial_solve_wit_16, OSMutexPost_partial_solve_wit_16_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29.
  intros h Hheap.
  assert (Hspatial :
(critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(UCOS2_inv sg acquired )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_17_pure : OSMutexPost_partial_solve_wit_17_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_17 : OSMutexPost_partial_solve_wit_17.
Proof.
  unfold OSMutexPost_partial_solve_wit_17, OSMutexPost_partial_solve_wit_17_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg acquired )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(UCOS2_inv sg acquired )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_18 : OSMutexPost_partial_solve_wit_18.
Proof.
  unfold OSMutexPost_partial_solve_wit_18.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33.
  intros h Hheap.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  (mutex_post_commit_field_frame sg acquired eid (event_image (sg) ((acquired.(TskState) )) (current)) EventCntField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  (mutex_post_commit_field_frame sg acquired eid (event_image (sg) ((acquired.(TskState) )) (current)) EventCntField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_19 : OSMutexPost_partial_solve_wit_19.
Proof.
  unfold OSMutexPost_partial_solve_wit_19, OSMutexPost_partial_solve_wit_19_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33.
  intros h Hheap.
  assert (Hlow_byte : 0 <= Z.land (encode_event_cnt_value current) 255 <= 255).
  { pose proof (Z.land_ones (encode_event_cnt_value current) 8 ltac:(lia)) as Hmask.
    change (Z.land (encode_event_cnt_value current) 255 =
            encode_event_cnt_value current mod 256) in Hmask.
    rewrite Hmask.
    pose proof (Z.mod_pos_bound (encode_event_cnt_value current) 256 ltac:(lia)); lia. }
  assert (Hhigh_byte : 0 <= unsigned_last_nbits (Z.shiftr (encode_event_cnt_value current) 8) 8 <= 255).
  { unfold unsigned_last_nbits.
    change (0 <= Z.shiftr (encode_event_cnt_value current) 8 mod 256 <= 255).
    pose proof (Z.mod_pos_bound (Z.shiftr (encode_event_cnt_value current) 8) 256 ltac:(lia)); lia. }
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  (mutex_post_commit_field_frame sg acquired eid (event_image (sg) ((acquired.(TskState) )) (current)) EventCntField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  (mutex_post_commit_field_frame sg acquired eid (event_image (sg) ((acquired.(TskState) )) (current)) EventCntField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | exact (proj1 Hlow_byte) | exact (proj2 Hlow_byte) | exact (proj1 Hhigh_byte) | exact (proj2 Hhigh_byte) | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_20 : OSMutexPost_partial_solve_wit_20.
Proof.
  unfold OSMutexPost_partial_solve_wit_20.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35.
  intros h Hheap.
  assert (Hspatial :
((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (caller)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (encode_event_ptr_value (sg) (current)))
  **  (mutex_post_comparison_frame sg acquired eid (event_image (sg) ((acquired.(TskState) )) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (encode_event_ptr_value (sg) (current)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (caller)))
  **  (mutex_post_comparison_frame sg acquired eid (event_image (sg) ((acquired.(TskState) )) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_21_pure : OSMutexPost_partial_solve_wit_21_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_21 : OSMutexPost_partial_solve_wit_21.
Proof.
  unfold OSMutexPost_partial_solve_wit_21, OSMutexPost_partial_solve_wit_21_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (encode_event_ptr_value (sg) (current)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (caller)))
  **  (mutex_post_comparison_frame sg acquired eid (event_image (sg) ((acquired.(TskState) )) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (caller)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (encode_event_ptr_value (sg) (current)))
  **  (mutex_post_comparison_frame sg acquired eid (event_image (sg) ((acquired.(TskState) )) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_22_pure : OSMutexPost_partial_solve_wit_22_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_22 : OSMutexPost_partial_solve_wit_22.
Proof.
  unfold OSMutexPost_partial_solve_wit_22, OSMutexPost_partial_solve_wit_22_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg acquired )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_23_pure : OSMutexPost_partial_solve_wit_23_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_23 : OSMutexPost_partial_solve_wit_23.
Proof.
  unfold OSMutexPost_partial_solve_wit_23, OSMutexPost_partial_solve_wit_23_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_restore_pre source_env external platform critical saved_local sg call mask retval acquired acquired )
|--
(mutex_post_api_restore_pre source_env external platform critical saved_local sg call mask retval acquired acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_24 : OSMutexPost_partial_solve_wit_24.
Proof.
  unfold OSMutexPost_partial_solve_wit_24.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_restore_source_post source_env external platform critical saved_local sg call mask acquired )
|--
(mutex_post_api_restore_source_post source_env external platform critical saved_local sg call mask acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_25_pure : OSMutexPost_partial_solve_wit_25_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_25 : OSMutexPost_partial_solve_wit_25.
Proof.
  unfold OSMutexPost_partial_solve_wit_25, OSMutexPost_partial_solve_wit_25_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (encode_event_ptr_value (sg) (current)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (caller)))
  **  (mutex_post_comparison_frame sg acquired eid (event_image (sg) ((acquired.(TskState) )) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (caller)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (encode_event_ptr_value (sg) (current)))
  **  (mutex_post_comparison_frame sg acquired eid (event_image (sg) ((acquired.(TskState) )) (current)) )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_26_pure : OSMutexPost_partial_solve_wit_26_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_26 : OSMutexPost_partial_solve_wit_26.
Proof.
  unfold OSMutexPost_partial_solve_wit_26, OSMutexPost_partial_solve_wit_26_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg acquired )
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (encode_event_cnt_value (current)) 8)) (8)))
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((( &( "pcp" ) )) # UChar  |-> (mfPCP (mutex)))
  **  (UCOS2_inv sg acquired )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_27_pure : OSMutexPost_partial_solve_wit_27_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_27 : OSMutexPost_partial_solve_wit_27.
Proof.
  unfold OSMutexPost_partial_solve_wit_27, OSMutexPost_partial_solve_wit_27_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40.
  intros h Hheap.
  assert (Hspatial :
(((( &( "OSTCBPrioTbl" ) ) + ((mfPCP (mutex)) * sizeof(PTR)))) # Ptr  |-> 1)
  **  (store_prio_tbl_missing_i sg ((acquired.(TskState) ).(prioTbl) ) (mfPCP (mutex)) )
  **  (UCOS2_raw_rep_missing_priority_table sg acquired )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(((( &( "OSTCBPrioTbl" ) ) + ((mfPCP (mutex)) * sizeof(PTR)))) # Ptr  |-> 1)
  **  (store_prio_tbl_missing_i sg ((acquired.(TskState) ).(prioTbl) ) (mfPCP (mutex)) )
  **  (UCOS2_raw_rep_missing_priority_table sg acquired )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_28 : OSMutexPost_partial_solve_wit_28.
Proof.
  unfold OSMutexPost_partial_solve_wit_28, OSMutexPost_partial_solve_wit_28_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40.
  intros h Hheap.
  assert (Hvalid : UCOS2_state_inv sg acquired) by exact PreH19.
  assert (Htasks : task_in_range sg acquired.(TskState))
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
  assert (Hrange : task_priority_in_range sg node.(curPrio))
    by (unfold task_in_range in Htasks; intuition eauto).
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile,
          valid_stable_glob_vars in Hvalid; tauto).
  unfold task_priority_in_range in Hrange; rewrite Hlowest in Hrange.
  assert (Hpriority_nonnegative : 0 <= node.(curPrio)) by lia.
  assert (Hpriority_byte : node.(curPrio) < 256) by lia.
  pose proof (mutex_del_priority_values_length sg
    (mutex_post_reserved_table acquired mutex.(mfPCP))) as Htable_length.
  assert (Hspatial :
(tcb64_storage_rep (task_slot_addr (sg) (caller)) (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_post_reserved_table (acquired) ((mfPCP (mutex)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((acquired.(TskState) )) (((acquired.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((acquired.(SchedState) ).(readyList) )) ((acquired.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (caller)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((acquired.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg acquired caller )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(tcb64_storage_rep (task_slot_addr (sg) (caller)) (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_post_reserved_table (acquired) ((mfPCP (mutex)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((acquired.(TskState) )) (((acquired.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((acquired.(SchedState) ).(readyList) )) ((acquired.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (caller)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((acquired.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg acquired caller )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_29 : OSMutexPost_partial_solve_wit_29.
Proof.
  unfold OSMutexPost_partial_solve_wit_29, OSMutexPost_partial_solve_wit_29_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval_2 acquired current mutex caller node retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41.
  intros h Hheap.
  assert (Hvalid : UCOS2_state_inv sg acquired) by assumption.
  assert (Htasks : task_in_range sg acquired.(TskState))
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
  assert (Hnode : acquired.(TskState).(inUsedTaskStates) caller = Some node) by assumption.
  assert (Hpriority_range : task_priority_in_range sg node.(curPrio))
    by (unfold task_in_range in Htasks; intuition eauto).
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile,
          valid_stable_glob_vars in Hvalid; tauto).
  unfold task_priority_in_range in Hpriority_range; rewrite Hlowest in Hpriority_range.
  assert (Hresult_range : 0 <= retval < 64).
  { unfold mutex_effective_priority_result in PreH1; intuition lia. }
  assert (Hresult_nonnegative : 0 <= retval) by lia.
  assert (Hresult_byte : retval <= 255) by lia.
  assert (Hspatial :
(tcb64_storage_rep (task_slot_addr (sg) (caller)) (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_post_reserved_table (acquired) ((mfPCP (mutex)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((acquired.(TskState) )) (((acquired.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((acquired.(SchedState) ).(readyList) )) ((acquired.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (caller)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((acquired.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg acquired caller )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(tcb64_storage_rep (task_slot_addr (sg) (caller)) (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_post_reserved_table (acquired) ((mfPCP (mutex)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((acquired.(TskState) )) (((acquired.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((acquired.(SchedState) ).(readyList) )) ((acquired.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (caller)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((acquired.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg acquired caller )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_30_pure : OSMutexPost_partial_solve_wit_30_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_30 : OSMutexPost_partial_solve_wit_30.
Proof.
  unfold OSMutexPost_partial_solve_wit_30, OSMutexPost_partial_solve_wit_30_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45.
  intros h Hheap.
  assert (Hspatial :
((&(((task_slot_addr (sg) (caller)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without (task_slot_addr (sg) (caller)) TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_post_reserved_table (acquired) ((mfPCP (mutex)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((acquired.(TskState) )) (((acquired.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((acquired.(SchedState) ).(readyList) )) ((acquired.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (caller)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((acquired.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg acquired caller )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&(((task_slot_addr (sg) (caller)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without (task_slot_addr (sg) (caller)) TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_post_reserved_table (acquired) ((mfPCP (mutex)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((acquired.(TskState) )) (((acquired.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((acquired.(SchedState) ).(readyList) )) ((acquired.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (caller)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((acquired.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg acquired caller )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_31 : OSMutexPost_partial_solve_wit_31.
Proof.
  unfold OSMutexPost_partial_solve_wit_31, OSMutexPost_partial_solve_wit_31_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval_2 acquired current mutex caller node retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45.
  intros h Hheap.
  assert (Hvalid : UCOS2_state_inv sg acquired) by assumption.
  assert (Htasks : task_in_range sg acquired.(TskState))
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
  assert (Hnode : acquired.(TskState).(inUsedTaskStates) caller = Some node) by assumption.
  assert (Hpriority_range : task_priority_in_range sg node.(curPrio))
    by (unfold task_in_range in Htasks; intuition eauto).
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile,
          valid_stable_glob_vars in Hvalid; tauto).
  unfold task_priority_in_range in Hpriority_range; rewrite Hlowest in Hpriority_range.
  destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding
    node.(curPrio) ltac:(lia)) as [Hx [[Hy_nonnegative Hy_upper] Hencode]].
  pose proof (mutex_del_priority_values_length sg
    (mutex_post_reserved_table acquired mutex.(mfPCP))) as Htable_length.
  assert (Hrows_length : Zlength (sched_row_values acquired.(TskState)
    acquired.(SchedState).(readyList)) = 8).
  { unfold sched_row_values; rewrite Zlength_correct, map_length; reflexivity. }
  assert (Himage_fields : mutex_priority_image_fields (task_tcb64_image sg node)
    node.(curPrio) (tcb_x_of_prio node.(curPrio)) (tcb_y_of_prio node.(curPrio))
    (tcb_bit_x_of_prio node.(curPrio)) (tcb_bit_y_of_prio node.(curPrio))).
  { unfold mutex_priority_image_fields; repeat split; reflexivity. }
  assert (Hspatial :
(tcb64_storage_rep (task_slot_addr (sg) (caller)) (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_post_reserved_table (acquired) ((mfPCP (mutex)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((acquired.(TskState) )) (((acquired.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((acquired.(SchedState) ).(readyList) )) ((acquired.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (caller)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((acquired.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg acquired caller )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(tcb64_storage_rep (task_slot_addr (sg) (caller)) (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_post_reserved_table (acquired) ((mfPCP (mutex)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((acquired.(TskState) )) (((acquired.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((acquired.(SchedState) ).(readyList) )) ((acquired.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (caller)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((acquired.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg acquired caller )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_32_pure : OSMutexPost_partial_solve_wit_32_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_32 : OSMutexPost_partial_solve_wit_32.
Proof.
  unfold OSMutexPost_partial_solve_wit_32, OSMutexPost_partial_solve_wit_32_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval_2 acquired current mutex caller node retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep (task_slot_addr (sg) (caller)) (mutex_priority_image ((task_tcb64_image (sg) (node))) (retval)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth (retval) ((task_slot_addr (sg) (caller))) ((mutex_del_priority_values (sg) ((mutex_post_reserved_table (acquired) ((mfPCP (mutex)))))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_rows ((sched_row_values ((acquired.(TskState) )) (((acquired.(SchedState) ).(readyList) )))) ((tcb_y_of_prio ((curPrio (node))))) ((tcb_bit_x_of_prio ((curPrio (node))))) (retval)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_group ((sched_row_values ((acquired.(TskState) )) (((acquired.(SchedState) ).(readyList) )))) ((encode_ready_grp (((acquired.(SchedState) ).(readyList) )) ((acquired.(TskState) )))) ((tcb_y_of_prio ((curPrio (node))))) ((tcb_bit_x_of_prio ((curPrio (node))))) ((tcb_bit_y_of_prio ((curPrio (node))))) (retval)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (caller)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current ((task_slot_addr (sg) (caller))) ((task_slot_addr (sg) (caller))) ((sched_priority_byte (((acquired.(SchedState) ).(curSchedPrio) )))) (retval)))
  **  (mutex_del_priority_frame sg acquired caller )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(tcb64_storage_rep (task_slot_addr (sg) (caller)) (mutex_priority_image ((task_tcb64_image (sg) (node))) (retval)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth (retval) ((task_slot_addr (sg) (caller))) ((mutex_del_priority_values (sg) ((mutex_post_reserved_table (acquired) ((mfPCP (mutex)))))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_rows ((sched_row_values ((acquired.(TskState) )) (((acquired.(SchedState) ).(readyList) )))) ((tcb_y_of_prio ((curPrio (node))))) ((tcb_bit_x_of_prio ((curPrio (node))))) (retval)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_group ((sched_row_values ((acquired.(TskState) )) (((acquired.(SchedState) ).(readyList) )))) ((encode_ready_grp (((acquired.(SchedState) ).(readyList) )) ((acquired.(TskState) )))) ((tcb_y_of_prio ((curPrio (node))))) ((tcb_bit_x_of_prio ((curPrio (node))))) ((tcb_bit_y_of_prio ((curPrio (node))))) (retval)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (caller)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current ((task_slot_addr (sg) (caller))) ((task_slot_addr (sg) (caller))) ((sched_priority_byte (((acquired.(SchedState) ).(curSchedPrio) )))) (retval)))
  **  (mutex_del_priority_frame sg acquired caller )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_33_pure : OSMutexPost_partial_solve_wit_33_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_33 : OSMutexPost_partial_solve_wit_33.
Proof.
  unfold OSMutexPost_partial_solve_wit_33, OSMutexPost_partial_solve_wit_33_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval_2 acquired current mutex caller node retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45.
  intros h Hheap.
  assert (Hspatial :
((&(((task_slot_addr (sg) (caller)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without (task_slot_addr (sg) (caller)) TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_post_reserved_table (acquired) ((mfPCP (mutex)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((acquired.(TskState) )) (((acquired.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((acquired.(SchedState) ).(readyList) )) ((acquired.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (caller)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((acquired.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg acquired caller )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&(((task_slot_addr (sg) (caller)))  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without (task_slot_addr (sg) (caller)) TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_post_reserved_table (acquired) ((mfPCP (mutex)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((acquired.(TskState) )) (((acquired.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((acquired.(SchedState) ).(readyList) )) ((acquired.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (caller)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((acquired.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg acquired caller )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_34_pure : OSMutexPost_partial_solve_wit_34_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_34 : OSMutexPost_partial_solve_wit_34.
Proof.
  unfold OSMutexPost_partial_solve_wit_34, OSMutexPost_partial_solve_wit_34_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval_2 acquired current mutex caller node retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg (mutex_post_owner_priority_state (sg) (acquired) ((mfPCP (mutex))) (caller) (node) (retval)) )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(UCOS2_inv sg (mutex_post_owner_priority_state (sg) (acquired) ((mfPCP (mutex))) (caller) (node) (retval)) )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_35 : OSMutexPost_partial_solve_wit_35.
Proof.
  unfold OSMutexPost_partial_solve_wit_35, OSMutexPost_partial_solve_wit_35_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38.
  intros h Hheap.
  assert (Hlow_byte : 0 <= Z.land (encode_event_cnt_value current) 255 <= 255).
  { pose proof (Z.land_ones (encode_event_cnt_value current) 8 ltac:(lia)) as Hmask.
    change (Z.land (encode_event_cnt_value current) 255 =
            encode_event_cnt_value current mod 256) in Hmask.
    rewrite Hmask.
    pose proof (Z.mod_pos_bound (encode_event_cnt_value current) 256 ltac:(lia)); lia. }
  assert (Hspatial :
(UCOS2_inv sg acquired )
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr (encode_event_cnt_value (current)) 8)) (8)))
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((( &( "pcp" ) )) # UChar  |-> (mfPCP (mutex)))
  **  (UCOS2_inv sg acquired )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { rewrite PreH4; entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | exact (proj1 Hlow_byte) | exact (proj2 Hlow_byte) | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_36_pure : OSMutexPost_partial_solve_wit_36_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_36 : OSMutexPost_partial_solve_wit_36.
Proof.
  unfold OSMutexPost_partial_solve_wit_36, OSMutexPost_partial_solve_wit_36_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval_2 acquired current mutex caller node retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg (mutex_post_owner_priority_state (sg) (acquired) ((mfPCP (mutex))) (caller) (node) (retval)) )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(UCOS2_inv sg (mutex_post_owner_priority_state (sg) (acquired) ((mfPCP (mutex))) (caller) (node) (retval)) )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_37_pure : OSMutexPost_partial_solve_wit_37_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_37 : OSMutexPost_partial_solve_wit_37.
Proof.
  unfold OSMutexPost_partial_solve_wit_37, OSMutexPost_partial_solve_wit_37_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval_2 acquired current mutex caller node retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg (mutex_post_owner_priority_state (sg) (acquired) ((mfPCP (mutex))) (caller) (node) (retval)) )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(UCOS2_inv sg (mutex_post_owner_priority_state (sg) (acquired) ((mfPCP (mutex))) (caller) (node) (retval)) )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_38_pure : OSMutexPost_partial_solve_wit_38_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_38 : OSMutexPost_partial_solve_wit_38.
Proof.
  unfold OSMutexPost_partial_solve_wit_38, OSMutexPost_partial_solve_wit_38_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg prepared )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(UCOS2_inv sg prepared )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_39_pure : OSMutexPost_partial_solve_wit_39_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_39 : OSMutexPost_partial_solve_wit_39.
Proof.
  unfold OSMutexPost_partial_solve_wit_39, OSMutexPost_partial_solve_wit_39_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg prepared )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(UCOS2_inv sg prepared )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_40_pure : OSMutexPost_partial_solve_wit_40_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_40 : OSMutexPost_partial_solve_wit_40.
Proof.
  unfold OSMutexPost_partial_solve_wit_40, OSMutexPost_partial_solve_wit_40_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg prepared )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(UCOS2_inv sg prepared )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_41 : OSMutexPost_partial_solve_wit_41.
Proof.
  unfold OSMutexPost_partial_solve_wit_41.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56.
  intros h Hheap.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((prepared.(TskState) ))))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventGrpField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((prepared.(TskState) ))))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventGrpField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_42 : OSMutexPost_partial_solve_wit_42.
Proof.
  unfold OSMutexPost_partial_solve_wit_42.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53.
  intros h Hheap.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((prepared.(TskState) ))))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventGrpField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((prepared.(TskState) ))))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventGrpField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_43 : OSMutexPost_partial_solve_wit_43.
Proof.
  unfold OSMutexPost_partial_solve_wit_43.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43.
  intros h Hheap.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((prepared.(TskState) ))))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventGrpField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((prepared.(TskState) ))))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventGrpField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_44_pure : OSMutexPost_partial_solve_wit_44_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_44 : OSMutexPost_partial_solve_wit_44.
Proof.
  unfold OSMutexPost_partial_solve_wit_44, OSMutexPost_partial_solve_wit_44_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((prepared.(TskState) ))))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventGrpField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((prepared.(TskState) ))))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventGrpField )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_45_pure : OSMutexPost_partial_solve_wit_45_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_45 : OSMutexPost_partial_solve_wit_45.
Proof.
  unfold OSMutexPost_partial_solve_wit_45, OSMutexPost_partial_solve_wit_45_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((prepared.(TskState) ))))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventGrpField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((prepared.(TskState) ))))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventGrpField )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_46_pure : OSMutexPost_partial_solve_wit_46_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_46 : OSMutexPost_partial_solve_wit_46.
Proof.
  unfold OSMutexPost_partial_solve_wit_46, OSMutexPost_partial_solve_wit_46_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((prepared.(TskState) ))))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventGrpField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((prepared.(TskState) ))))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventGrpField )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_47_pure : OSMutexPost_partial_solve_wit_47_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_47 : OSMutexPost_partial_solve_wit_47.
Proof.
  unfold OSMutexPost_partial_solve_wit_47, OSMutexPost_partial_solve_wit_47_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared waiter waiting PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58.
  intros h Hheap.
  assert (Hspatial :
(event_task_rdy_pre sg (prepared.(TskState) ) eid current waiter waiting 16 0 (encode_ready_grp (((prepared.(SchedState) ).(readyList) )) ((prepared.(TskState) ))) (sched_row_values ((prepared.(TskState) )) (((prepared.(SchedState) ).(readyList) ))) )
  **  (mutex_del_wake_frame sg prepared eid waiter )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(event_task_rdy_pre sg (prepared.(TskState) ) eid current waiter waiting 16 0 (encode_ready_grp (((prepared.(SchedState) ).(readyList) )) ((prepared.(TskState) ))) (sched_row_values ((prepared.(TskState) )) (((prepared.(SchedState) ).(readyList) ))) )
  **  (mutex_del_wake_frame sg prepared eid waiter )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_48_pure : OSMutexPost_partial_solve_wit_48_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_48 : OSMutexPost_partial_solve_wit_48.
Proof.
  unfold OSMutexPost_partial_solve_wit_48, OSMutexPost_partial_solve_wit_48_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared waiter waiting PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55.
  intros h Hheap.
  assert (Hspatial :
(event_task_rdy_pre sg (prepared.(TskState) ) eid current waiter waiting 16 0 (encode_ready_grp (((prepared.(SchedState) ).(readyList) )) ((prepared.(TskState) ))) (sched_row_values ((prepared.(TskState) )) (((prepared.(SchedState) ).(readyList) ))) )
  **  (mutex_del_wake_frame sg prepared eid waiter )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(event_task_rdy_pre sg (prepared.(TskState) ) eid current waiter waiting 16 0 (encode_ready_grp (((prepared.(SchedState) ).(readyList) )) ((prepared.(TskState) ))) (sched_row_values ((prepared.(TskState) )) (((prepared.(SchedState) ).(readyList) ))) )
  **  (mutex_del_wake_frame sg prepared eid waiter )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_49_pure : OSMutexPost_partial_solve_wit_49_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_49 : OSMutexPost_partial_solve_wit_49.
Proof.
  unfold OSMutexPost_partial_solve_wit_49, OSMutexPost_partial_solve_wit_49_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node prepared waiter waiting PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45.
  intros h Hheap.
  assert (Hspatial :
(event_task_rdy_pre sg (prepared.(TskState) ) eid current waiter waiting 16 0 (encode_ready_grp (((prepared.(SchedState) ).(readyList) )) ((prepared.(TskState) ))) (sched_row_values ((prepared.(TskState) )) (((prepared.(SchedState) ).(readyList) ))) )
  **  (mutex_del_wake_frame sg prepared eid waiter )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(event_task_rdy_pre sg (prepared.(TskState) ) eid current waiter waiting 16 0 (encode_ready_grp (((prepared.(SchedState) ).(readyList) )) ((prepared.(TskState) ))) (sched_row_values ((prepared.(TskState) )) (((prepared.(SchedState) ).(readyList) ))) )
  **  (mutex_del_wake_frame sg prepared eid waiter )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_50_pure : OSMutexPost_partial_solve_wit_50_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_50 : OSMutexPost_partial_solve_wit_50.
Proof.
  unfold OSMutexPost_partial_solve_wit_50, OSMutexPost_partial_solve_wit_50_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node prepared waiter waiting retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45.
  intros h Hheap.
  assert (Hspatial :
(event_task_rdy_post sg (prepared.(TskState) ) eid current waiter waiting 0 16 0 (encode_ready_grp (((prepared.(SchedState) ).(readyList) )) ((prepared.(TskState) ))) (sched_row_values ((prepared.(TskState) )) (((prepared.(SchedState) ).(readyList) ))) retval_2 )
  **  (mutex_del_wake_frame sg prepared eid waiter )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(event_task_rdy_post sg (prepared.(TskState) ) eid current waiter waiting 0 16 0 (encode_ready_grp (((prepared.(SchedState) ).(readyList) )) ((prepared.(TskState) ))) (sched_row_values ((prepared.(TskState) )) (((prepared.(SchedState) ).(readyList) ))) retval_2 )
  **  (mutex_del_wake_frame sg prepared eid waiter )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_51_pure : OSMutexPost_partial_solve_wit_51_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_51 : OSMutexPost_partial_solve_wit_51.
Proof.
  unfold OSMutexPost_partial_solve_wit_51, OSMutexPost_partial_solve_wit_51_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared waiter waiting retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55.
  intros h Hheap.
  assert (Hspatial :
(event_task_rdy_post sg (prepared.(TskState) ) eid current waiter waiting 0 16 0 (encode_ready_grp (((prepared.(SchedState) ).(readyList) )) ((prepared.(TskState) ))) (sched_row_values ((prepared.(TskState) )) (((prepared.(SchedState) ).(readyList) ))) retval_3 )
  **  (mutex_del_wake_frame sg prepared eid waiter )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(event_task_rdy_post sg (prepared.(TskState) ) eid current waiter waiting 0 16 0 (encode_ready_grp (((prepared.(SchedState) ).(readyList) )) ((prepared.(TskState) ))) (sched_row_values ((prepared.(TskState) )) (((prepared.(SchedState) ).(readyList) ))) retval_3 )
  **  (mutex_del_wake_frame sg prepared eid waiter )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_52_pure : OSMutexPost_partial_solve_wit_52_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_52 : OSMutexPost_partial_solve_wit_52.
Proof.
  unfold OSMutexPost_partial_solve_wit_52, OSMutexPost_partial_solve_wit_52_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared waiter waiting retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58.
  intros h Hheap.
  assert (Hspatial :
(event_task_rdy_post sg (prepared.(TskState) ) eid current waiter waiting 0 16 0 (encode_ready_grp (((prepared.(SchedState) ).(readyList) )) ((prepared.(TskState) ))) (sched_row_values ((prepared.(TskState) )) (((prepared.(SchedState) ).(readyList) ))) retval_3 )
  **  (mutex_del_wake_frame sg prepared eid waiter )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(event_task_rdy_post sg (prepared.(TskState) ) eid current waiter waiting 0 16 0 (encode_ready_grp (((prepared.(SchedState) ).(readyList) )) ((prepared.(TskState) ))) (sched_row_values ((prepared.(TskState) )) (((prepared.(SchedState) ).(readyList) ))) retval_3 )
  **  (mutex_del_wake_frame sg prepared eid waiter )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_53 : OSMutexPost_partial_solve_wit_53.
Proof.
  unfold OSMutexPost_partial_solve_wit_53.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared waiter waiting retval_3 woken found PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67.
  intros h Hheap.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (found)))
  **  (mutex_post_commit_field_frame sg woken eid (event_image (sg) ((woken.(TskState) )) (found)) EventCntField )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current)))))))))
  **  (mutex_post_commit_field_frame sg woken eid (event_image (sg) ((woken.(TskState) )) (found)) EventCntField )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_54 : OSMutexPost_partial_solve_wit_54.
Proof.
  unfold OSMutexPost_partial_solve_wit_54.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared waiter waiting retval_3 woken found PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64.
  intros h Hheap.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (found)))
  **  (mutex_post_commit_field_frame sg woken eid (event_image (sg) ((woken.(TskState) )) (found)) EventCntField )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current)))))))))
  **  (mutex_post_commit_field_frame sg woken eid (event_image (sg) ((woken.(TskState) )) (found)) EventCntField )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_55 : OSMutexPost_partial_solve_wit_55.
Proof.
  unfold OSMutexPost_partial_solve_wit_55.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node prepared waiter waiting retval_2 woken found PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54.
  intros h Hheap.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (found)))
  **  (mutex_post_commit_field_frame sg woken eid (event_image (sg) ((woken.(TskState) )) (found)) EventCntField )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current)))))))))
  **  (mutex_post_commit_field_frame sg woken eid (event_image (sg) ((woken.(TskState) )) (found)) EventCntField )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_56_pure : OSMutexPost_partial_solve_wit_56_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_56 : OSMutexPost_partial_solve_wit_56.
Proof.
  unfold OSMutexPost_partial_solve_wit_56, OSMutexPost_partial_solve_wit_56_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval_2 acquired current mutex caller node prepared waiter waiting retval woken found PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land (encode_event_cnt_value ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current)))))))) 65280) retval))
  **  (mutex_post_commit_field_frame sg woken eid (event_image (sg) ((woken.(TskState) )) (found)) EventCntField )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land (encode_event_cnt_value (found)) 65280) retval))
  **  (mutex_post_commit_field_frame sg woken eid (event_image (sg) ((woken.(TskState) )) (found)) EventCntField )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_57_pure : OSMutexPost_partial_solve_wit_57_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_57 : OSMutexPost_partial_solve_wit_57.
Proof.
  unfold OSMutexPost_partial_solve_wit_57, OSMutexPost_partial_solve_wit_57_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval_2 acquired current mutex caller node retval_3 prepared waiter waiting retval woken found PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land (encode_event_cnt_value ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current)))))))) 65280) retval))
  **  (mutex_post_commit_field_frame sg woken eid (event_image (sg) ((woken.(TskState) )) (found)) EventCntField )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land (encode_event_cnt_value (found)) 65280) retval))
  **  (mutex_post_commit_field_frame sg woken eid (event_image (sg) ((woken.(TskState) )) (found)) EventCntField )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_58_pure : OSMutexPost_partial_solve_wit_58_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_58 : OSMutexPost_partial_solve_wit_58.
Proof.
  unfold OSMutexPost_partial_solve_wit_58, OSMutexPost_partial_solve_wit_58_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval_2 acquired current mutex caller node retval_3 prepared waiter waiting retval woken found PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land (encode_event_cnt_value ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current)))))))) 65280) retval))
  **  (mutex_post_commit_field_frame sg woken eid (event_image (sg) ((woken.(TskState) )) (found)) EventCntField )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land (encode_event_cnt_value (found)) 65280) retval))
  **  (mutex_post_commit_field_frame sg woken eid (event_image (sg) ((woken.(TskState) )) (found)) EventCntField )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_59 : OSMutexPost_partial_solve_wit_59.
Proof.
  unfold OSMutexPost_partial_solve_wit_59.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared waiter waiting retval_3 woken found PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67.
  intros h Hheap.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (encode_event_ptr_value (sg) (found)))
  **  (((( &( "OSTCBPrioTbl" ) ) + (retval_3 * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (waiter)))
  **  (mutex_post_native_owner_store_frame sg woken eid (event_write ((event_image (sg) ((woken.(TskState) )) (found))) (EventCntField) ((Some ((Z.lor (Z.land (encode_event_cnt_value (found)) 65280) retval_3))))) retval_3 )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (((( &( "OSTCBPrioTbl" ) ) + (retval_3 * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (waiter)))
  **  (mutex_post_native_owner_store_frame sg woken eid (event_write ((event_image (sg) ((woken.(TskState) )) (found))) (EventCntField) ((Some ((Z.lor (Z.land (encode_event_cnt_value (found)) 65280) retval_3))))) retval_3 )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { rewrite PreH57.
    sep_apply_l_atomic (store_ptr_undef_store_ptr
      (&(pe # "os_event" ->ₛ "OSEventPtr")) (encode_event_ptr_value sg found)).
    entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_60 : OSMutexPost_partial_solve_wit_60.
Proof.
  unfold OSMutexPost_partial_solve_wit_60.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared waiter waiting retval_3 woken found PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64.
  intros h Hheap.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (encode_event_ptr_value (sg) (found)))
  **  (((( &( "OSTCBPrioTbl" ) ) + (retval_3 * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (waiter)))
  **  (mutex_post_native_owner_store_frame sg woken eid (event_write ((event_image (sg) ((woken.(TskState) )) (found))) (EventCntField) ((Some ((Z.lor (Z.land (encode_event_cnt_value (found)) 65280) retval_3))))) retval_3 )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (((( &( "OSTCBPrioTbl" ) ) + (retval_3 * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (waiter)))
  **  (mutex_post_native_owner_store_frame sg woken eid (event_write ((event_image (sg) ((woken.(TskState) )) (found))) (EventCntField) ((Some ((Z.lor (Z.land (encode_event_cnt_value (found)) 65280) retval_3))))) retval_3 )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { rewrite PreH54.
    sep_apply_l_atomic (store_ptr_undef_store_ptr
      (&(pe # "os_event" ->ₛ "OSEventPtr")) (encode_event_ptr_value sg found)).
    entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_61 : OSMutexPost_partial_solve_wit_61.
Proof.
  unfold OSMutexPost_partial_solve_wit_61.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node prepared waiter waiting retval_2 woken found PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54.
  intros h Hheap.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (encode_event_ptr_value (sg) (found)))
  **  (((( &( "OSTCBPrioTbl" ) ) + (retval_2 * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (waiter)))
  **  (mutex_post_native_owner_store_frame sg woken eid (event_write ((event_image (sg) ((woken.(TskState) )) (found))) (EventCntField) ((Some ((Z.lor (Z.land (encode_event_cnt_value (found)) 65280) retval_2))))) retval_2 )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (((( &( "OSTCBPrioTbl" ) ) + (retval_2 * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (waiter)))
  **  (mutex_post_native_owner_store_frame sg woken eid (event_write ((event_image (sg) ((woken.(TskState) )) (found))) (EventCntField) ((Some ((Z.lor (Z.land (encode_event_cnt_value (found)) 65280) retval_2))))) retval_2 )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { rewrite PreH44.
    sep_apply_l_atomic (store_ptr_undef_store_ptr
      (&(pe # "os_event" ->ₛ "OSEventPtr")) (encode_event_ptr_value sg found)).
    entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_62_pure : OSMutexPost_partial_solve_wit_62_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_62 : OSMutexPost_partial_solve_wit_62.
Proof.
  unfold OSMutexPost_partial_solve_wit_62, OSMutexPost_partial_solve_wit_62_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval_2 acquired current mutex caller node prepared waiter waiting retval woken found PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (waiter)))
  **  (((( &( "OSTCBPrioTbl" ) ) + (retval * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (waiter)))
  **  (mutex_post_native_owner_store_frame sg woken eid (event_write ((event_image (sg) ((woken.(TskState) )) (found))) (EventCntField) ((Some ((Z.lor (Z.land (encode_event_cnt_value (found)) 65280) retval))))) retval )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (waiter)))
  **  (((( &( "OSTCBPrioTbl" ) ) + (retval * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (waiter)))
  **  (mutex_post_native_owner_store_frame sg woken eid (event_write ((event_image (sg) ((woken.(TskState) )) (found))) (EventCntField) ((Some ((Z.lor (Z.land (encode_event_cnt_value (found)) 65280) retval))))) retval )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_63_pure : OSMutexPost_partial_solve_wit_63_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_63 : OSMutexPost_partial_solve_wit_63.
Proof.
  unfold OSMutexPost_partial_solve_wit_63, OSMutexPost_partial_solve_wit_63_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval_2 acquired current mutex caller node retval_3 prepared waiter waiting retval woken found PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (waiter)))
  **  (((( &( "OSTCBPrioTbl" ) ) + (retval * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (waiter)))
  **  (mutex_post_native_owner_store_frame sg woken eid (event_write ((event_image (sg) ((woken.(TskState) )) (found))) (EventCntField) ((Some ((Z.lor (Z.land (encode_event_cnt_value (found)) 65280) retval))))) retval )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (waiter)))
  **  (((( &( "OSTCBPrioTbl" ) ) + (retval * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (waiter)))
  **  (mutex_post_native_owner_store_frame sg woken eid (event_write ((event_image (sg) ((woken.(TskState) )) (found))) (EventCntField) ((Some ((Z.lor (Z.land (encode_event_cnt_value (found)) 65280) retval))))) retval )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_64_pure : OSMutexPost_partial_solve_wit_64_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_64 : OSMutexPost_partial_solve_wit_64.
Proof.
  unfold OSMutexPost_partial_solve_wit_64, OSMutexPost_partial_solve_wit_64_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval_2 acquired current mutex caller node retval_3 prepared waiter waiting retval woken found PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (waiter)))
  **  (((( &( "OSTCBPrioTbl" ) ) + (retval * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (waiter)))
  **  (mutex_post_native_owner_store_frame sg woken eid (event_write ((event_image (sg) ((woken.(TskState) )) (found))) (EventCntField) ((Some ((Z.lor (Z.land (encode_event_cnt_value (found)) 65280) retval))))) retval )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (task_slot_addr (sg) (waiter)))
  **  (((( &( "OSTCBPrioTbl" ) ) + (retval * sizeof(PTR)))) # Ptr  |-> (task_slot_addr (sg) (waiter)))
  **  (mutex_post_native_owner_store_frame sg woken eid (event_write ((event_image (sg) ((woken.(TskState) )) (found))) (EventCntField) ((Some ((Z.lor (Z.land (encode_event_cnt_value (found)) 65280) retval))))) retval )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval_2 acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_65_pure : OSMutexPost_partial_solve_wit_65_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_65 : OSMutexPost_partial_solve_wit_65.
Proof.
  unfold OSMutexPost_partial_solve_wit_65, OSMutexPost_partial_solve_wit_65_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_3 prepared waiter waiting retval_2 woken found committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg committed )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg committed )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. try rewrite PreH68. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_66_pure : OSMutexPost_partial_solve_wit_66_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_66 : OSMutexPost_partial_solve_wit_66.
Proof.
  unfold OSMutexPost_partial_solve_wit_66, OSMutexPost_partial_solve_wit_66_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_3 prepared waiter waiting retval_2 woken found committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg committed )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg committed )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. try rewrite PreH68. try rewrite PreH69. try rewrite PreH70. try rewrite PreH71. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_67_pure : OSMutexPost_partial_solve_wit_67_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_67 : OSMutexPost_partial_solve_wit_67.
Proof.
  unfold OSMutexPost_partial_solve_wit_67, OSMutexPost_partial_solve_wit_67_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared waiter waiting retval_3 woken found committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_restore_pre source_env external platform critical saved_local sg call mask retval acquired committed )
|--
(mutex_post_api_restore_pre source_env external platform critical saved_local sg call mask retval acquired (mutex_post_owner_state ((event_wake_state (sg) (prepared) (eid) (current) (waiter) (waiting) (PendMutex) (0) (PendOK))) (eid) ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current))))))) (mutex) ((Some (waiter))) ((Some (retval_3)))) )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. try rewrite PreH68. try rewrite PreH69. try rewrite PreH70. try rewrite PreH71. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_68_pure : OSMutexPost_partial_solve_wit_68_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_68 : OSMutexPost_partial_solve_wit_68.
Proof.
  unfold OSMutexPost_partial_solve_wit_68, OSMutexPost_partial_solve_wit_68_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared waiter waiting retval_3 woken found committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_restore_pre source_env external platform critical saved_local sg call mask retval acquired committed )
|--
(mutex_post_api_restore_pre source_env external platform critical saved_local sg call mask retval acquired (mutex_post_owner_state ((event_wake_state (sg) (prepared) (eid) (current) (waiter) (waiting) (PendMutex) (0) (PendOK))) (eid) ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current))))))) (mutex) ((Some (waiter))) ((Some (retval_3)))) )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. try rewrite PreH68. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_69_pure : OSMutexPost_partial_solve_wit_69_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_69 : OSMutexPost_partial_solve_wit_69.
Proof.
  unfold OSMutexPost_partial_solve_wit_69, OSMutexPost_partial_solve_wit_69_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared waiter waiting retval_3 woken found committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_restore_source_post source_env external platform critical saved_local sg call mask (mutex_post_owner_state ((event_wake_state (sg) (prepared) (eid) (current) (waiter) (waiting) (PendMutex) (0) (PendOK))) (eid) ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current))))))) (mutex) ((Some (waiter))) ((Some (retval_3)))) )
|--
(mutex_post_api_restore_source_post source_env external platform critical saved_local sg call mask (mutex_post_owner_state ((event_wake_state (sg) (prepared) (eid) (current) (waiter) (waiting) (PendMutex) (0) (PendOK))) (eid) ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current))))))) (mutex) ((Some (waiter))) ((Some (retval_3)))) )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. try rewrite PreH68. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_70_pure : OSMutexPost_partial_solve_wit_70_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_70 : OSMutexPost_partial_solve_wit_70.
Proof.
  unfold OSMutexPost_partial_solve_wit_70, OSMutexPost_partial_solve_wit_70_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared waiter waiting retval_3 woken found committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_restore_source_post source_env external platform critical saved_local sg call mask (mutex_post_owner_state ((event_wake_state (sg) (prepared) (eid) (current) (waiter) (waiting) (PendMutex) (0) (PendOK))) (eid) ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current))))))) (mutex) ((Some (waiter))) ((Some (retval_3)))) )
|--
(mutex_post_api_restore_source_post source_env external platform critical saved_local sg call mask (mutex_post_owner_state ((event_wake_state (sg) (prepared) (eid) (current) (waiter) (waiting) (PendMutex) (0) (PendOK))) (eid) ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current))))))) (mutex) ((Some (waiter))) ((Some (retval_3)))) )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. try rewrite PreH68. try rewrite PreH69. try rewrite PreH70. try rewrite PreH71. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_71_pure : OSMutexPost_partial_solve_wit_71_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_71 : OSMutexPost_partial_solve_wit_71.
Proof.
  unfold OSMutexPost_partial_solve_wit_71, OSMutexPost_partial_solve_wit_71_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared waiter waiting retval_3 woken found committed unmasked restored PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71 PreH72 PreH73 PreH74 PreH75 PreH76.
  intros h Hheap.
  assert (Hspatial :
(os_sched_continuation_call_pre (mutex_del_runtime_sched_environment (source_env)) saved_local mutex_del_stack_resources sg restored mask unmasked )
|--
(os_sched_continuation_call_pre (mutex_del_runtime_sched_environment (source_env)) saved_local mutex_del_stack_resources sg restored mask unmasked )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. try rewrite PreH68. try rewrite PreH69. try rewrite PreH70. try rewrite PreH71. try rewrite PreH72. try rewrite PreH73. try rewrite PreH74. try rewrite PreH75. try rewrite PreH76. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_72_pure : OSMutexPost_partial_solve_wit_72_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_72 : OSMutexPost_partial_solve_wit_72.
Proof.
  unfold OSMutexPost_partial_solve_wit_72, OSMutexPost_partial_solve_wit_72_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared waiter waiting retval_3 woken found committed unmasked restored PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71 PreH72 PreH73.
  intros h Hheap.
  assert (Hspatial :
(os_sched_continuation_call_pre (mutex_del_runtime_sched_environment (source_env)) saved_local mutex_del_stack_resources sg restored mask unmasked )
|--
(os_sched_continuation_call_pre (mutex_del_runtime_sched_environment (source_env)) saved_local mutex_del_stack_resources sg restored mask unmasked )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. try rewrite PreH68. try rewrite PreH69. try rewrite PreH70. try rewrite PreH71. try rewrite PreH72. try rewrite PreH73. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_73_pure : OSMutexPost_partial_solve_wit_73_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_73 : OSMutexPost_partial_solve_wit_73.
Proof.
  unfold OSMutexPost_partial_solve_wit_73, OSMutexPost_partial_solve_wit_73_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval_2 acquired current mutex caller node retval_3 prepared waiter waiting retval woken found committed unmasked restored PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71 PreH72 PreH73 PreH74.
  intros h Hheap.
  assert (Hspatial :
(sched_del_history_return_post (mutex_del_runtime_sched_environment (source_env)) critical saved_local sg restored mask unmasked )
|--
(sched_del_history_return_post (mutex_del_runtime_sched_environment (source_env)) critical saved_local sg restored mask unmasked )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. try rewrite PreH68. try rewrite PreH69. try rewrite PreH70. try rewrite PreH71. try rewrite PreH72. try rewrite PreH73. try rewrite PreH74. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_74_pure : OSMutexPost_partial_solve_wit_74_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_74 : OSMutexPost_partial_solve_wit_74.
Proof.
  unfold OSMutexPost_partial_solve_wit_74, OSMutexPost_partial_solve_wit_74_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval_2 acquired current mutex caller node retval_3 prepared waiter waiting retval woken found committed unmasked restored PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71 PreH72 PreH73 PreH74 PreH75 PreH76 PreH77.
  intros h Hheap.
  assert (Hspatial :
(sched_del_history_return_post (mutex_del_runtime_sched_environment (source_env)) critical saved_local sg restored mask unmasked )
|--
(sched_del_history_return_post (mutex_del_runtime_sched_environment (source_env)) critical saved_local sg restored mask unmasked )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. try rewrite PreH68. try rewrite PreH69. try rewrite PreH70. try rewrite PreH71. try rewrite PreH72. try rewrite PreH73. try rewrite PreH74. try rewrite PreH75. try rewrite PreH76. try rewrite PreH77. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_75_pure : OSMutexPost_partial_solve_wit_75_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_75 : OSMutexPost_partial_solve_wit_75.
Proof.
  unfold OSMutexPost_partial_solve_wit_75, OSMutexPost_partial_solve_wit_75_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_3 prepared waiter waiting retval_2 woken found committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg committed )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg committed )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. try rewrite PreH68. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_76_pure : OSMutexPost_partial_solve_wit_76_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_76 : OSMutexPost_partial_solve_wit_76.
Proof.
  unfold OSMutexPost_partial_solve_wit_76, OSMutexPost_partial_solve_wit_76_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_3 prepared waiter waiting retval_2 woken found committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg committed )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg committed )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. try rewrite PreH68. try rewrite PreH69. try rewrite PreH70. try rewrite PreH71. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_77_pure : OSMutexPost_partial_solve_wit_77_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_77 : OSMutexPost_partial_solve_wit_77.
Proof.
  unfold OSMutexPost_partial_solve_wit_77, OSMutexPost_partial_solve_wit_77_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node prepared waiter waiting retval_2 woken found committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg committed )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg committed )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_78_pure : OSMutexPost_partial_solve_wit_78_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_78 : OSMutexPost_partial_solve_wit_78.
Proof.
  unfold OSMutexPost_partial_solve_wit_78, OSMutexPost_partial_solve_wit_78_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node prepared waiter waiting retval_2 woken found committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_restore_pre source_env external platform critical saved_local sg call mask retval acquired committed )
|--
(mutex_post_api_restore_pre source_env external platform critical saved_local sg call mask retval acquired (mutex_post_owner_state ((event_wake_state (sg) (prepared) (eid) (current) (waiter) (waiting) (PendMutex) (0) (PendOK))) (eid) ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current))))))) (mutex) ((Some (waiter))) ((Some (retval_2)))) )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_79_pure : OSMutexPost_partial_solve_wit_79_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_79 : OSMutexPost_partial_solve_wit_79.
Proof.
  unfold OSMutexPost_partial_solve_wit_79, OSMutexPost_partial_solve_wit_79_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared waiter waiting retval_3 woken found committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_restore_pre source_env external platform critical saved_local sg call mask retval acquired committed )
|--
(mutex_post_api_restore_pre source_env external platform critical saved_local sg call mask retval acquired (mutex_post_owner_state ((event_wake_state (sg) (prepared) (eid) (current) (waiter) (waiting) (PendMutex) (0) (PendOK))) (eid) ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current))))))) (mutex) ((Some (waiter))) ((Some (retval_3)))) )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. try rewrite PreH68. try rewrite PreH69. try rewrite PreH70. try rewrite PreH71. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_80_pure : OSMutexPost_partial_solve_wit_80_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_80 : OSMutexPost_partial_solve_wit_80.
Proof.
  unfold OSMutexPost_partial_solve_wit_80, OSMutexPost_partial_solve_wit_80_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared waiter waiting retval_3 woken found committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_restore_pre source_env external platform critical saved_local sg call mask retval acquired committed )
|--
(mutex_post_api_restore_pre source_env external platform critical saved_local sg call mask retval acquired (mutex_post_owner_state ((event_wake_state (sg) (prepared) (eid) (current) (waiter) (waiting) (PendMutex) (0) (PendOK))) (eid) ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current))))))) (mutex) ((Some (waiter))) ((Some (retval_3)))) )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. try rewrite PreH68. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_81_pure : OSMutexPost_partial_solve_wit_81_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_81 : OSMutexPost_partial_solve_wit_81.
Proof.
  unfold OSMutexPost_partial_solve_wit_81, OSMutexPost_partial_solve_wit_81_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared waiter waiting retval_3 woken found committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_restore_source_post source_env external platform critical saved_local sg call mask (mutex_post_owner_state ((event_wake_state (sg) (prepared) (eid) (current) (waiter) (waiting) (PendMutex) (0) (PendOK))) (eid) ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current))))))) (mutex) ((Some (waiter))) ((Some (retval_3)))) )
|--
(mutex_post_api_restore_source_post source_env external platform critical saved_local sg call mask (mutex_post_owner_state ((event_wake_state (sg) (prepared) (eid) (current) (waiter) (waiting) (PendMutex) (0) (PendOK))) (eid) ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current))))))) (mutex) ((Some (waiter))) ((Some (retval_3)))) )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. try rewrite PreH68. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_82_pure : OSMutexPost_partial_solve_wit_82_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_82 : OSMutexPost_partial_solve_wit_82.
Proof.
  unfold OSMutexPost_partial_solve_wit_82, OSMutexPost_partial_solve_wit_82_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared waiter waiting retval_3 woken found committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_restore_source_post source_env external platform critical saved_local sg call mask (mutex_post_owner_state ((event_wake_state (sg) (prepared) (eid) (current) (waiter) (waiting) (PendMutex) (0) (PendOK))) (eid) ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current))))))) (mutex) ((Some (waiter))) ((Some (retval_3)))) )
|--
(mutex_post_api_restore_source_post source_env external platform critical saved_local sg call mask (mutex_post_owner_state ((event_wake_state (sg) (prepared) (eid) (current) (waiter) (waiting) (PendMutex) (0) (PendOK))) (eid) ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current))))))) (mutex) ((Some (waiter))) ((Some (retval_3)))) )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. try rewrite PreH68. try rewrite PreH69. try rewrite PreH70. try rewrite PreH71. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_83_pure : OSMutexPost_partial_solve_wit_83_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_83 : OSMutexPost_partial_solve_wit_83.
Proof.
  unfold OSMutexPost_partial_solve_wit_83, OSMutexPost_partial_solve_wit_83_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node prepared waiter waiting retval_2 woken found committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_restore_source_post source_env external platform critical saved_local sg call mask (mutex_post_owner_state ((event_wake_state (sg) (prepared) (eid) (current) (waiter) (waiting) (PendMutex) (0) (PendOK))) (eid) ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current))))))) (mutex) ((Some (waiter))) ((Some (retval_2)))) )
|--
(mutex_post_api_restore_source_post source_env external platform critical saved_local sg call mask (mutex_post_owner_state ((event_wake_state (sg) (prepared) (eid) (current) (waiter) (waiting) (PendMutex) (0) (PendOK))) (eid) ((event_set_wait_list (current) ((remove_Z_eqb (waiter) ((waitList (current))))))) (mutex) ((Some (waiter))) ((Some (retval_2)))) )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_84_pure : OSMutexPost_partial_solve_wit_84_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_84 : OSMutexPost_partial_solve_wit_84.
Proof.
  unfold OSMutexPost_partial_solve_wit_84, OSMutexPost_partial_solve_wit_84_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node prepared waiter waiting retval_2 woken found committed unmasked restored PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62.
  intros h Hheap.
  assert (Hspatial :
(os_sched_continuation_call_pre (mutex_del_runtime_sched_environment (source_env)) saved_local mutex_del_stack_resources sg restored mask unmasked )
|--
(os_sched_continuation_call_pre (mutex_del_runtime_sched_environment (source_env)) saved_local mutex_del_stack_resources sg restored mask unmasked )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_85_pure : OSMutexPost_partial_solve_wit_85_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_85 : OSMutexPost_partial_solve_wit_85.
Proof.
  unfold OSMutexPost_partial_solve_wit_85, OSMutexPost_partial_solve_wit_85_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared waiter waiting retval_3 woken found committed unmasked restored PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71 PreH72 PreH73 PreH74 PreH75 PreH76.
  intros h Hheap.
  assert (Hspatial :
(os_sched_continuation_call_pre (mutex_del_runtime_sched_environment (source_env)) saved_local mutex_del_stack_resources sg restored mask unmasked )
|--
(os_sched_continuation_call_pre (mutex_del_runtime_sched_environment (source_env)) saved_local mutex_del_stack_resources sg restored mask unmasked )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. try rewrite PreH68. try rewrite PreH69. try rewrite PreH70. try rewrite PreH71. try rewrite PreH72. try rewrite PreH73. try rewrite PreH74. try rewrite PreH75. try rewrite PreH76. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_86_pure : OSMutexPost_partial_solve_wit_86_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_86 : OSMutexPost_partial_solve_wit_86.
Proof.
  unfold OSMutexPost_partial_solve_wit_86, OSMutexPost_partial_solve_wit_86_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared waiter waiting retval_3 woken found committed unmasked restored PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71 PreH72 PreH73.
  intros h Hheap.
  assert (Hspatial :
(os_sched_continuation_call_pre (mutex_del_runtime_sched_environment (source_env)) saved_local mutex_del_stack_resources sg restored mask unmasked )
|--
(os_sched_continuation_call_pre (mutex_del_runtime_sched_environment (source_env)) saved_local mutex_del_stack_resources sg restored mask unmasked )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. try rewrite PreH68. try rewrite PreH69. try rewrite PreH70. try rewrite PreH71. try rewrite PreH72. try rewrite PreH73. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_87_pure : OSMutexPost_partial_solve_wit_87_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_87 : OSMutexPost_partial_solve_wit_87.
Proof.
  unfold OSMutexPost_partial_solve_wit_87, OSMutexPost_partial_solve_wit_87_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval_2 acquired current mutex caller node retval_3 prepared waiter waiting retval woken found committed unmasked restored PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71 PreH72 PreH73 PreH74.
  intros h Hheap.
  assert (Hspatial :
(sched_del_history_return_post (mutex_del_runtime_sched_environment (source_env)) critical saved_local sg restored mask unmasked )
|--
(sched_del_history_return_post (mutex_del_runtime_sched_environment (source_env)) critical saved_local sg restored mask unmasked )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. try rewrite PreH68. try rewrite PreH69. try rewrite PreH70. try rewrite PreH71. try rewrite PreH72. try rewrite PreH73. try rewrite PreH74. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_88_pure : OSMutexPost_partial_solve_wit_88_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_88 : OSMutexPost_partial_solve_wit_88.
Proof.
  unfold OSMutexPost_partial_solve_wit_88, OSMutexPost_partial_solve_wit_88_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval_2 acquired current mutex caller node retval_3 prepared waiter waiting retval woken found committed unmasked restored PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71 PreH72 PreH73 PreH74 PreH75 PreH76 PreH77.
  intros h Hheap.
  assert (Hspatial :
(sched_del_history_return_post (mutex_del_runtime_sched_environment (source_env)) critical saved_local sg restored mask unmasked )
|--
(sched_del_history_return_post (mutex_del_runtime_sched_environment (source_env)) critical saved_local sg restored mask unmasked )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. try rewrite PreH64. try rewrite PreH65. try rewrite PreH66. try rewrite PreH67. try rewrite PreH68. try rewrite PreH69. try rewrite PreH70. try rewrite PreH71. try rewrite PreH72. try rewrite PreH73. try rewrite PreH74. try rewrite PreH75. try rewrite PreH76. try rewrite PreH77. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_89_pure : OSMutexPost_partial_solve_wit_89_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_89 : OSMutexPost_partial_solve_wit_89.
Proof.
  unfold OSMutexPost_partial_solve_wit_89, OSMutexPost_partial_solve_wit_89_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval_2 acquired current mutex caller node prepared waiter waiting retval woken found committed unmasked restored PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63.
  intros h Hheap.
  assert (Hspatial :
(sched_del_history_return_post (mutex_del_runtime_sched_environment (source_env)) critical saved_local sg restored mask unmasked )
|--
(sched_del_history_return_post (mutex_del_runtime_sched_environment (source_env)) critical saved_local sg restored mask unmasked )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. try rewrite PreH60. try rewrite PreH61. try rewrite PreH62. try rewrite PreH63. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_90_pure : OSMutexPost_partial_solve_wit_90_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_90 : OSMutexPost_partial_solve_wit_90.
Proof.
  unfold OSMutexPost_partial_solve_wit_90, OSMutexPost_partial_solve_wit_90_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((prepared.(TskState) ))))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventGrpField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((prepared.(TskState) ))))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventGrpField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_91_pure : OSMutexPost_partial_solve_wit_91_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_91 : OSMutexPost_partial_solve_wit_91.
Proof.
  unfold OSMutexPost_partial_solve_wit_91, OSMutexPost_partial_solve_wit_91_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((prepared.(TskState) ))))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventGrpField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((prepared.(TskState) ))))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventGrpField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_92_pure : OSMutexPost_partial_solve_wit_92_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_92 : OSMutexPost_partial_solve_wit_92.
Proof.
  unfold OSMutexPost_partial_solve_wit_92, OSMutexPost_partial_solve_wit_92_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((prepared.(TskState) ))))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventGrpField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (current))) ((prepared.(TskState) ))))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventGrpField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_93 : OSMutexPost_partial_solve_wit_93.
Proof.
  unfold OSMutexPost_partial_solve_wit_93.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57.
  intros h Hheap.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventCntField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventCntField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_94 : OSMutexPost_partial_solve_wit_94.
Proof.
  unfold OSMutexPost_partial_solve_wit_94.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54.
  intros h Hheap.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventCntField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventCntField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_95 : OSMutexPost_partial_solve_wit_95.
Proof.
  unfold OSMutexPost_partial_solve_wit_95.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44.
  intros h Hheap.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventCntField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (encode_event_cnt_value (current)))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventCntField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_96_pure : OSMutexPost_partial_solve_wit_96_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_96 : OSMutexPost_partial_solve_wit_96.
Proof.
  unfold OSMutexPost_partial_solve_wit_96, OSMutexPost_partial_solve_wit_96_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((encode_event_cnt_value (current))) (16)) 255))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventCntField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((encode_event_cnt_value (current))) (16)) 255))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventCntField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_97_pure : OSMutexPost_partial_solve_wit_97_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_97 : OSMutexPost_partial_solve_wit_97.
Proof.
  unfold OSMutexPost_partial_solve_wit_97, OSMutexPost_partial_solve_wit_97_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((encode_event_cnt_value (current))) (16)) 255))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventCntField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((encode_event_cnt_value (current))) (16)) 255))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventCntField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_98_pure : OSMutexPost_partial_solve_wit_98_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_98 : OSMutexPost_partial_solve_wit_98.
Proof.
  unfold OSMutexPost_partial_solve_wit_98, OSMutexPost_partial_solve_wit_98_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((encode_event_cnt_value (current))) (16)) 255))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventCntField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((encode_event_cnt_value (current))) (16)) 255))
  **  (mutex_post_commit_field_frame sg prepared eid (event_image (sg) ((prepared.(TskState) )) (current)) EventCntField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_99 : OSMutexPost_partial_solve_wit_99.
Proof.
  unfold OSMutexPost_partial_solve_wit_99.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57.
  intros h Hheap.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (encode_event_ptr_value (sg) (current)))
  **  (mutex_post_commit_field_frame sg prepared eid (event_write ((event_image (sg) ((prepared.(TskState) )) (current))) (EventCntField) ((Some ((Z.lor (encode_event_cnt_value (current)) 255))))) EventPtrField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (mutex_post_commit_field_frame sg prepared eid (event_write ((event_image (sg) ((prepared.(TskState) )) (current))) (EventCntField) ((Some ((Z.lor (encode_event_cnt_value (current)) 255))))) EventPtrField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { rewrite PreH47.
    sep_apply_l_atomic (store_ptr_undef_store_ptr
      (&(pe # "os_event" ->ₛ "OSEventPtr")) (encode_event_ptr_value sg current)).
    entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_100 : OSMutexPost_partial_solve_wit_100.
Proof.
  unfold OSMutexPost_partial_solve_wit_100.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54.
  intros h Hheap.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (encode_event_ptr_value (sg) (current)))
  **  (mutex_post_commit_field_frame sg prepared eid (event_write ((event_image (sg) ((prepared.(TskState) )) (current))) (EventCntField) ((Some ((Z.lor (encode_event_cnt_value (current)) 255))))) EventPtrField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (mutex_post_commit_field_frame sg prepared eid (event_write ((event_image (sg) ((prepared.(TskState) )) (current))) (EventCntField) ((Some ((Z.lor (encode_event_cnt_value (current)) 255))))) EventPtrField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { rewrite PreH44.
    sep_apply_l_atomic (store_ptr_undef_store_ptr
      (&(pe # "os_event" ->ₛ "OSEventPtr")) (encode_event_ptr_value sg current)).
    entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_101 : OSMutexPost_partial_solve_wit_101.
Proof.
  unfold OSMutexPost_partial_solve_wit_101.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44.
  intros h Hheap.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (encode_event_ptr_value (sg) (current)))
  **  (mutex_post_commit_field_frame sg prepared eid (event_write ((event_image (sg) ((prepared.(TskState) )) (current))) (EventCntField) ((Some ((Z.lor (encode_event_cnt_value (current)) 255))))) EventPtrField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  (mutex_post_commit_field_frame sg prepared eid (event_write ((event_image (sg) ((prepared.(TskState) )) (current))) (EventCntField) ((Some ((Z.lor (encode_event_cnt_value (current)) 255))))) EventPtrField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { rewrite PreH34.
    sep_apply_l_atomic (store_ptr_undef_store_ptr
      (&(pe # "os_event" ->ₛ "OSEventPtr")) (encode_event_ptr_value sg current)).
    entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_102_pure : OSMutexPost_partial_solve_wit_102_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_102 : OSMutexPost_partial_solve_wit_102.
Proof.
  unfold OSMutexPost_partial_solve_wit_102, OSMutexPost_partial_solve_wit_102_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (mutex_post_commit_field_frame sg prepared eid (event_write ((event_image (sg) ((prepared.(TskState) )) (current))) (EventCntField) ((Some ((Z.lor (encode_event_cnt_value (current)) 255))))) EventPtrField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (mutex_post_commit_field_frame sg prepared eid (event_write ((event_image (sg) ((prepared.(TskState) )) (current))) (EventCntField) ((Some ((Z.lor (encode_event_cnt_value (current)) 255))))) EventPtrField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_103_pure : OSMutexPost_partial_solve_wit_103_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_103 : OSMutexPost_partial_solve_wit_103.
Proof.
  unfold OSMutexPost_partial_solve_wit_103, OSMutexPost_partial_solve_wit_103_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (mutex_post_commit_field_frame sg prepared eid (event_write ((event_image (sg) ((prepared.(TskState) )) (current))) (EventCntField) ((Some ((Z.lor (encode_event_cnt_value (current)) 255))))) EventPtrField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (mutex_post_commit_field_frame sg prepared eid (event_write ((event_image (sg) ((prepared.(TskState) )) (current))) (EventCntField) ((Some ((Z.lor (encode_event_cnt_value (current)) 255))))) EventPtrField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_104_pure : OSMutexPost_partial_solve_wit_104_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_104 : OSMutexPost_partial_solve_wit_104.
Proof.
  unfold OSMutexPost_partial_solve_wit_104, OSMutexPost_partial_solve_wit_104_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57.
  intros h Hheap.
  assert (Hspatial :
((&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (mutex_post_commit_field_frame sg prepared eid (event_write ((event_image (sg) ((prepared.(TskState) )) (current))) (EventCntField) ((Some ((Z.lor (encode_event_cnt_value (current)) 255))))) EventPtrField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (mutex_post_commit_field_frame sg prepared eid (event_write ((event_image (sg) ((prepared.(TskState) )) (current))) (EventCntField) ((Some ((Z.lor (encode_event_cnt_value (current)) 255))))) EventPtrField )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_105_pure : OSMutexPost_partial_solve_wit_105_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_105 : OSMutexPost_partial_solve_wit_105.
Proof.
  unfold OSMutexPost_partial_solve_wit_105, OSMutexPost_partial_solve_wit_105_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node prepared committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg committed )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg committed )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_106_pure : OSMutexPost_partial_solve_wit_106_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_106 : OSMutexPost_partial_solve_wit_106.
Proof.
  unfold OSMutexPost_partial_solve_wit_106, OSMutexPost_partial_solve_wit_106_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg committed )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg committed )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_107_pure : OSMutexPost_partial_solve_wit_107_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_107 : OSMutexPost_partial_solve_wit_107.
Proof.
  unfold OSMutexPost_partial_solve_wit_107, OSMutexPost_partial_solve_wit_107_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg committed )
  **  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )
|--
(critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg committed )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg call acquired )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_108_pure : OSMutexPost_partial_solve_wit_108_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_108 : OSMutexPost_partial_solve_wit_108.
Proof.
  unfold OSMutexPost_partial_solve_wit_108, OSMutexPost_partial_solve_wit_108_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_restore_pre source_env external platform critical saved_local sg call mask retval acquired committed )
|--
(mutex_post_api_restore_pre source_env external platform critical saved_local sg call mask retval acquired (mutex_post_owner_state (prepared) (eid) (current) (mutex) (None) (None)) )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_109_pure : OSMutexPost_partial_solve_wit_109_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_109 : OSMutexPost_partial_solve_wit_109.
Proof.
  unfold OSMutexPost_partial_solve_wit_109, OSMutexPost_partial_solve_wit_109_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_restore_pre source_env external platform critical saved_local sg call mask retval acquired committed )
|--
(mutex_post_api_restore_pre source_env external platform critical saved_local sg call mask retval acquired (mutex_post_owner_state (prepared) (eid) (current) (mutex) (None) (None)) )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_110_pure : OSMutexPost_partial_solve_wit_110_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_110 : OSMutexPost_partial_solve_wit_110.
Proof.
  unfold OSMutexPost_partial_solve_wit_110, OSMutexPost_partial_solve_wit_110_aux.
  intros H_pure.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node prepared committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_restore_pre source_env external platform critical saved_local sg call mask retval acquired committed )
|--
(mutex_post_api_restore_pre source_env external platform critical saved_local sg call mask retval acquired (mutex_post_owner_state (prepared) (eid) (current) (mutex) (None) (None)) )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_111 : OSMutexPost_partial_solve_wit_111.
Proof.
  unfold OSMutexPost_partial_solve_wit_111.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node prepared committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_restore_source_post source_env external platform critical saved_local sg call mask (mutex_post_owner_state (prepared) (eid) (current) (mutex) (None) (None)) )
|--
(mutex_post_api_restore_source_post source_env external platform critical saved_local sg call mask (mutex_post_owner_state (prepared) (eid) (current) (mutex) (None) (None)) )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_112 : OSMutexPost_partial_solve_wit_112.
Proof.
  unfold OSMutexPost_partial_solve_wit_112.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_restore_source_post source_env external platform critical saved_local sg call mask (mutex_post_owner_state (prepared) (eid) (current) (mutex) (None) (None)) )
|--
(mutex_post_api_restore_source_post source_env external platform critical saved_local sg call mask (mutex_post_owner_state (prepared) (eid) (current) (mutex) (None) (None)) )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexPost_partial_solve_wit_113 : OSMutexPost_partial_solve_wit_113.
Proof.
  unfold OSMutexPost_partial_solve_wit_113.
  intros pevent_pre X pe observed eid before mask origin invocation call sg critical platform external saved_local source_env retval acquired current mutex caller node retval_2 prepared committed PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59.
  intros h Hheap.
  assert (Hspatial :
(mutex_post_api_restore_source_post source_env external platform critical saved_local sg call mask (mutex_post_owner_state (prepared) (eid) (current) (mutex) (None) (None)) )
|--
(mutex_post_api_restore_source_post source_env external platform critical saved_local sg call mask (mutex_post_owner_state (prepared) (eid) (current) (mutex) (None) (None)) )).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. try rewrite PreH48. try rewrite PreH49. try rewrite PreH50. try rewrite PreH51. try rewrite PreH52. try rewrite PreH53. try rewrite PreH54. try rewrite PreH55. try rewrite PreH56. try rewrite PreH57. try rewrite PreH58. try rewrite PreH59. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

