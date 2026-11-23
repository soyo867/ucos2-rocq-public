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
From Ucos2Verify.VC.code.mutex Require Import mutex_del_api_goal.
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
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_api_program_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_sched_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_program_storage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_proofs.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_stage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_source_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_region_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_proofs.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
Local Open Scope sac_scope.
Local Open Scope sac.

Lemma proof_of_OSMutexDel_safety_wit_1 : OSMutexDel_safety_wit_1.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_2 : OSMutexDel_safety_wit_2.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_3 : OSMutexDel_safety_wit_3.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_6 : OSMutexDel_safety_wit_6.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_7 : OSMutexDel_safety_wit_7.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_8 : OSMutexDel_safety_wit_8.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_9 : OSMutexDel_safety_wit_9.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_10 : OSMutexDel_safety_wit_10.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_11 : OSMutexDel_safety_wit_11.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_12 : OSMutexDel_safety_wit_12.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_13 : OSMutexDel_safety_wit_13.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_22 : OSMutexDel_safety_wit_22.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_23 : OSMutexDel_safety_wit_23.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_24 : OSMutexDel_safety_wit_24.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_25 : OSMutexDel_safety_wit_25.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_26 : OSMutexDel_safety_wit_26.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_27 : OSMutexDel_safety_wit_27.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_28 : OSMutexDel_safety_wit_28.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_29 : OSMutexDel_safety_wit_29.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_30 : OSMutexDel_safety_wit_30.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_31 : OSMutexDel_safety_wit_31.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_32 : OSMutexDel_safety_wit_32.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_33 : OSMutexDel_safety_wit_33.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_34 : OSMutexDel_safety_wit_34.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_35 : OSMutexDel_safety_wit_35.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_36 : OSMutexDel_safety_wit_36.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_37 : OSMutexDel_safety_wit_37.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_38 : OSMutexDel_safety_wit_38.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_40 : OSMutexDel_safety_wit_40.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_41 : OSMutexDel_safety_wit_41.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_42 : OSMutexDel_safety_wit_42.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_43 : OSMutexDel_safety_wit_43.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_44 : OSMutexDel_safety_wit_44.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_45 : OSMutexDel_safety_wit_45.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_46 : OSMutexDel_safety_wit_46.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_47 : OSMutexDel_safety_wit_47.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_48 : OSMutexDel_safety_wit_48.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_49 : OSMutexDel_safety_wit_49.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_50 : OSMutexDel_safety_wit_50.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_51 : OSMutexDel_safety_wit_51.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_52 : OSMutexDel_safety_wit_52.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_53 : OSMutexDel_safety_wit_53.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_54 : OSMutexDel_safety_wit_54.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_55 : OSMutexDel_safety_wit_55.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_56 : OSMutexDel_safety_wit_56.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_57 : OSMutexDel_safety_wit_57.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_58 : OSMutexDel_safety_wit_58.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_59 : OSMutexDel_safety_wit_59.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_safety_wit_60 : OSMutexDel_safety_wit_60.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_entail_wit_1 : OSMutexDel_entail_wit_1.
Proof.
  unfold OSMutexDel_entail_wit_1.
  intros perr_pre opt_pre pevent_pre X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_save_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask retval before )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> err_in)
|--
((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (mutex_del_continuation_source_save_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask retval before )
  **  ((pd) # UChar  |-> err_in)).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_entail_wit_4 : OSMutexDel_entail_wit_4.
Proof.

  unfold OSMutexDel_entail_wit_4.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13.
  intros h Hheap.
  exists prepared, prepared, current, mutex, (@nil Z), entry, current.
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) Hheap); first [assumption | reflexivity | congruence | lia].

Qed. 

Lemma proof_of_OSMutexDel_entail_wit_5 : OSMutexDel_entail_wit_5.
Proof.

  unfold OSMutexDel_entail_wit_5.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr prepared_3 state_2 event_2 mutex_3 cpu_sr_2 entry_3 current_3 tasks_waiting_2 after next done PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25.
  intros h Hheap.
  exists prepared_3, after, next, mutex_3, done, entry_3, current_3.
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) Hheap); first [assumption | reflexivity | congruence | lia].

Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_1 : OSMutexDel_partial_solve_wit_1.
Proof.
  unfold OSMutexDel_partial_solve_wit_1.
  intros perr_pre opt_pre pevent_pre X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_entry source_env external platform saved_local sg context mask before )
  **  ((perr_pre) # UChar  |-> err_in)
|--
(mutex_del_continuation_entry source_env external platform saved_local sg context mask before )
  **  ((perr_pre) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_2_pure : OSMutexDel_partial_solve_wit_2_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_2 : OSMutexDel_partial_solve_wit_2.
Proof.
  unfold OSMutexDel_partial_solve_wit_2, OSMutexDel_partial_solve_wit_2_aux.
  intros H_pure.
  intros perr_pre opt_pre pevent_pre X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10.
  intros h Hheap.
  assert (Hspatial :
(mutex_query_closed platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (mutex_del_continuation_entry_support source_env external platform saved_local sg context before )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((perr_pre) # UChar  |-> err_in)
|--
(mutex_query_closed platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mutex_del_continuation_entry_support source_env external platform saved_local sg context before )
  **  ((perr_pre) # UChar  |-> err_in)).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_3_pure : OSMutexDel_partial_solve_wit_3_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_3 : OSMutexDel_partial_solve_wit_3.
Proof.
  unfold OSMutexDel_partial_solve_wit_3, OSMutexDel_partial_solve_wit_3_aux.
  intros H_pure.
  intros perr_pre opt_pre pevent_pre X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14.
  intros h Hheap.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (mutex_del_continuation_entry_support source_env external platform saved_local sg context before )
  **  ((perr_pre) # UChar  |-> err_in)
|--
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (mutex_del_continuation_entry_support source_env external platform saved_local sg context before )
  **  ((perr_pre) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_4 : OSMutexDel_partial_solve_wit_4.
Proof.
  unfold OSMutexDel_partial_solve_wit_4.
  intros perr_pre opt_pre pevent_pre X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14.
  intros h Hheap.
  assert (Hspatial :
(mutex_query_closed platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (mutex_del_continuation_entry_support source_env external platform saved_local sg context before )
  **  ((perr_pre) # UChar  |-> err_in)
|--
(mutex_query_closed platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (mutex_del_continuation_entry_support source_env external platform saved_local sg context before )
  **  ((perr_pre) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_5_pure : OSMutexDel_partial_solve_wit_5_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_5 : OSMutexDel_partial_solve_wit_5.
Proof.
  unfold OSMutexDel_partial_solve_wit_5, OSMutexDel_partial_solve_wit_5_aux.
  intros H_pure.
  intros perr_pre opt_pre pevent_pre X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14.
  intros h Hheap.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (mutex_del_continuation_entry_support source_env external platform saved_local sg context before )
  **  ((perr_pre) # UChar  |-> err_in)
|--
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((before.(EventState) )) (eid)))
  **  (sem_query_type_frame sg before eid )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (mutex_del_continuation_entry_support source_env external platform saved_local sg context before )
  **  ((perr_pre) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_6_pure : OSMutexDel_partial_solve_wit_6_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_6 : OSMutexDel_partial_solve_wit_6.
Proof.
  unfold OSMutexDel_partial_solve_wit_6, OSMutexDel_partial_solve_wit_6_aux.
  intros H_pure.
  intros perr_pre opt_pre pevent_pre X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15.
  intros h Hheap.
  assert (Hspatial :
((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (mutex_del_continuation_entry_support source_env external platform saved_local sg context before )
  **  ((perr_pre) # UChar  |-> err_in)
|--
((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (mutex_del_continuation_entry_support source_env external platform saved_local sg context before )
  **  ((perr_pre) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_7 : OSMutexDel_partial_solve_wit_7.
Proof.
  unfold OSMutexDel_partial_solve_wit_7.
  intros perr_pre opt_pre pevent_pre X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15.
  intros h Hheap.
  assert (Hspatial :
(mutex_query_closed platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (mutex_del_continuation_entry_support source_env external platform saved_local sg context before )
  **  ((perr_pre) # UChar  |-> err_in)
|--
(mutex_query_closed platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (mutex_del_continuation_entry_support source_env external platform saved_local sg context before )
  **  ((perr_pre) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_8_pure : OSMutexDel_partial_solve_wit_8_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_8 : OSMutexDel_partial_solve_wit_8.
Proof.
  unfold OSMutexDel_partial_solve_wit_8, OSMutexDel_partial_solve_wit_8_aux.
  intros H_pure.
  intros perr_pre opt_pre pevent_pre X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15.
  intros h Hheap.
  assert (Hspatial :
((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (mutex_del_continuation_entry_support source_env external platform saved_local sg context before )
  **  ((perr_pre) # UChar  |-> err_in)
|--
((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (interrupt_inv_no_int_nesting sg (before.(IntrState) ) )
  **  (mutex_query_whole_frame sg before )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (mutex_del_continuation_entry_support source_env external platform saved_local sg context before )
  **  ((perr_pre) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_9 : OSMutexDel_partial_solve_wit_9.
Proof.
  unfold OSMutexDel_partial_solve_wit_9.
  intros perr_pre opt_pre pevent_pre X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16.
  intros h Hheap.
  assert (Hspatial :
(mutex_query_closed platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (mutex_del_continuation_entry_support source_env external platform saved_local sg context before )
  **  ((perr_pre) # UChar  |-> err_in)
|--
(mutex_query_closed platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (mutex_del_continuation_entry_support source_env external platform saved_local sg context before )
  **  ((perr_pre) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_10 : OSMutexDel_partial_solve_wit_10.
Proof.
  unfold OSMutexDel_partial_solve_wit_10.
  intros perr_pre opt_pre pevent_pre X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_entry source_env external platform saved_local sg context mask before )
  **  ((perr_pre) # UChar  |-> err_in)
|--
(mutex_del_continuation_entry source_env external platform saved_local sg context mask before )
  **  ((perr_pre) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_11_pure : OSMutexDel_partial_solve_wit_11_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_11 : OSMutexDel_partial_solve_wit_11.
Proof.
  unfold OSMutexDel_partial_solve_wit_11, OSMutexDel_partial_solve_wit_11_aux.
  intros H_pure.
  intros perr_pre opt_pre pevent_pre X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_entry source_env external platform saved_local sg context mask before )
  **  ((perr_pre) # UChar  |-> err_in)
|--
(mutex_del_continuation_entry source_env external platform saved_local sg context mask before )
  **  ((perr_pre) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_12 : OSMutexDel_partial_solve_wit_12.
Proof.
  unfold OSMutexDel_partial_solve_wit_12.
  intros perr_pre opt_pre pevent_pre X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_save_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask before )
  **  ((perr_pre) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_save_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask before )
  **  ((perr_pre) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_13 : OSMutexDel_partial_solve_wit_13.
Proof.
  unfold OSMutexDel_partial_solve_wit_13.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_save_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr before )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_save_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr before )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_14_pure : OSMutexDel_partial_solve_wit_14_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_14 : OSMutexDel_partial_solve_wit_14.
Proof.
  unfold OSMutexDel_partial_solve_wit_14, OSMutexDel_partial_solve_wit_14_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13.
  intros h Hheap.
  assert (Hspatial :
(critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (kernel_program_inv sg entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)
|--
(kernel_program_inv sg entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_15 : OSMutexDel_partial_solve_wit_15.
Proof.
  unfold OSMutexDel_partial_solve_wit_15, OSMutexDel_partial_solve_wit_15_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14.
  intros h Hheap.
  assert (Hkind : kind <> 4).
  { intro Heq; rewrite Heq in PreH1; vm_compute in PreH1; contradiction. }
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  (mutex_del_continuation_type_frame source_env external platform saved_local sg context eid entry kind )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  (mutex_del_continuation_type_frame source_env external platform saved_local sg context eid entry kind )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_16_pure : OSMutexDel_partial_solve_wit_16_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_16 : OSMutexDel_partial_solve_wit_16.
Proof.
  unfold OSMutexDel_partial_solve_wit_16, OSMutexDel_partial_solve_wit_16_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_17_pure : OSMutexDel_partial_solve_wit_17_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_17 : OSMutexDel_partial_solve_wit_17.
Proof.
  unfold OSMutexDel_partial_solve_wit_17, OSMutexDel_partial_solve_wit_17_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_18_pure : OSMutexDel_partial_solve_wit_18_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_18 : OSMutexDel_partial_solve_wit_18.
Proof.
  unfold OSMutexDel_partial_solve_wit_18, OSMutexDel_partial_solve_wit_18_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14.
  intros h Hheap.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  (mutex_del_continuation_type_frame source_env external platform saved_local sg context eid entry kind )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  (mutex_del_continuation_type_frame source_env external platform saved_local sg context eid entry kind )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_19_pure : OSMutexDel_partial_solve_wit_19_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_19 : OSMutexDel_partial_solve_wit_19.
Proof.
  unfold OSMutexDel_partial_solve_wit_19, OSMutexDel_partial_solve_wit_19_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_20 : OSMutexDel_partial_solve_wit_20.
Proof.
  unfold OSMutexDel_partial_solve_wit_20, OSMutexDel_partial_solve_wit_20_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17.
  intros h Hheap.
  pose proof (proj1 PreH3) as Hentry_inv.
  pose proof (proj1 (proj2 PreH3)) as Hentry_lookup.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> initial_group)
  **  (mutex_del_event_group_frame sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> initial_group)
  **  (mutex_del_event_group_frame sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_21 : OSMutexDel_partial_solve_wit_21.
Proof.
  unfold OSMutexDel_partial_solve_wit_21, OSMutexDel_partial_solve_wit_21_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17.
  intros h Hheap.
  pose proof (proj1 PreH3) as Hentry_inv.
  pose proof (proj1 (proj2 PreH3)) as Hentry_lookup.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> initial_group)
  **  (mutex_del_event_group_frame sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> initial_group)
  **  (mutex_del_event_group_frame sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_22 : OSMutexDel_partial_solve_wit_22.
Proof.
  unfold OSMutexDel_partial_solve_wit_22.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_23 : OSMutexDel_partial_solve_wit_23.
Proof.
  unfold OSMutexDel_partial_solve_wit_23.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_24_pure : OSMutexDel_partial_solve_wit_24_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_24 : OSMutexDel_partial_solve_wit_24.
Proof.
  unfold OSMutexDel_partial_solve_wit_24, OSMutexDel_partial_solve_wit_24_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_25_pure : OSMutexDel_partial_solve_wit_25_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_25 : OSMutexDel_partial_solve_wit_25.
Proof.
  unfold OSMutexDel_partial_solve_wit_25, OSMutexDel_partial_solve_wit_25_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_26 : OSMutexDel_partial_solve_wit_26.
Proof.
  unfold OSMutexDel_partial_solve_wit_26, OSMutexDel_partial_solve_wit_26_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind_2 acquired mutex initial_group kind pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20.
  intros h Hheap.
  pose proof (proj1 PreH5) as Hentry_inv.
  pose proof (proj1 (proj2 PreH5)) as Hentry_lookup.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_event_rest sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_event_rest sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_27 : OSMutexDel_partial_solve_wit_27.
Proof.
  unfold OSMutexDel_partial_solve_wit_27, OSMutexDel_partial_solve_wit_27_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind_2 acquired mutex initial_group kind pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20.
  intros h Hheap.
  pose proof (proj1 PreH5) as Hentry_inv.
  pose proof (proj1 (proj2 PreH5)) as Hentry_lookup.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_event_rest sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_event_rest sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_28 : OSMutexDel_partial_solve_wit_28.
Proof.
  unfold OSMutexDel_partial_solve_wit_28, OSMutexDel_partial_solve_wit_28_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20.
  intros h Hheap.
  assert (Hceiling : mutex_del_parent_ceiling_at sg eid entry
      (unsigned_last_nbits (Z.shiftr count 8) 8)).
  { exists acquired, mutex; split; [exact PreH5|].
    pose proof PreH2 as [_ [_ [Hcount _]]].
    rewrite Hcount; eapply mutex_del_parent_cast_count; exact PreH5. }
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_29 : OSMutexDel_partial_solve_wit_29.
Proof.
  unfold OSMutexDel_partial_solve_wit_29, OSMutexDel_partial_solve_wit_29_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20.
  intros h Hheap.
  assert (Hceiling : mutex_del_parent_ceiling_at sg eid entry
      (unsigned_last_nbits (Z.shiftr count 8) 8)).
  { exists acquired, mutex; split; [exact PreH5|].
    pose proof PreH2 as [_ [_ [Hcount _]]].
    rewrite Hcount; eapply mutex_del_parent_cast_count; exact PreH5. }
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_30_pure : OSMutexDel_partial_solve_wit_30_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_30 : OSMutexDel_partial_solve_wit_30.
Proof.
  unfold OSMutexDel_partial_solve_wit_30, OSMutexDel_partial_solve_wit_30_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((entry.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (UCOS2_raw_rep_missing_priority_table sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((entry.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (UCOS2_raw_rep_missing_priority_table sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_31_pure : OSMutexDel_partial_solve_wit_31_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_31 : OSMutexDel_partial_solve_wit_31.
Proof.
  unfold OSMutexDel_partial_solve_wit_31, OSMutexDel_partial_solve_wit_31_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((entry.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (UCOS2_raw_rep_missing_priority_table sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((entry.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (UCOS2_raw_rep_missing_priority_table sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_32 : OSMutexDel_partial_solve_wit_32.
Proof.
  unfold OSMutexDel_partial_solve_wit_32, OSMutexDel_partial_solve_wit_32_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24.
  intros h Hheap.
  assert (Howner_pointer : mutex_del_parent_owner_pointer sg eid entry
      (unsigned_last_nbits (Z.shiftr count 8) 8) pointer).
  { exists acquired, mutex; split; [exact PreH9|].
    pose proof PreH6 as [_ [Hpointer [Hcount _]]].
    split; [|exact Hpointer].
    unfold mutex_del_parent_ceiling.
    rewrite Hcount, (mutex_del_parent_cast_count sg eid entry acquired mutex PreH9).
    exact (proj2 (proj2 (mutex_del_parent_count_decode sg eid entry acquired mutex PreH9))). }
  assert (Hspatial :
(mutex_del_released_resources sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_released_resources sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_33 : OSMutexDel_partial_solve_wit_33.
Proof.
  unfold OSMutexDel_partial_solve_wit_33, OSMutexDel_partial_solve_wit_33_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24.
  intros h Hheap.
  assert (Howner_pointer : mutex_del_parent_owner_pointer sg eid entry
      (unsigned_last_nbits (Z.shiftr count 8) 8) pointer).
  { exists acquired, mutex; split; [exact PreH9|].
    pose proof PreH6 as [_ [Hpointer [Hcount _]]].
    split; [|exact Hpointer].
    unfold mutex_del_parent_ceiling.
    rewrite Hcount, (mutex_del_parent_cast_count sg eid entry acquired mutex PreH9).
    exact (proj2 (proj2 (mutex_del_parent_count_decode sg eid entry acquired mutex PreH9))). }
  assert (Hspatial :
(mutex_del_released_resources sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_released_resources sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_34 : OSMutexDel_partial_solve_wit_34.
Proof.
  unfold OSMutexDel_partial_solve_wit_34, OSMutexDel_partial_solve_wit_34_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26.
  intros h Hheap.
  pose proof (proj1 PreH11) as Hentry_inv.
  pose proof (proj1 (proj2 PreH11)) as Hentry_lookup.
  assert (Hspatial :
(mutex_del_priority_input sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) owner node )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_priority_input sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) owner node )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_35 : OSMutexDel_partial_solve_wit_35.
Proof.
  unfold OSMutexDel_partial_solve_wit_35, OSMutexDel_partial_solve_wit_35_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26.
  intros h Hheap.
  pose proof (proj1 PreH11) as Hentry_inv.
  pose proof (proj1 (proj2 PreH11)) as Hentry_lookup.
  assert (Hspatial :
(mutex_del_priority_input sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) owner node )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_priority_input sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) owner node )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_36 : OSMutexDel_partial_solve_wit_36.
Proof.
  unfold OSMutexDel_partial_solve_wit_36.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_scan_pre pointer (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (curPrio (node)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_scan_pre pointer (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (curPrio (node)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_37 : OSMutexDel_partial_solve_wit_37.
Proof.
  unfold OSMutexDel_partial_solve_wit_37.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_scan_pre pointer (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (curPrio (node)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_scan_pre pointer (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (curPrio (node)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_38 : OSMutexDel_partial_solve_wit_38.
Proof.
  unfold OSMutexDel_partial_solve_wit_38.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_39 : OSMutexDel_partial_solve_wit_39.
Proof.
  unfold OSMutexDel_partial_solve_wit_39.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_40 : OSMutexDel_partial_solve_wit_40.
Proof.
  unfold OSMutexDel_partial_solve_wit_40.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without pointer TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without pointer TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_41 : OSMutexDel_partial_solve_wit_41.
Proof.
  unfold OSMutexDel_partial_solve_wit_41.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without pointer TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without pointer TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_42_pure : OSMutexDel_partial_solve_wit_42_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_42 : OSMutexDel_partial_solve_wit_42.
Proof.
  unfold OSMutexDel_partial_solve_wit_42, OSMutexDel_partial_solve_wit_42_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_43_pure : OSMutexDel_partial_solve_wit_43_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_43 : OSMutexDel_partial_solve_wit_43.
Proof.
  unfold OSMutexDel_partial_solve_wit_43, OSMutexDel_partial_solve_wit_43_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_44 : OSMutexDel_partial_solve_wit_44.
Proof.
  unfold OSMutexDel_partial_solve_wit_44.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_rdy_pre pointer retval (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) (curPrio (node)) (tcb_x_of_prio ((curPrio (node)))) (tcb_y_of_prio ((curPrio (node)))) (tcb_bit_x_of_prio ((curPrio (node)))) (tcb_bit_y_of_prio ((curPrio (node)))) (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))) (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))) )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_rdy_pre pointer retval (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) (curPrio (node)) (tcb_x_of_prio ((curPrio (node)))) (tcb_y_of_prio ((curPrio (node)))) (tcb_bit_x_of_prio ((curPrio (node)))) (tcb_bit_y_of_prio ((curPrio (node)))) (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))) (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))) )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_45 : OSMutexDel_partial_solve_wit_45.
Proof.
  unfold OSMutexDel_partial_solve_wit_45.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_rdy_pre pointer retval (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) (curPrio (node)) (tcb_x_of_prio ((curPrio (node)))) (tcb_y_of_prio ((curPrio (node)))) (tcb_bit_x_of_prio ((curPrio (node)))) (tcb_bit_y_of_prio ((curPrio (node)))) (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))) (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))) )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_rdy_pre pointer retval (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) (curPrio (node)) (tcb_x_of_prio ((curPrio (node)))) (tcb_y_of_prio ((curPrio (node)))) (tcb_bit_x_of_prio ((curPrio (node)))) (tcb_bit_y_of_prio ((curPrio (node)))) (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))) (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))) )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_46_pure : OSMutexDel_partial_solve_wit_46_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_46 : OSMutexDel_partial_solve_wit_46.
Proof.
  unfold OSMutexDel_partial_solve_wit_46, OSMutexDel_partial_solve_wit_46_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_parent_prepared sg eid entry prepared current mutex )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_parent_prepared sg eid entry prepared current mutex )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_47 : OSMutexDel_partial_solve_wit_47.
Proof.
  unfold OSMutexDel_partial_solve_wit_47, OSMutexDel_partial_solve_wit_47_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr kind pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18.
  intros h Hheap.
  pose proof (proj2 (proj2 (proj2 PreH4))) as Hrecycle_values.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> free)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pe)
  **  (mutex_del_parent_recycle_rest sg eid entry prepared current mutex )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> free)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pe)
  **  (mutex_del_parent_recycle_rest sg eid entry prepared current mutex )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_48_pure : OSMutexDel_partial_solve_wit_48_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_48 : OSMutexDel_partial_solve_wit_48.
Proof.
  unfold OSMutexDel_partial_solve_wit_48, OSMutexDel_partial_solve_wit_48_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr kind pointer count group free checkpoint PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry checkpoint )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry checkpoint )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_49_pure : OSMutexDel_partial_solve_wit_49_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_49 : OSMutexDel_partial_solve_wit_49.
Proof.
  unfold OSMutexDel_partial_solve_wit_49, OSMutexDel_partial_solve_wit_49_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr kind pointer count group free checkpoint PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry checkpoint )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry checkpoint )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_50 : OSMutexDel_partial_solve_wit_50.
Proof.
  unfold OSMutexDel_partial_solve_wit_50.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr kind pointer count group free checkpoint PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask checkpoint )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask checkpoint )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_51 : OSMutexDel_partial_solve_wit_51.
Proof.
  unfold OSMutexDel_partial_solve_wit_51, OSMutexDel_partial_solve_wit_51_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18.
  intros h Hheap.
  assert (Hwaiting : mutex_del_parent_waiting sg eid entry).
  { exists acquired, mutex; split; [exact PreH3|].
    intro Hz; rewrite PreH2, Hz in PreH1; vm_compute in PreH1; contradiction. }
  assert (Hspatial :
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_52 : OSMutexDel_partial_solve_wit_52.
Proof.
  unfold OSMutexDel_partial_solve_wit_52, OSMutexDel_partial_solve_wit_52_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18.
  intros h Hheap.
  assert (Hwaiting : mutex_del_parent_waiting sg eid entry).
  { exists acquired, mutex; split; [exact PreH3|].
    intro Hz; rewrite PreH2, Hz in PreH1; vm_compute in PreH1; contradiction. }
  assert (Hspatial :
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_53_pure : OSMutexDel_partial_solve_wit_53_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_53 : OSMutexDel_partial_solve_wit_53.
Proof.
  unfold OSMutexDel_partial_solve_wit_53, OSMutexDel_partial_solve_wit_53_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_54_pure : OSMutexDel_partial_solve_wit_54_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_54 : OSMutexDel_partial_solve_wit_54.
Proof.
  unfold OSMutexDel_partial_solve_wit_54, OSMutexDel_partial_solve_wit_54_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_55_pure : OSMutexDel_partial_solve_wit_55_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_55 : OSMutexDel_partial_solve_wit_55.
Proof.
  unfold OSMutexDel_partial_solve_wit_55, OSMutexDel_partial_solve_wit_55_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_56_pure : OSMutexDel_partial_solve_wit_56_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_56 : OSMutexDel_partial_solve_wit_56.
Proof.
  unfold OSMutexDel_partial_solve_wit_56, OSMutexDel_partial_solve_wit_56_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_57 : OSMutexDel_partial_solve_wit_57.
Proof.
  unfold OSMutexDel_partial_solve_wit_57.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_58 : OSMutexDel_partial_solve_wit_58.
Proof.
  unfold OSMutexDel_partial_solve_wit_58.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_59 : OSMutexDel_partial_solve_wit_59.
Proof.
  unfold OSMutexDel_partial_solve_wit_59.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_60 : OSMutexDel_partial_solve_wit_60.
Proof.
  unfold OSMutexDel_partial_solve_wit_60.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_61 : OSMutexDel_partial_solve_wit_61.
Proof.
  unfold OSMutexDel_partial_solve_wit_61.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_62 : OSMutexDel_partial_solve_wit_62.
Proof.
  unfold OSMutexDel_partial_solve_wit_62.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_63 : OSMutexDel_partial_solve_wit_63.
Proof.
  unfold OSMutexDel_partial_solve_wit_63.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_64 : OSMutexDel_partial_solve_wit_64.
Proof.
  unfold OSMutexDel_partial_solve_wit_64.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_65 : OSMutexDel_partial_solve_wit_65.
Proof.
  unfold OSMutexDel_partial_solve_wit_65.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_66 : OSMutexDel_partial_solve_wit_66.
Proof.
  unfold OSMutexDel_partial_solve_wit_66.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_67_pure : OSMutexDel_partial_solve_wit_67_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_67 : OSMutexDel_partial_solve_wit_67.
Proof.
  unfold OSMutexDel_partial_solve_wit_67, OSMutexDel_partial_solve_wit_67_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_68_pure : OSMutexDel_partial_solve_wit_68_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_68 : OSMutexDel_partial_solve_wit_68.
Proof.
  unfold OSMutexDel_partial_solve_wit_68, OSMutexDel_partial_solve_wit_68_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_69_pure : OSMutexDel_partial_solve_wit_69_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_69 : OSMutexDel_partial_solve_wit_69.
Proof.
  unfold OSMutexDel_partial_solve_wit_69, OSMutexDel_partial_solve_wit_69_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_70_pure : OSMutexDel_partial_solve_wit_70_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_70 : OSMutexDel_partial_solve_wit_70.
Proof.
  unfold OSMutexDel_partial_solve_wit_70, OSMutexDel_partial_solve_wit_70_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_71_pure : OSMutexDel_partial_solve_wit_71_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_71 : OSMutexDel_partial_solve_wit_71.
Proof.
  unfold OSMutexDel_partial_solve_wit_71, OSMutexDel_partial_solve_wit_71_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_72_pure : OSMutexDel_partial_solve_wit_72_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_72 : OSMutexDel_partial_solve_wit_72.
Proof.
  unfold OSMutexDel_partial_solve_wit_72, OSMutexDel_partial_solve_wit_72_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_73_pure : OSMutexDel_partial_solve_wit_73_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_73 : OSMutexDel_partial_solve_wit_73.
Proof.
  unfold OSMutexDel_partial_solve_wit_73, OSMutexDel_partial_solve_wit_73_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_74_pure : OSMutexDel_partial_solve_wit_74_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_74 : OSMutexDel_partial_solve_wit_74.
Proof.
  unfold OSMutexDel_partial_solve_wit_74, OSMutexDel_partial_solve_wit_74_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_75 : OSMutexDel_partial_solve_wit_75.
Proof.
  unfold OSMutexDel_partial_solve_wit_75, OSMutexDel_partial_solve_wit_75_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind_2 acquired mutex initial_group kind pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  pose proof (proj1 PreH5) as Hentry_inv.
  pose proof (proj1 (proj2 PreH5)) as Hentry_lookup.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_event_rest sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_event_rest sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_76 : OSMutexDel_partial_solve_wit_76.
Proof.
  unfold OSMutexDel_partial_solve_wit_76, OSMutexDel_partial_solve_wit_76_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind_2 acquired mutex initial_group kind pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  pose proof (proj1 PreH5) as Hentry_inv.
  pose proof (proj1 (proj2 PreH5)) as Hentry_lookup.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_event_rest sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_event_rest sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_77 : OSMutexDel_partial_solve_wit_77.
Proof.
  unfold OSMutexDel_partial_solve_wit_77, OSMutexDel_partial_solve_wit_77_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind_2 acquired mutex initial_group kind pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  pose proof (proj1 PreH5) as Hentry_inv.
  pose proof (proj1 (proj2 PreH5)) as Hentry_lookup.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_event_rest sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_event_rest sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_78 : OSMutexDel_partial_solve_wit_78.
Proof.
  unfold OSMutexDel_partial_solve_wit_78, OSMutexDel_partial_solve_wit_78_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind_2 acquired mutex initial_group kind pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  pose proof (proj1 PreH5) as Hentry_inv.
  pose proof (proj1 (proj2 PreH5)) as Hentry_lookup.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_event_rest sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_event_rest sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_79 : OSMutexDel_partial_solve_wit_79.
Proof.
  unfold OSMutexDel_partial_solve_wit_79, OSMutexDel_partial_solve_wit_79_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind_2 acquired mutex initial_group kind pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  pose proof (proj1 PreH5) as Hentry_inv.
  pose proof (proj1 (proj2 PreH5)) as Hentry_lookup.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_event_rest sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_event_rest sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_80 : OSMutexDel_partial_solve_wit_80.
Proof.
  unfold OSMutexDel_partial_solve_wit_80, OSMutexDel_partial_solve_wit_80_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind_2 acquired mutex initial_group kind pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  pose proof (proj1 PreH5) as Hentry_inv.
  pose proof (proj1 (proj2 PreH5)) as Hentry_lookup.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_event_rest sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_event_rest sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_81 : OSMutexDel_partial_solve_wit_81.
Proof.
  unfold OSMutexDel_partial_solve_wit_81, OSMutexDel_partial_solve_wit_81_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind_2 acquired mutex initial_group kind pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  pose proof (proj1 PreH5) as Hentry_inv.
  pose proof (proj1 (proj2 PreH5)) as Hentry_lookup.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_event_rest sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_event_rest sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_82 : OSMutexDel_partial_solve_wit_82.
Proof.
  unfold OSMutexDel_partial_solve_wit_82, OSMutexDel_partial_solve_wit_82_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind_2 acquired mutex initial_group kind pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  pose proof (proj1 PreH5) as Hentry_inv.
  pose proof (proj1 (proj2 PreH5)) as Hentry_lookup.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_event_rest sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_event_rest sg entry eid acquired )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_83 : OSMutexDel_partial_solve_wit_83.
Proof.
  unfold OSMutexDel_partial_solve_wit_83, OSMutexDel_partial_solve_wit_83_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hceiling : mutex_del_parent_ceiling_at sg eid entry
      (unsigned_last_nbits (Z.shiftr count 8) 8)).
  { exists acquired, mutex; split; [exact PreH5|].
    pose proof PreH2 as [_ [_ [Hcount _]]].
    rewrite Hcount; eapply mutex_del_parent_cast_count; exact PreH5. }
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_84 : OSMutexDel_partial_solve_wit_84.
Proof.
  unfold OSMutexDel_partial_solve_wit_84, OSMutexDel_partial_solve_wit_84_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hceiling : mutex_del_parent_ceiling_at sg eid entry
      (unsigned_last_nbits (Z.shiftr count 8) 8)).
  { exists acquired, mutex; split; [exact PreH5|].
    pose proof PreH2 as [_ [_ [Hcount _]]].
    rewrite Hcount; eapply mutex_del_parent_cast_count; exact PreH5. }
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_85 : OSMutexDel_partial_solve_wit_85.
Proof.
  unfold OSMutexDel_partial_solve_wit_85, OSMutexDel_partial_solve_wit_85_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hceiling : mutex_del_parent_ceiling_at sg eid entry
      (unsigned_last_nbits (Z.shiftr count 8) 8)).
  { exists acquired, mutex; split; [exact PreH5|].
    pose proof PreH2 as [_ [_ [Hcount _]]].
    rewrite Hcount; eapply mutex_del_parent_cast_count; exact PreH5. }
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_86 : OSMutexDel_partial_solve_wit_86.
Proof.
  unfold OSMutexDel_partial_solve_wit_86, OSMutexDel_partial_solve_wit_86_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hceiling : mutex_del_parent_ceiling_at sg eid entry
      (unsigned_last_nbits (Z.shiftr count 8) 8)).
  { exists acquired, mutex; split; [exact PreH5|].
    pose proof PreH2 as [_ [_ [Hcount _]]].
    rewrite Hcount; eapply mutex_del_parent_cast_count; exact PreH5. }
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_87 : OSMutexDel_partial_solve_wit_87.
Proof.
  unfold OSMutexDel_partial_solve_wit_87, OSMutexDel_partial_solve_wit_87_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hceiling : mutex_del_parent_ceiling_at sg eid entry
      (unsigned_last_nbits (Z.shiftr count 8) 8)).
  { exists acquired, mutex; split; [exact PreH5|].
    pose proof PreH2 as [_ [_ [Hcount _]]].
    rewrite Hcount; eapply mutex_del_parent_cast_count; exact PreH5. }
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_88 : OSMutexDel_partial_solve_wit_88.
Proof.
  unfold OSMutexDel_partial_solve_wit_88, OSMutexDel_partial_solve_wit_88_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hceiling : mutex_del_parent_ceiling_at sg eid entry
      (unsigned_last_nbits (Z.shiftr count 8) 8)).
  { exists acquired, mutex; split; [exact PreH5|].
    pose proof PreH2 as [_ [_ [Hcount _]]].
    rewrite Hcount; eapply mutex_del_parent_cast_count; exact PreH5. }
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_89 : OSMutexDel_partial_solve_wit_89.
Proof.
  unfold OSMutexDel_partial_solve_wit_89, OSMutexDel_partial_solve_wit_89_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hceiling : mutex_del_parent_ceiling_at sg eid entry
      (unsigned_last_nbits (Z.shiftr count 8) 8)).
  { exists acquired, mutex; split; [exact PreH5|].
    pose proof PreH2 as [_ [_ [Hcount _]]].
    rewrite Hcount; eapply mutex_del_parent_cast_count; exact PreH5. }
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_90 : OSMutexDel_partial_solve_wit_90.
Proof.
  unfold OSMutexDel_partial_solve_wit_90, OSMutexDel_partial_solve_wit_90_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hceiling : mutex_del_parent_ceiling_at sg eid entry
      (unsigned_last_nbits (Z.shiftr count 8) 8)).
  { exists acquired, mutex; split; [exact PreH5|].
    pose proof PreH2 as [_ [_ [Hcount _]]].
    rewrite Hcount; eapply mutex_del_parent_cast_count; exact PreH5. }
  assert (Hspatial :
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_raw_rep sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_91_pure : OSMutexDel_partial_solve_wit_91_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_91 : OSMutexDel_partial_solve_wit_91.
Proof.
  unfold OSMutexDel_partial_solve_wit_91, OSMutexDel_partial_solve_wit_91_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24.
  intros h Hheap.
  assert (Hspatial :
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((entry.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (UCOS2_raw_rep_missing_priority_table sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((entry.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (UCOS2_raw_rep_missing_priority_table sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_92_pure : OSMutexDel_partial_solve_wit_92_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_92 : OSMutexDel_partial_solve_wit_92.
Proof.
  unfold OSMutexDel_partial_solve_wit_92, OSMutexDel_partial_solve_wit_92_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24.
  intros h Hheap.
  assert (Hspatial :
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((entry.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (UCOS2_raw_rep_missing_priority_table sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((entry.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (UCOS2_raw_rep_missing_priority_table sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_93_pure : OSMutexDel_partial_solve_wit_93_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_93 : OSMutexDel_partial_solve_wit_93.
Proof.
  unfold OSMutexDel_partial_solve_wit_93, OSMutexDel_partial_solve_wit_93_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24.
  intros h Hheap.
  assert (Hspatial :
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((entry.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (UCOS2_raw_rep_missing_priority_table sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((entry.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (UCOS2_raw_rep_missing_priority_table sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_94_pure : OSMutexDel_partial_solve_wit_94_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_94 : OSMutexDel_partial_solve_wit_94.
Proof.
  unfold OSMutexDel_partial_solve_wit_94, OSMutexDel_partial_solve_wit_94_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24.
  intros h Hheap.
  assert (Hspatial :
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((entry.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (UCOS2_raw_rep_missing_priority_table sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((entry.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (UCOS2_raw_rep_missing_priority_table sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_95_pure : OSMutexDel_partial_solve_wit_95_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_95 : OSMutexDel_partial_solve_wit_95.
Proof.
  unfold OSMutexDel_partial_solve_wit_95, OSMutexDel_partial_solve_wit_95_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24.
  intros h Hheap.
  assert (Hspatial :
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((entry.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (UCOS2_raw_rep_missing_priority_table sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((entry.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (UCOS2_raw_rep_missing_priority_table sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_96_pure : OSMutexDel_partial_solve_wit_96_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_96 : OSMutexDel_partial_solve_wit_96.
Proof.
  unfold OSMutexDel_partial_solve_wit_96, OSMutexDel_partial_solve_wit_96_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24.
  intros h Hheap.
  assert (Hspatial :
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((entry.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (UCOS2_raw_rep_missing_priority_table sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((entry.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (UCOS2_raw_rep_missing_priority_table sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_97_pure : OSMutexDel_partial_solve_wit_97_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_97 : OSMutexDel_partial_solve_wit_97.
Proof.
  unfold OSMutexDel_partial_solve_wit_97, OSMutexDel_partial_solve_wit_97_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24.
  intros h Hheap.
  assert (Hspatial :
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((entry.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (UCOS2_raw_rep_missing_priority_table sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((entry.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (UCOS2_raw_rep_missing_priority_table sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_98_pure : OSMutexDel_partial_solve_wit_98_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_98 : OSMutexDel_partial_solve_wit_98.
Proof.
  unfold OSMutexDel_partial_solve_wit_98, OSMutexDel_partial_solve_wit_98_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24.
  intros h Hheap.
  assert (Hspatial :
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((entry.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (UCOS2_raw_rep_missing_priority_table sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((entry.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (UCOS2_raw_rep_missing_priority_table sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_99 : OSMutexDel_partial_solve_wit_99.
Proof.
  unfold OSMutexDel_partial_solve_wit_99, OSMutexDel_partial_solve_wit_99_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25.
  intros h Hheap.
  assert (Howner_pointer : mutex_del_parent_owner_pointer sg eid entry
      (unsigned_last_nbits (Z.shiftr count 8) 8) pointer).
  { exists acquired, mutex; split; [exact PreH9|].
    pose proof PreH6 as [_ [Hpointer [Hcount _]]].
    split; [|exact Hpointer].
    unfold mutex_del_parent_ceiling.
    rewrite Hcount, (mutex_del_parent_cast_count sg eid entry acquired mutex PreH9).
    exact (proj2 (proj2 (mutex_del_parent_count_decode sg eid entry acquired mutex PreH9))). }
  assert (Hspatial :
(mutex_del_released_resources sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_released_resources sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_100 : OSMutexDel_partial_solve_wit_100.
Proof.
  unfold OSMutexDel_partial_solve_wit_100, OSMutexDel_partial_solve_wit_100_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25.
  intros h Hheap.
  assert (Howner_pointer : mutex_del_parent_owner_pointer sg eid entry
      (unsigned_last_nbits (Z.shiftr count 8) 8) pointer).
  { exists acquired, mutex; split; [exact PreH9|].
    pose proof PreH6 as [_ [Hpointer [Hcount _]]].
    split; [|exact Hpointer].
    unfold mutex_del_parent_ceiling.
    rewrite Hcount, (mutex_del_parent_cast_count sg eid entry acquired mutex PreH9).
    exact (proj2 (proj2 (mutex_del_parent_count_decode sg eid entry acquired mutex PreH9))). }
  assert (Hspatial :
(mutex_del_released_resources sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_released_resources sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_101 : OSMutexDel_partial_solve_wit_101.
Proof.
  unfold OSMutexDel_partial_solve_wit_101, OSMutexDel_partial_solve_wit_101_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25.
  intros h Hheap.
  assert (Howner_pointer : mutex_del_parent_owner_pointer sg eid entry
      (unsigned_last_nbits (Z.shiftr count 8) 8) pointer).
  { exists acquired, mutex; split; [exact PreH9|].
    pose proof PreH6 as [_ [Hpointer [Hcount _]]].
    split; [|exact Hpointer].
    unfold mutex_del_parent_ceiling.
    rewrite Hcount, (mutex_del_parent_cast_count sg eid entry acquired mutex PreH9).
    exact (proj2 (proj2 (mutex_del_parent_count_decode sg eid entry acquired mutex PreH9))). }
  assert (Hspatial :
(mutex_del_released_resources sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_released_resources sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_102 : OSMutexDel_partial_solve_wit_102.
Proof.
  unfold OSMutexDel_partial_solve_wit_102, OSMutexDel_partial_solve_wit_102_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25.
  intros h Hheap.
  assert (Howner_pointer : mutex_del_parent_owner_pointer sg eid entry
      (unsigned_last_nbits (Z.shiftr count 8) 8) pointer).
  { exists acquired, mutex; split; [exact PreH9|].
    pose proof PreH6 as [_ [Hpointer [Hcount _]]].
    split; [|exact Hpointer].
    unfold mutex_del_parent_ceiling.
    rewrite Hcount, (mutex_del_parent_cast_count sg eid entry acquired mutex PreH9).
    exact (proj2 (proj2 (mutex_del_parent_count_decode sg eid entry acquired mutex PreH9))). }
  assert (Hspatial :
(mutex_del_released_resources sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_released_resources sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_103 : OSMutexDel_partial_solve_wit_103.
Proof.
  unfold OSMutexDel_partial_solve_wit_103, OSMutexDel_partial_solve_wit_103_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25.
  intros h Hheap.
  assert (Howner_pointer : mutex_del_parent_owner_pointer sg eid entry
      (unsigned_last_nbits (Z.shiftr count 8) 8) pointer).
  { exists acquired, mutex; split; [exact PreH9|].
    pose proof PreH6 as [_ [Hpointer [Hcount _]]].
    split; [|exact Hpointer].
    unfold mutex_del_parent_ceiling.
    rewrite Hcount, (mutex_del_parent_cast_count sg eid entry acquired mutex PreH9).
    exact (proj2 (proj2 (mutex_del_parent_count_decode sg eid entry acquired mutex PreH9))). }
  assert (Hspatial :
(mutex_del_released_resources sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_released_resources sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_104 : OSMutexDel_partial_solve_wit_104.
Proof.
  unfold OSMutexDel_partial_solve_wit_104, OSMutexDel_partial_solve_wit_104_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25.
  intros h Hheap.
  assert (Howner_pointer : mutex_del_parent_owner_pointer sg eid entry
      (unsigned_last_nbits (Z.shiftr count 8) 8) pointer).
  { exists acquired, mutex; split; [exact PreH9|].
    pose proof PreH6 as [_ [Hpointer [Hcount _]]].
    split; [|exact Hpointer].
    unfold mutex_del_parent_ceiling.
    rewrite Hcount, (mutex_del_parent_cast_count sg eid entry acquired mutex PreH9).
    exact (proj2 (proj2 (mutex_del_parent_count_decode sg eid entry acquired mutex PreH9))). }
  assert (Hspatial :
(mutex_del_released_resources sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_released_resources sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_105 : OSMutexDel_partial_solve_wit_105.
Proof.
  unfold OSMutexDel_partial_solve_wit_105, OSMutexDel_partial_solve_wit_105_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25.
  intros h Hheap.
  assert (Howner_pointer : mutex_del_parent_owner_pointer sg eid entry
      (unsigned_last_nbits (Z.shiftr count 8) 8) pointer).
  { exists acquired, mutex; split; [exact PreH9|].
    pose proof PreH6 as [_ [Hpointer [Hcount _]]].
    split; [|exact Hpointer].
    unfold mutex_del_parent_ceiling.
    rewrite Hcount, (mutex_del_parent_cast_count sg eid entry acquired mutex PreH9).
    exact (proj2 (proj2 (mutex_del_parent_count_decode sg eid entry acquired mutex PreH9))). }
  assert (Hspatial :
(mutex_del_released_resources sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_released_resources sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_106 : OSMutexDel_partial_solve_wit_106.
Proof.
  unfold OSMutexDel_partial_solve_wit_106, OSMutexDel_partial_solve_wit_106_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25.
  intros h Hheap.
  assert (Howner_pointer : mutex_del_parent_owner_pointer sg eid entry
      (unsigned_last_nbits (Z.shiftr count 8) 8) pointer).
  { exists acquired, mutex; split; [exact PreH9|].
    pose proof PreH6 as [_ [Hpointer [Hcount _]]].
    split; [|exact Hpointer].
    unfold mutex_del_parent_ceiling.
    rewrite Hcount, (mutex_del_parent_cast_count sg eid entry acquired mutex PreH9).
    exact (proj2 (proj2 (mutex_del_parent_count_decode sg eid entry acquired mutex PreH9))). }
  assert (Hspatial :
(mutex_del_released_resources sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_released_resources sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_107 : OSMutexDel_partial_solve_wit_107.
Proof.
  unfold OSMutexDel_partial_solve_wit_107, OSMutexDel_partial_solve_wit_107_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27.
  intros h Hheap.
  pose proof (proj1 PreH11) as Hentry_inv.
  pose proof (proj1 (proj2 PreH11)) as Hentry_lookup.
  assert (Hspatial :
(mutex_del_priority_input sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) owner node )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_priority_input sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) owner node )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_108 : OSMutexDel_partial_solve_wit_108.
Proof.
  unfold OSMutexDel_partial_solve_wit_108, OSMutexDel_partial_solve_wit_108_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27.
  intros h Hheap.
  pose proof (proj1 PreH11) as Hentry_inv.
  pose proof (proj1 (proj2 PreH11)) as Hentry_lookup.
  assert (Hspatial :
(mutex_del_priority_input sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) owner node )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_priority_input sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) owner node )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_109 : OSMutexDel_partial_solve_wit_109.
Proof.
  unfold OSMutexDel_partial_solve_wit_109, OSMutexDel_partial_solve_wit_109_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27.
  intros h Hheap.
  pose proof (proj1 PreH11) as Hentry_inv.
  pose proof (proj1 (proj2 PreH11)) as Hentry_lookup.
  assert (Hspatial :
(mutex_del_priority_input sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) owner node )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_priority_input sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) owner node )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_110 : OSMutexDel_partial_solve_wit_110.
Proof.
  unfold OSMutexDel_partial_solve_wit_110, OSMutexDel_partial_solve_wit_110_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27.
  intros h Hheap.
  pose proof (proj1 PreH11) as Hentry_inv.
  pose proof (proj1 (proj2 PreH11)) as Hentry_lookup.
  assert (Hspatial :
(mutex_del_priority_input sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) owner node )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_priority_input sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) owner node )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_111 : OSMutexDel_partial_solve_wit_111.
Proof.
  unfold OSMutexDel_partial_solve_wit_111, OSMutexDel_partial_solve_wit_111_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27.
  intros h Hheap.
  pose proof (proj1 PreH11) as Hentry_inv.
  pose proof (proj1 (proj2 PreH11)) as Hentry_lookup.
  assert (Hspatial :
(mutex_del_priority_input sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) owner node )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_priority_input sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) owner node )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_112 : OSMutexDel_partial_solve_wit_112.
Proof.
  unfold OSMutexDel_partial_solve_wit_112, OSMutexDel_partial_solve_wit_112_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27.
  intros h Hheap.
  pose proof (proj1 PreH11) as Hentry_inv.
  pose proof (proj1 (proj2 PreH11)) as Hentry_lookup.
  assert (Hspatial :
(mutex_del_priority_input sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) owner node )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_priority_input sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) owner node )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_113 : OSMutexDel_partial_solve_wit_113.
Proof.
  unfold OSMutexDel_partial_solve_wit_113, OSMutexDel_partial_solve_wit_113_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27.
  intros h Hheap.
  pose proof (proj1 PreH11) as Hentry_inv.
  pose proof (proj1 (proj2 PreH11)) as Hentry_lookup.
  assert (Hspatial :
(mutex_del_priority_input sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) owner node )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_priority_input sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) owner node )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_114 : OSMutexDel_partial_solve_wit_114.
Proof.
  unfold OSMutexDel_partial_solve_wit_114, OSMutexDel_partial_solve_wit_114_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27.
  intros h Hheap.
  pose proof (proj1 PreH11) as Hentry_inv.
  pose proof (proj1 (proj2 PreH11)) as Hentry_lookup.
  assert (Hspatial :
(mutex_del_priority_input sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) owner node )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_priority_input sg entry (unsigned_last_nbits ((Z.shiftr count 8)) (8)) owner node )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_115 : OSMutexDel_partial_solve_wit_115.
Proof.
  unfold OSMutexDel_partial_solve_wit_115.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_scan_pre pointer (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (curPrio (node)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_scan_pre pointer (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (curPrio (node)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_116 : OSMutexDel_partial_solve_wit_116.
Proof.
  unfold OSMutexDel_partial_solve_wit_116.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_scan_pre pointer (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (curPrio (node)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_scan_pre pointer (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (curPrio (node)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_117 : OSMutexDel_partial_solve_wit_117.
Proof.
  unfold OSMutexDel_partial_solve_wit_117.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_scan_pre pointer (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (curPrio (node)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_scan_pre pointer (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (curPrio (node)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_118 : OSMutexDel_partial_solve_wit_118.
Proof.
  unfold OSMutexDel_partial_solve_wit_118.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_scan_pre pointer (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (curPrio (node)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_scan_pre pointer (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (curPrio (node)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_119 : OSMutexDel_partial_solve_wit_119.
Proof.
  unfold OSMutexDel_partial_solve_wit_119.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_scan_pre pointer (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (curPrio (node)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_scan_pre pointer (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (curPrio (node)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_120 : OSMutexDel_partial_solve_wit_120.
Proof.
  unfold OSMutexDel_partial_solve_wit_120.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_scan_pre pointer (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (curPrio (node)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_scan_pre pointer (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (curPrio (node)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_121 : OSMutexDel_partial_solve_wit_121.
Proof.
  unfold OSMutexDel_partial_solve_wit_121.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_scan_pre pointer (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (curPrio (node)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_scan_pre pointer (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (curPrio (node)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_122 : OSMutexDel_partial_solve_wit_122.
Proof.
  unfold OSMutexDel_partial_solve_wit_122.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_scan_pre pointer (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (curPrio (node)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_scan_pre pointer (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (curPrio (node)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_123 : OSMutexDel_partial_solve_wit_123.
Proof.
  unfold OSMutexDel_partial_solve_wit_123.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_124 : OSMutexDel_partial_solve_wit_124.
Proof.
  unfold OSMutexDel_partial_solve_wit_124.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_125 : OSMutexDel_partial_solve_wit_125.
Proof.
  unfold OSMutexDel_partial_solve_wit_125.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_126 : OSMutexDel_partial_solve_wit_126.
Proof.
  unfold OSMutexDel_partial_solve_wit_126.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_127 : OSMutexDel_partial_solve_wit_127.
Proof.
  unfold OSMutexDel_partial_solve_wit_127.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_128 : OSMutexDel_partial_solve_wit_128.
Proof.
  unfold OSMutexDel_partial_solve_wit_128.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_129 : OSMutexDel_partial_solve_wit_129.
Proof.
  unfold OSMutexDel_partial_solve_wit_129.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_130 : OSMutexDel_partial_solve_wit_130.
Proof.
  unfold OSMutexDel_partial_solve_wit_130.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_131 : OSMutexDel_partial_solve_wit_131.
Proof.
  unfold OSMutexDel_partial_solve_wit_131.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without pointer TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without pointer TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_132 : OSMutexDel_partial_solve_wit_132.
Proof.
  unfold OSMutexDel_partial_solve_wit_132.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without pointer TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without pointer TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_133 : OSMutexDel_partial_solve_wit_133.
Proof.
  unfold OSMutexDel_partial_solve_wit_133.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without pointer TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without pointer TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_134 : OSMutexDel_partial_solve_wit_134.
Proof.
  unfold OSMutexDel_partial_solve_wit_134.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without pointer TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without pointer TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_135 : OSMutexDel_partial_solve_wit_135.
Proof.
  unfold OSMutexDel_partial_solve_wit_135.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without pointer TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without pointer TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_136 : OSMutexDel_partial_solve_wit_136.
Proof.
  unfold OSMutexDel_partial_solve_wit_136.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without pointer TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without pointer TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_137 : OSMutexDel_partial_solve_wit_137.
Proof.
  unfold OSMutexDel_partial_solve_wit_137.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without pointer TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without pointer TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_138 : OSMutexDel_partial_solve_wit_138.
Proof.
  unfold OSMutexDel_partial_solve_wit_138.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without pointer TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pointer)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> (curPrio (node)))
  **  (tcb64_storage_without pointer TCBPrio (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_139_pure : OSMutexDel_partial_solve_wit_139_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_139 : OSMutexDel_partial_solve_wit_139.
Proof.
  unfold OSMutexDel_partial_solve_wit_139, OSMutexDel_partial_solve_wit_139_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_140_pure : OSMutexDel_partial_solve_wit_140_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_140 : OSMutexDel_partial_solve_wit_140.
Proof.
  unfold OSMutexDel_partial_solve_wit_140, OSMutexDel_partial_solve_wit_140_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_141_pure : OSMutexDel_partial_solve_wit_141_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_141 : OSMutexDel_partial_solve_wit_141.
Proof.
  unfold OSMutexDel_partial_solve_wit_141, OSMutexDel_partial_solve_wit_141_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_142_pure : OSMutexDel_partial_solve_wit_142_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_142 : OSMutexDel_partial_solve_wit_142.
Proof.
  unfold OSMutexDel_partial_solve_wit_142, OSMutexDel_partial_solve_wit_142_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_143_pure : OSMutexDel_partial_solve_wit_143_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_143 : OSMutexDel_partial_solve_wit_143.
Proof.
  unfold OSMutexDel_partial_solve_wit_143, OSMutexDel_partial_solve_wit_143_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_144_pure : OSMutexDel_partial_solve_wit_144_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_144 : OSMutexDel_partial_solve_wit_144.
Proof.
  unfold OSMutexDel_partial_solve_wit_144, OSMutexDel_partial_solve_wit_144_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_145_pure : OSMutexDel_partial_solve_wit_145_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_145 : OSMutexDel_partial_solve_wit_145.
Proof.
  unfold OSMutexDel_partial_solve_wit_145, OSMutexDel_partial_solve_wit_145_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_146_pure : OSMutexDel_partial_solve_wit_146_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_146 : OSMutexDel_partial_solve_wit_146.
Proof.
  unfold OSMutexDel_partial_solve_wit_146, OSMutexDel_partial_solve_wit_146_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(tcb64_storage_rep pointer (task_tcb64_image (sg) (node)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))))
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_147 : OSMutexDel_partial_solve_wit_147.
Proof.
  unfold OSMutexDel_partial_solve_wit_147.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_rdy_pre pointer retval (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) (curPrio (node)) (tcb_x_of_prio ((curPrio (node)))) (tcb_y_of_prio ((curPrio (node)))) (tcb_bit_x_of_prio ((curPrio (node)))) (tcb_bit_y_of_prio ((curPrio (node)))) (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))) (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))) )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_rdy_pre pointer retval (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) (curPrio (node)) (tcb_x_of_prio ((curPrio (node)))) (tcb_y_of_prio ((curPrio (node)))) (tcb_bit_x_of_prio ((curPrio (node)))) (tcb_bit_y_of_prio ((curPrio (node)))) (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))) (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))) )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_148 : OSMutexDel_partial_solve_wit_148.
Proof.
  unfold OSMutexDel_partial_solve_wit_148.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_rdy_pre pointer retval (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) (curPrio (node)) (tcb_x_of_prio ((curPrio (node)))) (tcb_y_of_prio ((curPrio (node)))) (tcb_bit_x_of_prio ((curPrio (node)))) (tcb_bit_y_of_prio ((curPrio (node)))) (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))) (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))) )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_rdy_pre pointer retval (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) (curPrio (node)) (tcb_x_of_prio ((curPrio (node)))) (tcb_y_of_prio ((curPrio (node)))) (tcb_bit_x_of_prio ((curPrio (node)))) (tcb_bit_y_of_prio ((curPrio (node)))) (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))) (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))) )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_149 : OSMutexDel_partial_solve_wit_149.
Proof.
  unfold OSMutexDel_partial_solve_wit_149.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_rdy_pre pointer retval (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) (curPrio (node)) (tcb_x_of_prio ((curPrio (node)))) (tcb_y_of_prio ((curPrio (node)))) (tcb_bit_x_of_prio ((curPrio (node)))) (tcb_bit_y_of_prio ((curPrio (node)))) (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))) (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))) )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_rdy_pre pointer retval (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) (curPrio (node)) (tcb_x_of_prio ((curPrio (node)))) (tcb_y_of_prio ((curPrio (node)))) (tcb_bit_x_of_prio ((curPrio (node)))) (tcb_bit_y_of_prio ((curPrio (node)))) (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))) (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))) )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_150 : OSMutexDel_partial_solve_wit_150.
Proof.
  unfold OSMutexDel_partial_solve_wit_150.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_rdy_pre pointer retval (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) (curPrio (node)) (tcb_x_of_prio ((curPrio (node)))) (tcb_y_of_prio ((curPrio (node)))) (tcb_bit_x_of_prio ((curPrio (node)))) (tcb_bit_y_of_prio ((curPrio (node)))) (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))) (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))) )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_rdy_pre pointer retval (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) (curPrio (node)) (tcb_x_of_prio ((curPrio (node)))) (tcb_y_of_prio ((curPrio (node)))) (tcb_bit_x_of_prio ((curPrio (node)))) (tcb_bit_y_of_prio ((curPrio (node)))) (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))) (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))) )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_151 : OSMutexDel_partial_solve_wit_151.
Proof.
  unfold OSMutexDel_partial_solve_wit_151.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_rdy_pre pointer retval (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) (curPrio (node)) (tcb_x_of_prio ((curPrio (node)))) (tcb_y_of_prio ((curPrio (node)))) (tcb_bit_x_of_prio ((curPrio (node)))) (tcb_bit_y_of_prio ((curPrio (node)))) (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))) (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))) )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_rdy_pre pointer retval (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) (curPrio (node)) (tcb_x_of_prio ((curPrio (node)))) (tcb_y_of_prio ((curPrio (node)))) (tcb_bit_x_of_prio ((curPrio (node)))) (tcb_bit_y_of_prio ((curPrio (node)))) (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))) (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))) )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_152 : OSMutexDel_partial_solve_wit_152.
Proof.
  unfold OSMutexDel_partial_solve_wit_152.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_rdy_pre pointer retval (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) (curPrio (node)) (tcb_x_of_prio ((curPrio (node)))) (tcb_y_of_prio ((curPrio (node)))) (tcb_bit_x_of_prio ((curPrio (node)))) (tcb_bit_y_of_prio ((curPrio (node)))) (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))) (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))) )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_rdy_pre pointer retval (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) (curPrio (node)) (tcb_x_of_prio ((curPrio (node)))) (tcb_y_of_prio ((curPrio (node)))) (tcb_bit_x_of_prio ((curPrio (node)))) (tcb_bit_y_of_prio ((curPrio (node)))) (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))) (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))) )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_153 : OSMutexDel_partial_solve_wit_153.
Proof.
  unfold OSMutexDel_partial_solve_wit_153.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_rdy_pre pointer retval (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) (curPrio (node)) (tcb_x_of_prio ((curPrio (node)))) (tcb_y_of_prio ((curPrio (node)))) (tcb_bit_x_of_prio ((curPrio (node)))) (tcb_bit_y_of_prio ((curPrio (node)))) (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))) (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))) )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_rdy_pre pointer retval (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) (curPrio (node)) (tcb_x_of_prio ((curPrio (node)))) (tcb_y_of_prio ((curPrio (node)))) (tcb_bit_x_of_prio ((curPrio (node)))) (tcb_bit_y_of_prio ((curPrio (node)))) (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))) (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))) )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_154 : OSMutexDel_partial_solve_wit_154.
Proof.
  unfold OSMutexDel_partial_solve_wit_154.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group kind_2 pointer count group free node owner retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_rdy_pre pointer retval (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) (curPrio (node)) (tcb_x_of_prio ((curPrio (node)))) (tcb_y_of_prio ((curPrio (node)))) (tcb_bit_x_of_prio ((curPrio (node)))) (tcb_bit_y_of_prio ((curPrio (node)))) (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))) (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))) )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_rdy_pre pointer retval (task_tcb64_image (sg) (node)) (mutex_del_priority_values (sg) ((mutex_del_released_table (entry) ((unsigned_last_nbits ((Z.shiftr count 8)) (8)))))) (sched_row_values ((entry.(TskState) )) (((entry.(SchedState) ).(readyList) ))) (curPrio (node)) (tcb_x_of_prio ((curPrio (node)))) (tcb_y_of_prio ((curPrio (node)))) (tcb_bit_x_of_prio ((curPrio (node)))) (tcb_bit_y_of_prio ((curPrio (node)))) (encode_ready_grp (((entry.(SchedState) ).(readyList) )) ((entry.(TskState) ))) (encode_task_link (sg) (((entry.(SchedState) ).(curTaskID) ))) (sched_priority_byte (((entry.(SchedState) ).(curSchedPrio) ))) )
  **  (mutex_del_priority_frame sg entry owner )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_155_pure : OSMutexDel_partial_solve_wit_155_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_155 : OSMutexDel_partial_solve_wit_155.
Proof.
  unfold OSMutexDel_partial_solve_wit_155, OSMutexDel_partial_solve_wit_155_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_parent_prepared sg eid entry prepared current mutex )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_parent_prepared sg eid entry prepared current mutex )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_156 : OSMutexDel_partial_solve_wit_156.
Proof.
  unfold OSMutexDel_partial_solve_wit_156, OSMutexDel_partial_solve_wit_156_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr prepared_2 state event mutex_2 priorities cpu_sr_2 entry_2 current_2 tasks_waiting_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25.
  intros h Hheap.
  assert (Hgroup_nonzero : encode_event_wait_grp event.(waitList) state.(TskState) <> 0).
  { intro Hz; rewrite Hz in PreH1; vm_compute in PreH1; contradiction. }
  assert (Hspatial :
(mutex_del_parent_loop_rest sg eid entry_2 prepared_2 state current_2 event mutex_2 priorities )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (event))) ((state.(TskState) ))))
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_parent_loop_rest sg eid entry_2 prepared_2 state current_2 event mutex_2 priorities )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (event))) ((state.(TskState) ))))
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_157 : OSMutexDel_partial_solve_wit_157.
Proof.
  unfold OSMutexDel_partial_solve_wit_157, OSMutexDel_partial_solve_wit_157_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr prepared_2 state event mutex_2 priorities cpu_sr_2 entry_2 current_2 tasks_waiting_2 tid old PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25.
  intros h Hheap.
  assert (Hrows_address : &("OSRdyTbl") = sg.(g_OSRdyTbl))
    by (unfold mutex_del_parent_layout in PreH6; tauto).
  assert (Hgroup_address : &("OSRdyGrp") = sg.(g_OSRdyGrp))
    by (unfold mutex_del_parent_layout in PreH6; tauto).
  assert (Htable_address : &("OSTCBPrioTbl") = sg.(g_OSTCBPrioTbl))
    by (unfold mutex_del_parent_layout in PreH6; tauto).
  assert (Hunmap_address : &("OSUnMapTbl") = sg.(g_OSUnMapTbl))
    by (unfold mutex_del_parent_layout in PreH6; tauto).
  assert (Hspatial :
(event_task_rdy_pre sg (state.(TskState) ) eid event tid old 16 2 (encode_ready_grp (((state.(SchedState) ).(readyList) )) ((state.(TskState) ))) (sched_row_values ((state.(TskState) )) (((state.(SchedState) ).(readyList) ))) )
  **  (mutex_del_parent_wake_call_rest sg eid entry_2 prepared_2 state current_2 event mutex_2 priorities tid old )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)
|--
(event_task_rdy_pre sg (state.(TskState) ) eid event tid old 16 2 (encode_ready_grp (((state.(SchedState) ).(readyList) )) ((state.(TskState) ))) (sched_row_values ((state.(TskState) )) (((state.(SchedState) ).(readyList) ))) )
  **  (mutex_del_parent_wake_call_rest sg eid entry_2 prepared_2 state current_2 event mutex_2 priorities tid old )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_158_pure : OSMutexDel_partial_solve_wit_158_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_158 : OSMutexDel_partial_solve_wit_158.
Proof.
  unfold OSMutexDel_partial_solve_wit_158, OSMutexDel_partial_solve_wit_158_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr prepared_2 state event mutex_2 priorities cpu_sr_2 entry_2 current_2 tasks_waiting_2 tid old retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25.
  intros h Hheap.
  assert (Hspatial :
(event_task_rdy_post sg (state.(TskState) ) eid event tid old 0 16 2 (encode_ready_grp (((state.(SchedState) ).(readyList) )) ((state.(TskState) ))) (sched_row_values ((state.(TskState) )) (((state.(SchedState) ).(readyList) ))) retval )
  **  (mutex_del_parent_wake_call_rest sg eid entry_2 prepared_2 state current_2 event mutex_2 priorities tid old )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)
|--
(event_task_rdy_post sg (state.(TskState) ) eid event tid old 0 16 2 (encode_ready_grp (((state.(SchedState) ).(readyList) )) ((state.(TskState) ))) (sched_row_values ((state.(TskState) )) (((state.(SchedState) ).(readyList) ))) retval )
  **  (mutex_del_parent_wake_call_rest sg eid entry_2 prepared_2 state current_2 event mutex_2 priorities tid old )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_159 : OSMutexDel_partial_solve_wit_159.
Proof.
  unfold OSMutexDel_partial_solve_wit_159, OSMutexDel_partial_solve_wit_159_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr prepared_2 state event mutex_2 priorities cpu_sr_2 entry_2 current_2 tasks_waiting_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25.
  intros h Hheap.
  assert (Hgroup_range :
(mutex_del_parent_loop_rest sg eid entry_2 prepared_2 state current_2 event mutex_2 priorities )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (event))) ((state.(TskState) ))))
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)
|-- coq_prop (0 <= encode_event_wait_grp event.(waitList) state.(TskState) <= 255)).
  { prop_apply_p (store_uchar_range (&(pe # "os_event" ->ₛ "OSEventGrp"))
      (encode_event_wait_grp event.(waitList) state.(TskState))).
    Intros; entailer!. }
  pose proof (Hgroup_range h Hheap) as Hgroup_bound.
  change (0 <= encode_event_wait_grp event.(waitList) state.(TskState) <= 255) in Hgroup_bound.
  assert (Hgroup_cast : unsigned_last_nbits
    (encode_event_wait_grp event.(waitList) state.(TskState)) 32 =
    encode_event_wait_grp event.(waitList) state.(TskState)).
  { apply unsigned_last_nbits_eq.
    change (0 <= encode_event_wait_grp event.(waitList) state.(TskState) < 4294967296); lia. }
  assert (Hgroup_zero : encode_event_wait_grp event.(waitList) state.(TskState) = 0)
    by (rewrite Hgroup_cast in PreH1; exact PreH1).
  assert (Hspatial :
(mutex_del_parent_loop_rest sg eid entry_2 prepared_2 state current_2 event mutex_2 priorities )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((waitList (event))) ((state.(TskState) ))))
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_parent_loop_rest sg eid entry_2 prepared_2 state current_2 event mutex_2 priorities )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)).
  { rewrite Hgroup_zero; entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_160_pure : OSMutexDel_partial_solve_wit_160_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_160 : OSMutexDel_partial_solve_wit_160.
Proof.
  unfold OSMutexDel_partial_solve_wit_160, OSMutexDel_partial_solve_wit_160_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr prepared_2 state event mutex_2 priorities cpu_sr_2 entry_2 current_2 tasks_waiting_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_parent_drained sg eid entry_2 prepared_2 state current_2 event mutex_2 priorities )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_parent_drained sg eid entry_2 prepared_2 state current_2 event mutex_2 priorities )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_161 : OSMutexDel_partial_solve_wit_161.
Proof.
  unfold OSMutexDel_partial_solve_wit_161, OSMutexDel_partial_solve_wit_161_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr prepared_2 state event mutex_2 priorities cpu_sr_2 entry_2 current_2 tasks_waiting_2 kind pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26.
  intros h Hheap.
  assert (Hcount_range :
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_drained_rest sg eid entry_2 prepared_2 state current_2 event mutex_2 priorities )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)
|-- coq_prop (0 <= count <= 65535)).
  { prop_apply_p (store_ushort_range (&(pe # "os_event" ->ₛ "OSEventCnt")) count).
    Intros; entailer!. }
  pose proof (Hcount_range h Hheap) as Hcount_bound.
  change (0 <= count <= 65535) in Hcount_bound.
  assert (Hcount_cast : unsigned_last_nbits (Z.shiftr count 8) 8 = Z.shiftr count 8).
  { apply unsigned_last_nbits_eq.
    change (0 <= Z.shiftr count 8 < 256).
    rewrite Z.shiftr_div_pow2 by lia.
    change (0 <= count / 256 < 256).
    split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_drained_rest sg eid entry_2 prepared_2 state current_2 event mutex_2 priorities )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> kind)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pointer)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> count)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> free)
  **  (mutex_del_parent_drained_rest sg eid entry_2 prepared_2 state current_2 event mutex_2 priorities )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_162_pure : OSMutexDel_partial_solve_wit_162_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_162 : OSMutexDel_partial_solve_wit_162.
Proof.
  unfold OSMutexDel_partial_solve_wit_162, OSMutexDel_partial_solve_wit_162_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex_2 prepared tasks_waiting cpu_sr prepared_2 state event mutex priorities cpu_sr_2 entry_2 current_2 tasks_waiting_2 kind pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_parent_drained sg eid entry_2 prepared_2 state current_2 event mutex priorities )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_parent_drained sg eid entry_2 prepared_2 state current_2 event mutex priorities )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_163_pure : OSMutexDel_partial_solve_wit_163_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_163 : OSMutexDel_partial_solve_wit_163.
Proof.
  unfold OSMutexDel_partial_solve_wit_163, OSMutexDel_partial_solve_wit_163_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex_2 prepared tasks_waiting cpu_sr prepared_2 state event mutex priorities cpu_sr_2 entry_2 current_2 tasks_waiting_2 kind pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30.
  intros h Hheap.
  assert (Hspatial :
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((state.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (mutex_del_parent_drained_without_priority sg eid entry_2 prepared_2 state current_2 event mutex priorities )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)
|--
(((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr count 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_prio_tbl_missing_i sg ((state.(TskState) ).(prioTbl) ) (unsigned_last_nbits ((Z.shiftr count 8)) (8)) )
  **  (mutex_del_parent_drained_without_priority sg eid entry_2 prepared_2 state current_2 event mutex priorities )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_164_pure : OSMutexDel_partial_solve_wit_164_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_164 : OSMutexDel_partial_solve_wit_164.
Proof.
  unfold OSMutexDel_partial_solve_wit_164, OSMutexDel_partial_solve_wit_164_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr prepared_2 state event mutex_2 priorities cpu_sr_2 entry_2 current_2 tasks_waiting_2 kind pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_parent_drained sg eid entry_2 prepared_2 state current_2 event mutex_2 priorities )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_parent_drained sg eid entry_2 prepared_2 state current_2 event mutex_2 priorities )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_165_pure : OSMutexDel_partial_solve_wit_165_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_165 : OSMutexDel_partial_solve_wit_165.
Proof.
  unfold OSMutexDel_partial_solve_wit_165, OSMutexDel_partial_solve_wit_165_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr prepared_2 state event mutex_2 priorities cpu_sr_2 entry_2 current_2 tasks_waiting_2 kind pointer count group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_parent_drained sg eid entry_2 prepared_2 state current_2 event mutex_2 priorities )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_parent_drained sg eid entry_2 prepared_2 state current_2 event mutex_2 priorities )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry_2 )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr_2 entry_2 )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_166 : OSMutexDel_partial_solve_wit_166.
Proof.
  unfold OSMutexDel_partial_solve_wit_166, OSMutexDel_partial_solve_wit_166_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry_2 current_2 mutex prepared tasks_waiting_2 cpu_sr_2 prepared_2 state event mutex_2 priorities cpu_sr entry current tasks_waiting kind pointer count group_2 free_2 kind_2 pointer_2 count_2 group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29.
  intros h Hheap.
  pose proof (proj2 (proj2 (proj2 PreH1))) as Hrecycle_values.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> free)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pe)
  **  (mutex_del_parent_drained_rest sg eid entry prepared_2 state current event mutex_2 priorities )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> free)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pe)
  **  (mutex_del_parent_drained_rest sg eid entry prepared_2 state current event mutex_2 priorities )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_167 : OSMutexDel_partial_solve_wit_167.
Proof.
  unfold OSMutexDel_partial_solve_wit_167, OSMutexDel_partial_solve_wit_167_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry_2 current_2 mutex prepared tasks_waiting_2 cpu_sr_2 prepared_2 state event mutex_2 priorities cpu_sr entry current tasks_waiting kind pointer count group_2 free_2 kind_2 pointer_2 count_2 group free PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31.
  intros h Hheap.
  pose proof (proj2 (proj2 (proj2 PreH1))) as Hrecycle_values.
  assert (Hspatial :
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> free)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pe)
  **  (mutex_del_parent_drained_rest sg eid entry prepared_2 state current event mutex_2 priorities )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> free)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pe)
  **  (mutex_del_parent_drained_rest sg eid entry prepared_2 state current event mutex_2 priorities )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_168_pure : OSMutexDel_partial_solve_wit_168_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_168_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry_2 current mutex prepared tasks_waiting cpu_sr state event mutex_2 cpu_sr_2 entry current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32.
  intros h Hheap.
  rewrite PreH3 in PreH1.
  exact (conj (conj PreH17 PreH18) PreH1).
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_168 : OSMutexDel_partial_solve_wit_168.
Proof.
  unfold OSMutexDel_partial_solve_wit_168, OSMutexDel_partial_solve_wit_168_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry_2 current mutex prepared tasks_waiting cpu_sr state event mutex_2 cpu_sr_2 entry current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32.
  intros h Hheap.
  assert (Hobservation : mutex_del_parent_critical_observation sg eid opt_in 0 0 1 entry checkpoint)
    by (rewrite <- PreH3; exact PreH1).
  assert (Hspatial :
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr_2 before entry checkpoint )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr_2 before entry checkpoint )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_169_pure : OSMutexDel_partial_solve_wit_169_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_169_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry_2 current mutex prepared tasks_waiting cpu_sr state event mutex_2 cpu_sr_2 entry current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32.
  intros h Hheap.
  rewrite PreH3 in PreH1.
  exact (conj (conj PreH17 PreH18) PreH1).
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_169 : OSMutexDel_partial_solve_wit_169.
Proof.
  unfold OSMutexDel_partial_solve_wit_169, OSMutexDel_partial_solve_wit_169_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry_2 current mutex prepared tasks_waiting cpu_sr state event mutex_2 cpu_sr_2 entry current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32.
  intros h Hheap.
  assert (Hobservation : mutex_del_parent_critical_observation sg eid opt_in 0 0 0 entry checkpoint)
    by (pose proof PreH1 as Hactual; rewrite PreH3 in Hactual; exact Hactual).
  assert (Hspatial :
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr_2 before entry checkpoint )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr_2 before entry checkpoint )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_170_pure : OSMutexDel_partial_solve_wit_170_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_170_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry_2 current mutex prepared tasks_waiting cpu_sr state event mutex_2 cpu_sr_2 entry current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34.
  intros h Hheap.
  rewrite PreH3 in PreH1.
  exact (conj (conj PreH19 PreH20) PreH1).
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_170 : OSMutexDel_partial_solve_wit_170.
Proof.
  unfold OSMutexDel_partial_solve_wit_170, OSMutexDel_partial_solve_wit_170_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry_2 current mutex prepared tasks_waiting cpu_sr state event mutex_2 cpu_sr_2 entry current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34.
  intros h Hheap.
  assert (Hobservation : mutex_del_parent_critical_observation sg eid opt_in 0 0 1 entry checkpoint)
    by (rewrite <- PreH3; exact PreH1).
  assert (Hspatial :
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr_2 before entry checkpoint )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr_2 before entry checkpoint )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_171_pure : OSMutexDel_partial_solve_wit_171_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_171_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry_2 current mutex prepared tasks_waiting cpu_sr state event mutex_2 cpu_sr_2 entry current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34.
  intros h Hheap.
  rewrite PreH3 in PreH1.
  exact (conj (conj PreH19 PreH20) PreH1).
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_171 : OSMutexDel_partial_solve_wit_171.
Proof.
  unfold OSMutexDel_partial_solve_wit_171, OSMutexDel_partial_solve_wit_171_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry_2 current mutex prepared tasks_waiting cpu_sr state event mutex_2 cpu_sr_2 entry current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34.
  intros h Hheap.
  assert (Hobservation : mutex_del_parent_critical_observation sg eid opt_in 0 0 0 entry checkpoint)
    by (pose proof PreH1 as Hactual; rewrite PreH3 in Hactual; exact Hactual).
  assert (Hspatial :
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr_2 before entry checkpoint )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr_2 before entry checkpoint )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_172_pure : OSMutexDel_partial_solve_wit_172_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_172 : OSMutexDel_partial_solve_wit_172.
Proof.
  unfold OSMutexDel_partial_solve_wit_172, OSMutexDel_partial_solve_wit_172_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr_2 state event mutex_2 cpu_sr entry_2 current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry_2 checkpoint )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry_2 checkpoint )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_173_pure : OSMutexDel_partial_solve_wit_173_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_173 : OSMutexDel_partial_solve_wit_173.
Proof.
  unfold OSMutexDel_partial_solve_wit_173, OSMutexDel_partial_solve_wit_173_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr_2 state event mutex_2 cpu_sr entry_2 current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry_2 checkpoint )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry_2 checkpoint )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_174_pure : OSMutexDel_partial_solve_wit_174_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_174 : OSMutexDel_partial_solve_wit_174.
Proof.
  unfold OSMutexDel_partial_solve_wit_174, OSMutexDel_partial_solve_wit_174_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr_2 state event mutex_2 cpu_sr entry_2 current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry_2 checkpoint )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry_2 checkpoint )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_175_pure : OSMutexDel_partial_solve_wit_175_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_175 : OSMutexDel_partial_solve_wit_175.
Proof.
  unfold OSMutexDel_partial_solve_wit_175, OSMutexDel_partial_solve_wit_175_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr_2 state event mutex_2 cpu_sr entry_2 current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry_2 checkpoint )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry_2 checkpoint )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_176 : OSMutexDel_partial_solve_wit_176.
Proof.
  unfold OSMutexDel_partial_solve_wit_176.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr state event mutex_2 cpu_sr_2 entry_2 current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask checkpoint )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask checkpoint )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_177 : OSMutexDel_partial_solve_wit_177.
Proof.
  unfold OSMutexDel_partial_solve_wit_177.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr state event mutex_2 cpu_sr_2 entry_2 current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask checkpoint )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask checkpoint )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_178 : OSMutexDel_partial_solve_wit_178.
Proof.
  unfold OSMutexDel_partial_solve_wit_178.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr state event mutex_2 cpu_sr_2 entry_2 current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask checkpoint )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask checkpoint )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_179 : OSMutexDel_partial_solve_wit_179.
Proof.
  unfold OSMutexDel_partial_solve_wit_179.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr state event mutex_2 cpu_sr_2 entry_2 current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask checkpoint )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask checkpoint )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_180_pure : OSMutexDel_partial_solve_wit_180_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_180 : OSMutexDel_partial_solve_wit_180.
Proof.
  unfold OSMutexDel_partial_solve_wit_180, OSMutexDel_partial_solve_wit_180_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr state event mutex_2 cpu_sr_2 entry_2 current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint returned current_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_return_at source_env external platform saved_local sg context mask returned current_3 )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_return_at source_env external platform saved_local sg context mask returned current_3 )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_181_pure : OSMutexDel_partial_solve_wit_181_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_181 : OSMutexDel_partial_solve_wit_181.
Proof.
  unfold OSMutexDel_partial_solve_wit_181, OSMutexDel_partial_solve_wit_181_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr state event mutex_2 cpu_sr_2 entry_2 current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint returned current_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_return_at source_env external platform saved_local sg context mask returned current_3 )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_return_at source_env external platform saved_local sg context mask returned current_3 )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_182_pure : OSMutexDel_partial_solve_wit_182_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_182 : OSMutexDel_partial_solve_wit_182.
Proof.
  unfold OSMutexDel_partial_solve_wit_182, OSMutexDel_partial_solve_wit_182_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr state event mutex_2 cpu_sr_2 entry_2 current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint returned current_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_sched_pre source_env external platform saved_local sg returned mask current_3 )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_sched_pre source_env external platform saved_local sg returned mask current_3 )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_183_pure : OSMutexDel_partial_solve_wit_183_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_183 : OSMutexDel_partial_solve_wit_183.
Proof.
  unfold OSMutexDel_partial_solve_wit_183, OSMutexDel_partial_solve_wit_183_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr state event mutex_2 cpu_sr_2 entry_2 current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint returned current_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_sched_pre source_env external platform saved_local sg returned mask current_3 )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_sched_pre source_env external platform saved_local sg returned mask current_3 )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_184_pure : OSMutexDel_partial_solve_wit_184_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_184 : OSMutexDel_partial_solve_wit_184.
Proof.
  unfold OSMutexDel_partial_solve_wit_184, OSMutexDel_partial_solve_wit_184_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr state event mutex_2 cpu_sr_2 entry_2 current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint returned current_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43.
  intros h Hheap.
  assert (Hspatial :
(os_sched_continuation_call_pre (mutex_del_runtime_sched_environment (source_env)) saved_local mutex_del_stack_resources sg returned mask current_3 )
  **  ((pd) # UChar  |-> err_in)
|--
(os_sched_continuation_call_pre (mutex_del_runtime_sched_environment (source_env)) saved_local mutex_del_stack_resources sg returned mask current_3 )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_185_pure : OSMutexDel_partial_solve_wit_185_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_185 : OSMutexDel_partial_solve_wit_185.
Proof.
  unfold OSMutexDel_partial_solve_wit_185, OSMutexDel_partial_solve_wit_185_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current mutex prepared tasks_waiting cpu_sr state event mutex_2 cpu_sr_2 entry_2 current_2 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint returned current_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41.
  intros h Hheap.
  assert (Hspatial :
(os_sched_continuation_call_pre (mutex_del_runtime_sched_environment (source_env)) saved_local mutex_del_stack_resources sg returned mask current_3 )
  **  ((pd) # UChar  |-> err_in)
|--
(os_sched_continuation_call_pre (mutex_del_runtime_sched_environment (source_env)) saved_local mutex_del_stack_resources sg returned mask current_3 )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_186_pure : OSMutexDel_partial_solve_wit_186_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_186 : OSMutexDel_partial_solve_wit_186.
Proof.
  unfold OSMutexDel_partial_solve_wit_186, OSMutexDel_partial_solve_wit_186_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current_2 mutex prepared tasks_waiting cpu_sr state event mutex_2 cpu_sr_2 entry_2 current_3 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint returned current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42.
  intros h Hheap.
  assert (Hspatial :
(sched_del_history_return_post (mutex_del_runtime_sched_environment (source_env)) (mutex_program_region (configuration)) saved_local sg returned mask current )
  **  ((pd) # UChar  |-> err_in)
|--
(sched_del_history_return_post (mutex_del_runtime_sched_environment (source_env)) (mutex_program_region (configuration)) saved_local sg returned mask current )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_187_pure : OSMutexDel_partial_solve_wit_187_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_187 : OSMutexDel_partial_solve_wit_187.
Proof.
  unfold OSMutexDel_partial_solve_wit_187, OSMutexDel_partial_solve_wit_187_aux.
  intros H_pure.
  intros X pd err_in opt_in pe eid before mask context sg saved_local configuration platform external source_env entry current_2 mutex prepared tasks_waiting cpu_sr state event mutex_2 cpu_sr_2 entry_2 current_3 tasks_waiting_2 kind pointer count group free kind_2 pointer_2 count_2 group_2 free_2 checkpoint returned current PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44.
  intros h Hheap.
  assert (Hspatial :
(sched_del_history_return_post (mutex_del_runtime_sched_environment (source_env)) (mutex_program_region (configuration)) saved_local sg returned mask current )
  **  ((pd) # UChar  |-> err_in)
|--
(sched_del_history_return_post (mutex_del_runtime_sched_environment (source_env)) (mutex_program_region (configuration)) saved_local sg returned mask current )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_188 : OSMutexDel_partial_solve_wit_188.
Proof.
  unfold OSMutexDel_partial_solve_wit_188.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_189 : OSMutexDel_partial_solve_wit_189.
Proof.
  unfold OSMutexDel_partial_solve_wit_189.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_190 : OSMutexDel_partial_solve_wit_190.
Proof.
  unfold OSMutexDel_partial_solve_wit_190.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_191 : OSMutexDel_partial_solve_wit_191.
Proof.
  unfold OSMutexDel_partial_solve_wit_191.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_192 : OSMutexDel_partial_solve_wit_192.
Proof.
  unfold OSMutexDel_partial_solve_wit_192.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_193 : OSMutexDel_partial_solve_wit_193.
Proof.
  unfold OSMutexDel_partial_solve_wit_193.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_194 : OSMutexDel_partial_solve_wit_194.
Proof.
  unfold OSMutexDel_partial_solve_wit_194.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_195 : OSMutexDel_partial_solve_wit_195.
Proof.
  unfold OSMutexDel_partial_solve_wit_195.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_api_restore_source_post source_env external platform (mutex_program_region (configuration)) saved_local sg context mask entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_196_pure : OSMutexDel_partial_solve_wit_196_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_196 : OSMutexDel_partial_solve_wit_196.
Proof.
  unfold OSMutexDel_partial_solve_wit_196, OSMutexDel_partial_solve_wit_196_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_197_pure : OSMutexDel_partial_solve_wit_197_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_197 : OSMutexDel_partial_solve_wit_197.
Proof.
  unfold OSMutexDel_partial_solve_wit_197, OSMutexDel_partial_solve_wit_197_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_198_pure : OSMutexDel_partial_solve_wit_198_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_198 : OSMutexDel_partial_solve_wit_198.
Proof.
  unfold OSMutexDel_partial_solve_wit_198, OSMutexDel_partial_solve_wit_198_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_199_pure : OSMutexDel_partial_solve_wit_199_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_199 : OSMutexDel_partial_solve_wit_199.
Proof.
  unfold OSMutexDel_partial_solve_wit_199, OSMutexDel_partial_solve_wit_199_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_200_pure : OSMutexDel_partial_solve_wit_200_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_200 : OSMutexDel_partial_solve_wit_200.
Proof.
  unfold OSMutexDel_partial_solve_wit_200, OSMutexDel_partial_solve_wit_200_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_201_pure : OSMutexDel_partial_solve_wit_201_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_201 : OSMutexDel_partial_solve_wit_201.
Proof.
  unfold OSMutexDel_partial_solve_wit_201, OSMutexDel_partial_solve_wit_201_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_202_pure : OSMutexDel_partial_solve_wit_202_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_202 : OSMutexDel_partial_solve_wit_202.
Proof.
  unfold OSMutexDel_partial_solve_wit_202, OSMutexDel_partial_solve_wit_202_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_203_pure : OSMutexDel_partial_solve_wit_203_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_203 : OSMutexDel_partial_solve_wit_203.
Proof.
  unfold OSMutexDel_partial_solve_wit_203, OSMutexDel_partial_solve_wit_203_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_continuation_source_restore_pre source_env external platform (mutex_program_region (configuration)) saved_local sg context mask cpu_sr entry entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_204_pure : OSMutexDel_partial_solve_wit_204_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_204 : OSMutexDel_partial_solve_wit_204.
Proof.
  unfold OSMutexDel_partial_solve_wit_204, OSMutexDel_partial_solve_wit_204_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_205_pure : OSMutexDel_partial_solve_wit_205_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_205 : OSMutexDel_partial_solve_wit_205.
Proof.
  unfold OSMutexDel_partial_solve_wit_205, OSMutexDel_partial_solve_wit_205_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_206_pure : OSMutexDel_partial_solve_wit_206_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_206 : OSMutexDel_partial_solve_wit_206.
Proof.
  unfold OSMutexDel_partial_solve_wit_206, OSMutexDel_partial_solve_wit_206_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_207_pure : OSMutexDel_partial_solve_wit_207_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_207 : OSMutexDel_partial_solve_wit_207.
Proof.
  unfold OSMutexDel_partial_solve_wit_207, OSMutexDel_partial_solve_wit_207_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_208_pure : OSMutexDel_partial_solve_wit_208_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_208 : OSMutexDel_partial_solve_wit_208.
Proof.
  unfold OSMutexDel_partial_solve_wit_208, OSMutexDel_partial_solve_wit_208_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_209_pure : OSMutexDel_partial_solve_wit_209_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_209 : OSMutexDel_partial_solve_wit_209.
Proof.
  unfold OSMutexDel_partial_solve_wit_209, OSMutexDel_partial_solve_wit_209_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_210_pure : OSMutexDel_partial_solve_wit_210_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_210 : OSMutexDel_partial_solve_wit_210.
Proof.
  unfold OSMutexDel_partial_solve_wit_210, OSMutexDel_partial_solve_wit_210_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_211_pure : OSMutexDel_partial_solve_wit_211_pure.
Proof. pre_process; entailer!. Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_211 : OSMutexDel_partial_solve_wit_211.
Proof.
  unfold OSMutexDel_partial_solve_wit_211, OSMutexDel_partial_solve_wit_211_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hspatial :
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)
|--
(mutex_del_runtime_program_restore_pre platform (mutex_program_region (configuration)) sg context mask cpu_sr before entry entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_212 : OSMutexDel_partial_solve_wit_212.
Proof.
  unfold OSMutexDel_partial_solve_wit_212, OSMutexDel_partial_solve_wit_212_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hlive : mutex_del_parent_live sg eid entry)
    by (exists acquired, mutex; exact PreH3).
  assert (Hspatial :
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_213 : OSMutexDel_partial_solve_wit_213.
Proof.
  unfold OSMutexDel_partial_solve_wit_213, OSMutexDel_partial_solve_wit_213_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hlive : mutex_del_parent_live sg eid entry)
    by (exists acquired, mutex; exact PreH3).
  assert (Hspatial :
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_214 : OSMutexDel_partial_solve_wit_214.
Proof.
  unfold OSMutexDel_partial_solve_wit_214, OSMutexDel_partial_solve_wit_214_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hlive : mutex_del_parent_live sg eid entry)
    by (exists acquired, mutex; exact PreH3).
  assert (Hspatial :
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_215 : OSMutexDel_partial_solve_wit_215.
Proof.
  unfold OSMutexDel_partial_solve_wit_215, OSMutexDel_partial_solve_wit_215_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hlive : mutex_del_parent_live sg eid entry)
    by (exists acquired, mutex; exact PreH3).
  assert (Hspatial :
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_216 : OSMutexDel_partial_solve_wit_216.
Proof.
  unfold OSMutexDel_partial_solve_wit_216, OSMutexDel_partial_solve_wit_216_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hlive : mutex_del_parent_live sg eid entry)
    by (exists acquired, mutex; exact PreH3).
  assert (Hspatial :
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_217 : OSMutexDel_partial_solve_wit_217.
Proof.
  unfold OSMutexDel_partial_solve_wit_217, OSMutexDel_partial_solve_wit_217_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hlive : mutex_del_parent_live sg eid entry)
    by (exists acquired, mutex; exact PreH3).
  assert (Hspatial :
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_218 : OSMutexDel_partial_solve_wit_218.
Proof.
  unfold OSMutexDel_partial_solve_wit_218, OSMutexDel_partial_solve_wit_218_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hlive : mutex_del_parent_live sg eid entry)
    by (exists acquired, mutex; exact PreH3).
  assert (Hspatial :
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexDel_partial_solve_wit_219 : OSMutexDel_partial_solve_wit_219.
Proof.
  unfold OSMutexDel_partial_solve_wit_219, OSMutexDel_partial_solve_wit_219_aux.
  intros H_pure.
  intros X pd err_in opt_in pe observed eid before mask context sg saved_local configuration platform external source_env cpu_sr entry kind acquired mutex initial_group PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hlive : mutex_del_parent_live sg eid entry)
    by (exists acquired, mutex; exact PreH3).
  assert (Hspatial :
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  ((pd) # UChar  |-> err_in)
|--
(UCOS2_inv sg entry )
  **  (unmap_table_rep sg )
  **  (critical_region_masked platform (mutex_program_region (configuration)) sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) cpu_sr entry )
  **  (mutex_del_continuation_acquired source_env external platform saved_local sg context entry )
  **  ((pd) # UChar  |-> err_in)).
  { subst; try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

