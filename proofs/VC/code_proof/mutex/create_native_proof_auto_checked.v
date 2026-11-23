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
From Ucos2Verify.VC.code.mutex Require Import create_native_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.mutex_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wait_list_init_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.full_interrupt_localization.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_publication_spec.
Import MutexCreatePublication.
Import UCOS2_C_Rules MutexCreateFull MutexCreateCall MutexCreateSpatial MutexCreateInitialization MutexCreatePrivateContext.
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.mutex_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wait_list_init_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.full_interrupt_localization.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_publication_spec.
Import MutexCreatePublication.
Import UCOS2_C_Rules MutexCreateFull MutexCreateCall MutexCreateSpatial MutexCreateInitialization MutexCreatePrivateContext.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSMutexCreate_safety_wit_1 : OSMutexCreate_safety_wit_1.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_2 : OSMutexCreate_safety_wit_2.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_3 : OSMutexCreate_safety_wit_3.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_4_priority_enabled : OSMutexCreate_safety_wit_4_priority_enabled.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_5_priority_disabled : OSMutexCreate_safety_wit_5_priority_disabled.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_6_priority_enabled : OSMutexCreate_safety_wit_6_priority_enabled.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_7_priority_disabled : OSMutexCreate_safety_wit_7_priority_disabled.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_8_priority_enabled : OSMutexCreate_safety_wit_8_priority_enabled.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_9_priority_enabled : OSMutexCreate_safety_wit_9_priority_enabled.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_10_priority_enabled : OSMutexCreate_safety_wit_10_priority_enabled.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_11_priority_enabled : OSMutexCreate_safety_wit_11_priority_enabled.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_12_priority_enabled : OSMutexCreate_safety_wit_12_priority_enabled.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_13_priority_disabled : OSMutexCreate_safety_wit_13_priority_disabled.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_14_priority_enabled : OSMutexCreate_safety_wit_14_priority_enabled.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_15_priority_disabled : OSMutexCreate_safety_wit_15_priority_disabled.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_16_priority_enabled : OSMutexCreate_safety_wit_16_priority_enabled.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_17_priority_enabled : OSMutexCreate_safety_wit_17_priority_enabled.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_18_priority_disabled : OSMutexCreate_safety_wit_18_priority_disabled.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_20_priority_disabled : OSMutexCreate_safety_wit_20_priority_disabled.
Proof.
  pre_process.
  replace prio_pre with 255 by lia.
  entailer!.
  all: vm_compute; congruence.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_21_priority_enabled : OSMutexCreate_safety_wit_21_priority_enabled.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_22_priority_disabled : OSMutexCreate_safety_wit_22_priority_disabled.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_23_priority_enabled : OSMutexCreate_safety_wit_23_priority_enabled.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_safety_wit_24_priority_disabled : OSMutexCreate_safety_wit_24_priority_disabled.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_1 : OSMutexCreate_partial_solve_wit_1.
Proof.
  unfold OSMutexCreate_partial_solve_wit_1.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
|--
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. entailer!. }
  refine (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_2 : OSMutexCreate_partial_solve_wit_2.
Proof.
  unfold OSMutexCreate_partial_solve_wit_2.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
|--
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_3 : OSMutexCreate_partial_solve_wit_3.
Proof.
  unfold OSMutexCreate_partial_solve_wit_3.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
|--
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_4 : OSMutexCreate_partial_solve_wit_4.
Proof.
  unfold OSMutexCreate_partial_solve_wit_4.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
|--
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_5 : OSMutexCreate_partial_solve_wit_5.
Proof.
  unfold OSMutexCreate_partial_solve_wit_5.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
|--
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_6 : OSMutexCreate_partial_solve_wit_6.
Proof.
  unfold OSMutexCreate_partial_solve_wit_6.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
|--
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (UCOS2_state_inv (sg) (before)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (intNesting ((before.(IntrState) ))))
  **  (UCOS2_inv_without_os_int_nesting sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_7_priority_enabled_pure : OSMutexCreate_partial_solve_wit_7_priority_enabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_7_priority_enabled : OSMutexCreate_partial_solve_wit_7_priority_enabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_7_priority_enabled, OSMutexCreate_partial_solve_wit_7_priority_enabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
|--
(coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_8_priority_disabled_pure : OSMutexCreate_partial_solve_wit_8_priority_disabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_8_priority_disabled : OSMutexCreate_partial_solve_wit_8_priority_disabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_8_priority_disabled, OSMutexCreate_partial_solve_wit_8_priority_disabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
|--
(coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_9_priority_disabled : OSMutexCreate_partial_solve_wit_9_priority_disabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_9_priority_disabled.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
|--
(interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_10_priority_enabled : OSMutexCreate_partial_solve_wit_10_priority_enabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_10_priority_enabled.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_inv sg before )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (interrupt_platform_running platform invocation origin mask )
|--
(interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_11_priority_enabled : OSMutexCreate_partial_solve_wit_11_priority_enabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_11_priority_enabled.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10.
  intros h Hheap.
  assert (Hspatial :
(closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_12_priority_disabled : OSMutexCreate_partial_solve_wit_12_priority_disabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_12_priority_disabled.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9.
  intros h Hheap.
  assert (Hspatial :
(closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(closed platform critical sg invocation origin mask before )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_13_priority_disabled_pure : OSMutexCreate_partial_solve_wit_13_priority_disabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_13_priority_disabled : OSMutexCreate_partial_solve_wit_13_priority_disabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_13_priority_disabled, OSMutexCreate_partial_solve_wit_13_priority_disabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform entry retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_14_priority_enabled_pure : OSMutexCreate_partial_solve_wit_14_priority_enabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_14_priority_enabled : OSMutexCreate_partial_solve_wit_14_priority_enabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_14_priority_enabled, OSMutexCreate_partial_solve_wit_14_priority_enabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform entry retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_15_priority_enabled_pure : OSMutexCreate_partial_solve_wit_15_priority_enabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_15_priority_enabled : OSMutexCreate_partial_solve_wit_15_priority_enabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_15_priority_enabled, OSMutexCreate_partial_solve_wit_15_priority_enabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14.
  intros h Hheap.
  assert (Hpriority_enabled : prio_in <> 255) by lia.
  assert (Hpriority_table_index : prio_in < 64) by lia.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_16_priority_enabled_pure : OSMutexCreate_partial_solve_wit_16_priority_enabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_16_priority_enabled : OSMutexCreate_partial_solve_wit_16_priority_enabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_16_priority_enabled, OSMutexCreate_partial_solve_wit_16_priority_enabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (priority_value (sg) (entry) (prio_in)))
  **  (priority_table_missing sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (priority_value (sg) (entry) (prio_in)))
  **  (priority_table_missing sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_17_priority_enabled_pure : OSMutexCreate_partial_solve_wit_17_priority_enabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_17_priority_enabled : OSMutexCreate_partial_solve_wit_17_priority_enabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_17_priority_enabled, OSMutexCreate_partial_solve_wit_17_priority_enabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry entry_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_2)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (UCOS2_inv sg entry_2 )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_18_priority_enabled_pure : OSMutexCreate_partial_solve_wit_18_priority_enabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_18_priority_enabled : OSMutexCreate_partial_solve_wit_18_priority_enabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_18_priority_enabled, OSMutexCreate_partial_solve_wit_18_priority_enabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 1)
  **  (priority_table_missing sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 1)
  **  (priority_table_missing sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_19_priority_disabled_pure : OSMutexCreate_partial_solve_wit_19_priority_disabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_19_priority_disabled : OSMutexCreate_partial_solve_wit_19_priority_disabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_19_priority_disabled, OSMutexCreate_partial_solve_wit_19_priority_disabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_20_priority_enabled_pure : OSMutexCreate_partial_solve_wit_20_priority_enabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_20_priority_enabled : OSMutexCreate_partial_solve_wit_20_priority_enabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_20_priority_enabled, OSMutexCreate_partial_solve_wit_20_priority_enabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry_2 entry PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_21_priority_enabled_pure : OSMutexCreate_partial_solve_wit_21_priority_enabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_21_priority_enabled : OSMutexCreate_partial_solve_wit_21_priority_enabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_21_priority_enabled, OSMutexCreate_partial_solve_wit_21_priority_enabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry_2 entry_3 entry PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
  **  (reserved_priority_table_missing sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
  **  (reserved_priority_table_missing sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_22_priority_disabled_pure : OSMutexCreate_partial_solve_wit_22_priority_disabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_22_priority_disabled : OSMutexCreate_partial_solve_wit_22_priority_disabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_22_priority_disabled, OSMutexCreate_partial_solve_wit_22_priority_disabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_23_priority_disabled_pure : OSMutexCreate_partial_solve_wit_23_priority_disabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_23_priority_disabled : OSMutexCreate_partial_solve_wit_23_priority_disabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_23_priority_disabled, OSMutexCreate_partial_solve_wit_23_priority_disabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry_2 entry PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_24_priority_enabled_pure : OSMutexCreate_partial_solve_wit_24_priority_enabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_24_priority_enabled : OSMutexCreate_partial_solve_wit_24_priority_enabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_24_priority_enabled, OSMutexCreate_partial_solve_wit_24_priority_enabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry_2 entry_3 entry_4 entry PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (priority_table sg entry )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_25_priority_enabled_pure : OSMutexCreate_partial_solve_wit_25_priority_enabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_25_priority_enabled : OSMutexCreate_partial_solve_wit_25_priority_enabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_25_priority_enabled, OSMutexCreate_partial_solve_wit_25_priority_enabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry entry_2 entry_3 entry_4 entry_5 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_5)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_5)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_5) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_5 )
  **  (UCOS2_inv sg entry_5 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_5)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_5 )
  **  (UCOS2_inv sg entry_5 )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_5)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_5) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. try rewrite PreH39. try rewrite PreH40. try rewrite PreH41. try rewrite PreH42. try rewrite PreH43. try rewrite PreH44. try rewrite PreH45. try rewrite PreH46. try rewrite PreH47. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_26_priority_disabled_pure : OSMutexCreate_partial_solve_wit_26_priority_disabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_26_priority_disabled : OSMutexCreate_partial_solve_wit_26_priority_disabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_26_priority_disabled, OSMutexCreate_partial_solve_wit_26_priority_disabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry entry_2 entry_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (UCOS2_inv sg entry_3 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (UCOS2_inv sg entry_3 )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_27_priority_disabled_pure : OSMutexCreate_partial_solve_wit_27_priority_disabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_27_priority_disabled : OSMutexCreate_partial_solve_wit_27_priority_disabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_27_priority_disabled, OSMutexCreate_partial_solve_wit_27_priority_disabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_28_priority_enabled_pure : OSMutexCreate_partial_solve_wit_28_priority_enabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_28_priority_enabled : OSMutexCreate_partial_solve_wit_28_priority_enabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_28_priority_enabled, OSMutexCreate_partial_solve_wit_28_priority_enabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry_2 entry PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (head_residual sg entry )
  **  (reserved_priority_table sg entry prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry)))
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  { exact (fun h H => H). }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_29_priority_enabled : OSMutexCreate_partial_solve_wit_29_priority_enabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_29_priority_enabled.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry entry_2 eid rest image entry_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (node_residual sg entry_3 eid )
  **  (reserved_priority_table sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_3)))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (event_storage_without_field false (free_head (sg) (entry_2)) image EventPtrField )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
((&(((free_head (sg) (entry_3)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (node_residual sg entry_3 eid )
  **  (reserved_priority_table sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_3)))
  **  (event_storage_without_field false (free_head (sg) (entry_2)) image EventPtrField )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_30_priority_disabled : OSMutexCreate_partial_solve_wit_30_priority_disabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_30_priority_disabled.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry eid rest image entry_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_2) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (node_residual sg entry_2 eid )
  **  (reserved_priority_table sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (event_storage_without_field false (free_head (sg) (entry)) image EventPtrField )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_2) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (node_residual sg entry_2 eid )
  **  (reserved_priority_table sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (free_head (sg) (entry_2)))
  **  (event_storage_without_field false (free_head (sg) (entry)) image EventPtrField )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_31_priority_disabled_pure : OSMutexCreate_partial_solve_wit_31_priority_disabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_31_priority_disabled : OSMutexCreate_partial_solve_wit_31_priority_disabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_31_priority_disabled, OSMutexCreate_partial_solve_wit_31_priority_disabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry eid rest image entry_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22.
  intros h Hheap.
  assert (Hspatial :
((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_2) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (node_residual sg entry_2 eid )
  **  (reserved_priority_table sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (event_storage_without_field false (free_head (sg) (entry)) image EventPtrField )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_2)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_2) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_2) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_2 )
  **  (node_residual sg entry_2 eid )
  **  (reserved_priority_table sg entry_2 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (event_storage_without_field false (free_head (sg) (entry)) image EventPtrField )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_32_priority_enabled_pure : OSMutexCreate_partial_solve_wit_32_priority_enabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_32_priority_enabled : OSMutexCreate_partial_solve_wit_32_priority_enabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_32_priority_enabled, OSMutexCreate_partial_solve_wit_32_priority_enabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry entry_2 eid rest image entry_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32.
  intros h Hheap.
  assert (Hspatial :
((&(((free_head (sg) (entry_3)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (node_residual sg entry_3 eid )
  **  (reserved_priority_table sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (event_storage_without_field false (free_head (sg) (entry_2)) image EventPtrField )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (node_residual sg entry_3 eid )
  **  (reserved_priority_table sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  (event_storage_without_field false (free_head (sg) (entry_2)) image EventPtrField )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_33_priority_enabled : OSMutexCreate_partial_solve_wit_33_priority_enabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_33_priority_enabled.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry entry_2 entry_3 eid rest image entry_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35.
  intros h Hheap.
  pose proof (mutex_create_pcp_cnt_encoding_exact__leaf_pure_and_global_localization prio_pre ltac:(lia)) as Hencoding.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (node_residual sg entry_4 eid )
  **  (reserved_priority_table sg entry_4 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (event_wait_list_init_pre &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding (free_head (sg) (entry_2)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(event_wait_list_init_pre &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (node_residual sg entry_4 eid )
  **  (reserved_priority_table sg entry_4 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (initialization_padding (free_head (sg) (entry_2)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  { rewrite Hencoding. try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_34_priority_disabled : OSMutexCreate_partial_solve_wit_34_priority_disabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_34_priority_disabled.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry entry_2 eid rest image entry_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (node_residual sg entry_3 eid )
  **  (reserved_priority_table sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.shiftl prio_pre 8) 255))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (event_wait_list_init_pre &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding (free_head (sg) (entry)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(event_wait_list_init_pre &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (node_residual sg entry_3 eid )
  **  (reserved_priority_table sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventType")) # UChar  |->_)
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.shiftl prio_pre 8) 255))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (initialization_padding (free_head (sg) (entry)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_35_priority_disabled_pure : OSMutexCreate_partial_solve_wit_35_priority_disabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_35_priority_disabled : OSMutexCreate_partial_solve_wit_35_priority_disabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_35_priority_disabled, OSMutexCreate_partial_solve_wit_35_priority_disabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry entry_2 eid rest image entry_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25.
  intros h Hheap.
  assert (Hspatial :
(event_wait_list_init_post &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (node_residual sg entry_3 eid )
  **  (reserved_priority_table sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.shiftl prio_pre 8) 255))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (initialization_padding (free_head (sg) (entry)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (node_residual sg entry_3 eid )
  **  (reserved_priority_table sg entry_3 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((prio_in * 256 ) + 255 ))
  **  ((&(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (event_wait_list_init_post &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding (free_head (sg) (entry)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_36_priority_enabled : OSMutexCreate_partial_solve_wit_36_priority_enabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_36_priority_enabled, OSMutexCreate_partial_solve_wit_36_priority_enabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry entry_2 entry_3 eid rest image entry_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35.
  intros h Hheap.
  pose proof (mutex_create_pcp_cnt_encoding_exact__leaf_pure_and_global_localization prio_pre ltac:(lia)) as Hencoding.
  assert (Hspatial :
(event_wait_list_init_post &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (node_residual sg entry_4 eid )
  **  (reserved_priority_table sg entry_4 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (initialization_padding (free_head (sg) (entry_2)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_object_layout_prop (sg) (eid)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (node_residual sg entry_4 eid )
  **  (reserved_priority_table sg entry_4 prio_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (event_encode_pool_link (sg) ((hd_error (rest)))))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((prio_in * 256 ) + 255 ))
  **  ((&(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  (event_wait_list_init_post &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventGrp") &(((free_head (sg) (entry_2)))  # "os_event" ->ₛ "OSEventTbl") )
  **  (initialization_padding (free_head (sg) (entry_2)) image )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  { rewrite Hencoding. try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_37_priority_enabled_pure : OSMutexCreate_partial_solve_wit_37_priority_enabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_37_priority_enabled : OSMutexCreate_partial_solve_wit_37_priority_enabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_37_priority_enabled, OSMutexCreate_partial_solve_wit_37_priority_enabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry entry_2 entry_3 eid rest image entry_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (UCOS2_inv sg (mutex_create_state (sg) (prio_in) (eid) (rest) (entry_4)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_4)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_4 )
  **  (UCOS2_inv sg (mutex_create_state (sg) (prio_in) (eid) (rest) (entry_4)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_4)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (slot_available (sg) (entry_4) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_4) (eid) (rest) (image)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry_2)))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. try rewrite PreH29. try rewrite PreH30. try rewrite PreH31. try rewrite PreH32. try rewrite PreH33. try rewrite PreH34. try rewrite PreH35. try rewrite PreH36. try rewrite PreH37. try rewrite PreH38. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_38_priority_disabled_pure : OSMutexCreate_partial_solve_wit_38_priority_disabled_pure.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_OSMutexCreate_partial_solve_wit_38_priority_disabled : OSMutexCreate_partial_solve_wit_38_priority_disabled.
Proof.
  unfold OSMutexCreate_partial_solve_wit_38_priority_disabled, OSMutexCreate_partial_solve_wit_38_priority_disabled_aux.
  intros H_pure.
  intros perr_pre prio_pre X perr_in prio_in before mask origin invocation sg critical platform retval entry entry_2 eid rest image entry_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28.
  intros h Hheap.
  assert (Hspatial :
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (UCOS2_inv sg (mutex_create_state (sg) (prio_in) (eid) (rest) (entry_3)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
(coq_prop (acquire_facts (critical) (sg) (invocation) (mask) (retval) (before) (entry_3)) )
  **  (critical_region_masked platform critical sg invocation origin retval entry_3 )
  **  (UCOS2_inv sg (mutex_create_state (sg) (255) (eid) (rest) (entry_3)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (UCOS2_state_inv (sg) (entry_3)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_table_layout_prop (sg)) )
  **  (coq_prop (slot_available (sg) (entry_3) (prio_in)) )
  **  (coq_prop (free_head_facts (sg) (entry_3) (eid) (rest) (image)) )
  **  (coq_prop (event_pointer_eq (sg) (eid) ((free_head (sg) (entry)))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)).
  {  try rewrite PreH1. try rewrite PreH2. try rewrite PreH3. try rewrite PreH4. try rewrite PreH5. try rewrite PreH6. try rewrite PreH7. try rewrite PreH8. try rewrite PreH9. try rewrite PreH10. try rewrite PreH11. try rewrite PreH12. try rewrite PreH13. try rewrite PreH14. try rewrite PreH15. try rewrite PreH16. try rewrite PreH17. try rewrite PreH18. try rewrite PreH19. try rewrite PreH20. try rewrite PreH21. try rewrite PreH22. try rewrite PreH23. try rewrite PreH24. try rewrite PreH25. try rewrite PreH26. try rewrite PreH27. try rewrite PreH28. entailer!. }
  refine (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj (conj _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Hspatial h Hheap));
    first [assumption | reflexivity | congruence | lia].
Qed. 

