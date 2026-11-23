From SimpleC.Verification Require Import VCPrelude.
From Ucos2Verify.VC.code.sem Require Import sem_pend_task_client_goal.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.sem.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_remove_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_wait_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_checkpoint_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_clear_status_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_clear_status_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_acquire_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_restore_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_program_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_clear_status_pend_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_return_fields_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_multi_pointer_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_fields_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_resource_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_wait_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_cleanup_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_sched_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_sched_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_client_case_lib.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_sched_call_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSSemPend_safety_wit_1 : OSSemPend_safety_wit_1.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_2 : OSSemPend_safety_wit_2.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_3 : OSSemPend_safety_wit_3.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_4 : OSSemPend_safety_wit_4.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_5 : OSSemPend_safety_wit_5.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_6 : OSSemPend_safety_wit_6.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_7 : OSSemPend_safety_wit_7.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_8 : OSSemPend_safety_wit_8.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_9 : OSSemPend_safety_wit_9.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_10 : OSSemPend_safety_wit_10.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_11 : OSSemPend_safety_wit_11.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_12 : OSSemPend_safety_wit_12.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_13 : OSSemPend_safety_wit_13.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_14 : OSSemPend_safety_wit_14.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_15 : OSSemPend_safety_wit_15.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_16 : OSSemPend_safety_wit_16.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_17 : OSSemPend_safety_wit_17.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_18 : OSSemPend_safety_wit_18.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_19 : OSSemPend_safety_wit_19.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_20 : OSSemPend_safety_wit_20.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_21 : OSSemPend_safety_wit_21.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_22 : OSSemPend_safety_wit_22.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_23 : OSSemPend_safety_wit_23.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_24 : OSSemPend_safety_wit_24.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_25 : OSSemPend_safety_wit_25.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_26 : OSSemPend_safety_wit_26.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_27 : OSSemPend_safety_wit_27.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_28 : OSSemPend_safety_wit_28.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_29 : OSSemPend_safety_wit_29.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_30 : OSSemPend_safety_wit_30.
Proof. Admitted.

Lemma proof_of_OSSemPend_safety_wit_31 : OSSemPend_safety_wit_31.
Proof. Admitted.

Lemma proof_of_OSSemPend_entail_wit_1_1 : OSSemPend_entail_wit_1_1.
Proof. Admitted.

Lemma proof_of_OSSemPend_entail_wit_1_2 : OSSemPend_entail_wit_1_2.
Proof. Admitted.

Lemma proof_of_OSSemPend_entail_wit_1_3 : OSSemPend_entail_wit_1_3.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_1 : OSSemPend_partial_solve_wit_1.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_2 : OSSemPend_partial_solve_wit_2.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_3 : OSSemPend_partial_solve_wit_3.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_4 : OSSemPend_partial_solve_wit_4.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_5 : OSSemPend_partial_solve_wit_5.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_6 : OSSemPend_partial_solve_wit_6.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_7 : OSSemPend_partial_solve_wit_7.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_8 : OSSemPend_partial_solve_wit_8.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_9 : OSSemPend_partial_solve_wit_9.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_10 : OSSemPend_partial_solve_wit_10.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_11_pure : OSSemPend_partial_solve_wit_11_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_11 : OSSemPend_partial_solve_wit_11.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_12_pure : OSSemPend_partial_solve_wit_12_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_12 : OSSemPend_partial_solve_wit_12.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_13_pure : OSSemPend_partial_solve_wit_13_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_13 : OSSemPend_partial_solve_wit_13.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_14_pure : OSSemPend_partial_solve_wit_14_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_14 : OSSemPend_partial_solve_wit_14.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_15_pure : OSSemPend_partial_solve_wit_15_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_15 : OSSemPend_partial_solve_wit_15.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_16_pure : OSSemPend_partial_solve_wit_16_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_16 : OSSemPend_partial_solve_wit_16.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_17_pure : OSSemPend_partial_solve_wit_17_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_17 : OSSemPend_partial_solve_wit_17.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_18_pure : OSSemPend_partial_solve_wit_18_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_18 : OSSemPend_partial_solve_wit_18.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_19_pure : OSSemPend_partial_solve_wit_19_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_19 : OSSemPend_partial_solve_wit_19.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_20_pure : OSSemPend_partial_solve_wit_20_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_20 : OSSemPend_partial_solve_wit_20.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_21_pure : OSSemPend_partial_solve_wit_21_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_21 : OSSemPend_partial_solve_wit_21.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_22 : OSSemPend_partial_solve_wit_22.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_23 : OSSemPend_partial_solve_wit_23.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_24_pure : OSSemPend_partial_solve_wit_24_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_24 : OSSemPend_partial_solve_wit_24.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_25_pure : OSSemPend_partial_solve_wit_25_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_25 : OSSemPend_partial_solve_wit_25.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_26_pure : OSSemPend_partial_solve_wit_26_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_26 : OSSemPend_partial_solve_wit_26.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_27_pure : OSSemPend_partial_solve_wit_27_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_27 : OSSemPend_partial_solve_wit_27.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_28_pure : OSSemPend_partial_solve_wit_28_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_28 : OSSemPend_partial_solve_wit_28.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_29_pure : OSSemPend_partial_solve_wit_29_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_29 : OSSemPend_partial_solve_wit_29.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_30_pure : OSSemPend_partial_solve_wit_30_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_30 : OSSemPend_partial_solve_wit_30.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_31_pure : OSSemPend_partial_solve_wit_31_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_31 : OSSemPend_partial_solve_wit_31.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_32_pure : OSSemPend_partial_solve_wit_32_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_32 : OSSemPend_partial_solve_wit_32.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_33_pure : OSSemPend_partial_solve_wit_33_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_33 : OSSemPend_partial_solve_wit_33.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_34 : OSSemPend_partial_solve_wit_34.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_35 : OSSemPend_partial_solve_wit_35.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_36 : OSSemPend_partial_solve_wit_36.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_37 : OSSemPend_partial_solve_wit_37.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_38 : OSSemPend_partial_solve_wit_38.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_39_pure : OSSemPend_partial_solve_wit_39_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_39 : OSSemPend_partial_solve_wit_39.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_40_pure : OSSemPend_partial_solve_wit_40_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_40 : OSSemPend_partial_solve_wit_40.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_41_pure : OSSemPend_partial_solve_wit_41_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_41 : OSSemPend_partial_solve_wit_41.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_42_pure : OSSemPend_partial_solve_wit_42_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_42 : OSSemPend_partial_solve_wit_42.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_43_pure : OSSemPend_partial_solve_wit_43_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_43 : OSSemPend_partial_solve_wit_43.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_44 : OSSemPend_partial_solve_wit_44.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_45 : OSSemPend_partial_solve_wit_45.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_46_pure : OSSemPend_partial_solve_wit_46_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_46 : OSSemPend_partial_solve_wit_46.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_47_pure : OSSemPend_partial_solve_wit_47_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_47 : OSSemPend_partial_solve_wit_47.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_48_pure : OSSemPend_partial_solve_wit_48_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_48 : OSSemPend_partial_solve_wit_48.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_49_pure : OSSemPend_partial_solve_wit_49_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_49 : OSSemPend_partial_solve_wit_49.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_50_pure : OSSemPend_partial_solve_wit_50_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_50 : OSSemPend_partial_solve_wit_50.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_51_pure : OSSemPend_partial_solve_wit_51_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_51 : OSSemPend_partial_solve_wit_51.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_52_pure : OSSemPend_partial_solve_wit_52_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_52 : OSSemPend_partial_solve_wit_52.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_53_pure : OSSemPend_partial_solve_wit_53_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_53 : OSSemPend_partial_solve_wit_53.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_54_pure : OSSemPend_partial_solve_wit_54_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_54 : OSSemPend_partial_solve_wit_54.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_55_pure : OSSemPend_partial_solve_wit_55_pure.
Proof. Admitted.

Lemma proof_of_OSSemPend_partial_solve_wit_55 : OSSemPend_partial_solve_wit_55.
Proof. Admitted.

Lemma proof_of_OSSemPend_which_implies_wit_5 : OSSemPend_which_implies_wit_5.
Proof. Admitted.

Lemma proof_of_OSSemPend_which_implies_wit_11 : OSSemPend_which_implies_wit_11.
Proof. Admitted.

