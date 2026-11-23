From SimpleC.Verification Require Import VCPrelude.
From Ucos2Verify.VC.code.sched Require Import tmr_task_sched_source_goal.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_protocol_spec.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_entry_control_spec Ucos2Verify.VC.code.flag.spec.flag_pend_local_control_spec Ucos2Verify.VC.code.flag.spec.flag_pend_counter_entry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec Ucos2Verify.VC.code.sched.spec.sched_task_return_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_caller_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_sched_phase_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.lib.task_idle_ready.
Import PrimitiveComponent.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_call_spec Ucos2Verify.VC.code.flag.spec.flag_pend_active_caller_control_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_completed_caller_signal_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_signal_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_entry_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_sched_entry_call_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_sched_source_call_spec.
Local Open Scope sac.

Lemma proof_of_OS_Sched_safety_wit_1 : OS_Sched_safety_wit_1.
Proof. Admitted.

Lemma proof_of_OS_Sched_safety_wit_2 : OS_Sched_safety_wit_2.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_1_pure : OS_Sched_partial_solve_wit_1_pure.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_1 : OS_Sched_partial_solve_wit_1.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_2_pure : OS_Sched_partial_solve_wit_2_pure.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_2 : OS_Sched_partial_solve_wit_2.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_3_pure : OS_Sched_partial_solve_wit_3_pure.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_3 : OS_Sched_partial_solve_wit_3.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_4 : OS_Sched_partial_solve_wit_4.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_5_pure : OS_Sched_partial_solve_wit_5_pure.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_5 : OS_Sched_partial_solve_wit_5.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_6_pure : OS_Sched_partial_solve_wit_6_pure.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_6 : OS_Sched_partial_solve_wit_6.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_7 : OS_Sched_partial_solve_wit_7.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_8 : OS_Sched_partial_solve_wit_8.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_9_pure : OS_Sched_partial_solve_wit_9_pure.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_9 : OS_Sched_partial_solve_wit_9.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_10 : OS_Sched_partial_solve_wit_10.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_11_pure : OS_Sched_partial_solve_wit_11_pure.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_11 : OS_Sched_partial_solve_wit_11.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_12_pure : OS_Sched_partial_solve_wit_12_pure.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_12 : OS_Sched_partial_solve_wit_12.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_13_pure : OS_Sched_partial_solve_wit_13_pure.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_13 : OS_Sched_partial_solve_wit_13.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_14 : OS_Sched_partial_solve_wit_14.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_15_pure : OS_Sched_partial_solve_wit_15_pure.
Proof. Admitted.

Lemma proof_of_OS_Sched_partial_solve_wit_15 : OS_Sched_partial_solve_wit_15.
Proof. Admitted.

