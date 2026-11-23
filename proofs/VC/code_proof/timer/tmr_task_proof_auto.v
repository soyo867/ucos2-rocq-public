From SimpleC.Verification Require Import VCPrelude.
From Ucos2Verify.VC.code.timer Require Import tmr_task_goal.
From SimpleC.CoreLang Require Import CTypes.
Import SimpleCtypeNotations.
Require Import Ucos2Verify.VC.code.timer.spec.timer_callback_semantics.
Import TimerCallback_C_Rules.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_call_adapter_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_witness_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_iteration_entry_spec.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.task.spec.task_sw_hook_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_fields_resource_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_unlock_fields_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_pend_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_pend_adapter_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_call_layout_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_progress_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_callback_registry_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_scan_unlock_entry_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_clear_status_pend_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_callback_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_iteration_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_entry_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_unlock_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_vc_spec.
Import TimerCallback_C_Rules TimerCallback_C_Rules.Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTmr_Task_safety_wit_1 : OSTmr_Task_safety_wit_1.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_safety_wit_2 : OSTmr_Task_safety_wit_2.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_safety_wit_3 : OSTmr_Task_safety_wit_3.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_safety_wit_4 : OSTmr_Task_safety_wit_4.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_entail_wit_14 : OSTmr_Task_entail_wit_14.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_1_pure : OSTmr_Task_partial_solve_wit_1_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_1 : OSTmr_Task_partial_solve_wit_1.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_2_pure : OSTmr_Task_partial_solve_wit_2_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_2 : OSTmr_Task_partial_solve_wit_2.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_3_pure : OSTmr_Task_partial_solve_wit_3_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_3 : OSTmr_Task_partial_solve_wit_3.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_4_pure : OSTmr_Task_partial_solve_wit_4_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_4 : OSTmr_Task_partial_solve_wit_4.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_5_pure : OSTmr_Task_partial_solve_wit_5_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_5 : OSTmr_Task_partial_solve_wit_5.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_6_pure : OSTmr_Task_partial_solve_wit_6_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_6 : OSTmr_Task_partial_solve_wit_6.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_7 : OSTmr_Task_partial_solve_wit_7.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_8 : OSTmr_Task_partial_solve_wit_8.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_9 : OSTmr_Task_partial_solve_wit_9.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_10_pure : OSTmr_Task_partial_solve_wit_10_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_10 : OSTmr_Task_partial_solve_wit_10.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_11 : OSTmr_Task_partial_solve_wit_11.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_12_pure : OSTmr_Task_partial_solve_wit_12_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_12 : OSTmr_Task_partial_solve_wit_12.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_13_pure : OSTmr_Task_partial_solve_wit_13_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_13 : OSTmr_Task_partial_solve_wit_13.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_14_pure : OSTmr_Task_partial_solve_wit_14_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_14 : OSTmr_Task_partial_solve_wit_14.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_15_pure : OSTmr_Task_partial_solve_wit_15_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_15 : OSTmr_Task_partial_solve_wit_15.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_16_pure : OSTmr_Task_partial_solve_wit_16_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_16 : OSTmr_Task_partial_solve_wit_16.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_17_pure : OSTmr_Task_partial_solve_wit_17_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_17 : OSTmr_Task_partial_solve_wit_17.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_18_pure : OSTmr_Task_partial_solve_wit_18_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_18 : OSTmr_Task_partial_solve_wit_18.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_19_pure : OSTmr_Task_partial_solve_wit_19_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_19 : OSTmr_Task_partial_solve_wit_19.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_20_pure : OSTmr_Task_partial_solve_wit_20_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_20 : OSTmr_Task_partial_solve_wit_20.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_21_pure : OSTmr_Task_partial_solve_wit_21_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_21 : OSTmr_Task_partial_solve_wit_21.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_22_pure : OSTmr_Task_partial_solve_wit_22_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_22 : OSTmr_Task_partial_solve_wit_22.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_23_pure : OSTmr_Task_partial_solve_wit_23_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_23 : OSTmr_Task_partial_solve_wit_23.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_24_pure : OSTmr_Task_partial_solve_wit_24_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_24 : OSTmr_Task_partial_solve_wit_24.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_25_pure : OSTmr_Task_partial_solve_wit_25_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_25 : OSTmr_Task_partial_solve_wit_25.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_26 : OSTmr_Task_partial_solve_wit_26.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_27_pure : OSTmr_Task_partial_solve_wit_27_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_27 : OSTmr_Task_partial_solve_wit_27.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_28 : OSTmr_Task_partial_solve_wit_28.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_29 : OSTmr_Task_partial_solve_wit_29.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_30_pure : OSTmr_Task_partial_solve_wit_30_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_30 : OSTmr_Task_partial_solve_wit_30.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_31 : OSTmr_Task_partial_solve_wit_31.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_32 : OSTmr_Task_partial_solve_wit_32.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_33_pure : OSTmr_Task_partial_solve_wit_33_pure.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_33 : OSTmr_Task_partial_solve_wit_33.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_34 : OSTmr_Task_partial_solve_wit_34.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_35 : OSTmr_Task_partial_solve_wit_35.
Proof. Admitted.

Lemma proof_of_OSTmr_Task_partial_solve_wit_36 : OSTmr_Task_partial_solve_wit_36.
Proof. Admitted.

