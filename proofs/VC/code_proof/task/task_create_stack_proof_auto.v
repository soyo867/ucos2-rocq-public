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
From Ucos2Verify.VC.code.task Require Import task_create_stack_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_call_protocol_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_runtime_consumer_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_modular_init_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_modular_call_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_calls_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.task.spec.task_create_name_api_spec.
Local Open Scope sac.

Lemma proof_of_OSTaskCreate_safety_wit_1 : OSTaskCreate_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_safety_wit_2 : OSTaskCreate_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_safety_wit_3 : OSTaskCreate_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_safety_wit_4 : OSTaskCreate_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_safety_wit_5 : OSTaskCreate_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_safety_wit_6 : OSTaskCreate_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_safety_wit_7 : OSTaskCreate_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_safety_wit_8 : OSTaskCreate_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_safety_wit_9 : OSTaskCreate_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_safety_wit_10 : OSTaskCreate_safety_wit_10.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_safety_wit_11 : OSTaskCreate_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_1 : OSTaskCreate_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_2 : OSTaskCreate_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_3 : OSTaskCreate_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_4_pure : OSTaskCreate_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_4 : OSTaskCreate_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_5 : OSTaskCreate_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_6_pure : OSTaskCreate_partial_solve_wit_6_pure.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_6 : OSTaskCreate_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_7 : OSTaskCreate_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_8_pure : OSTaskCreate_partial_solve_wit_8_pure.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_8 : OSTaskCreate_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_9_pure : OSTaskCreate_partial_solve_wit_9_pure.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_9 : OSTaskCreate_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_10_pure : OSTaskCreate_partial_solve_wit_10_pure.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_10 : OSTaskCreate_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_11_pure : OSTaskCreate_partial_solve_wit_11_pure.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_11 : OSTaskCreate_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_12_pure : OSTaskCreate_partial_solve_wit_12_pure.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_12 : OSTaskCreate_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_13_pure : OSTaskCreate_partial_solve_wit_13_pure.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_13 : OSTaskCreate_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_14_pure : OSTaskCreate_partial_solve_wit_14_pure.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_14 : OSTaskCreate_partial_solve_wit_14.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_15 : OSTaskCreate_partial_solve_wit_15.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_16 : OSTaskCreate_partial_solve_wit_16.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_17_pure : OSTaskCreate_partial_solve_wit_17_pure.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_17 : OSTaskCreate_partial_solve_wit_17.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_18_pure : OSTaskCreate_partial_solve_wit_18_pure.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_18 : OSTaskCreate_partial_solve_wit_18.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_19 : OSTaskCreate_partial_solve_wit_19.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_20 : OSTaskCreate_partial_solve_wit_20.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_21_pure : OSTaskCreate_partial_solve_wit_21_pure.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_21 : OSTaskCreate_partial_solve_wit_21.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_22_pure : OSTaskCreate_partial_solve_wit_22_pure.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_22 : OSTaskCreate_partial_solve_wit_22.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_23_pure : OSTaskCreate_partial_solve_wit_23_pure.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_23 : OSTaskCreate_partial_solve_wit_23.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_24_pure : OSTaskCreate_partial_solve_wit_24_pure.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_24 : OSTaskCreate_partial_solve_wit_24.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_25_pure : OSTaskCreate_partial_solve_wit_25_pure.
Proof. Admitted. 

Lemma proof_of_OSTaskCreate_partial_solve_wit_25 : OSTaskCreate_partial_solve_wit_25.
Proof. Admitted. 

