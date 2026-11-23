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
From Ucos2Verify.VC.code.task Require Import task_create_stack_proof_auto.
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

Lemma proof_of_OSTaskCreate_return_wit_1_split_goal_spatial : OSTaskCreate_return_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSTaskCreate_return_wit_2_split_goal_spatial : OSTaskCreate_return_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSTaskCreate_return_wit_3_split_goal_spatial : OSTaskCreate_return_wit_3_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSTaskCreate_return_wit_4_split_goal_spatial : OSTaskCreate_return_wit_4_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSTaskCreate_return_wit_5_split_goal_spatial : OSTaskCreate_return_wit_5_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSTaskCreate_return_wit_6_split_goal_spatial : OSTaskCreate_return_wit_6_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSTaskCreate_partial_solve_wit_2_pure_split_goal_1 : OSTaskCreate_partial_solve_wit_2_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_OSTaskCreate_partial_solve_wit_2_pure_split_goal_2 : OSTaskCreate_partial_solve_wit_2_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_OSTaskCreate_partial_solve_wit_5_pure_split_goal_1 : OSTaskCreate_partial_solve_wit_5_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_OSTaskCreate_partial_solve_wit_7_pure_split_goal_1 : OSTaskCreate_partial_solve_wit_7_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_OSTaskCreate_partial_solve_wit_15_pure_split_goal_1 : OSTaskCreate_partial_solve_wit_15_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_OSTaskCreate_partial_solve_wit_16_pure_split_goal_1 : OSTaskCreate_partial_solve_wit_16_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_OSTaskCreate_partial_solve_wit_19_pure_split_goal_1 : OSTaskCreate_partial_solve_wit_19_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_OSTaskCreate_which_implies_wit_1_split_goal_1 : OSTaskCreate_which_implies_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_OSTaskCreate_which_implies_wit_1_split_goal_spatial : OSTaskCreate_which_implies_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSTaskCreate_which_implies_wit_2_split_goal_1 : OSTaskCreate_which_implies_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_OSTaskCreate_which_implies_wit_2_split_goal_2 : OSTaskCreate_which_implies_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_OSTaskCreate_which_implies_wit_2_split_goal_3 : OSTaskCreate_which_implies_wit_2_split_goal_3.
Proof. Abort.

Lemma proof_of_OSTaskCreate_which_implies_wit_2_split_goal_4 : OSTaskCreate_which_implies_wit_2_split_goal_4.
Proof. Abort.

Lemma proof_of_OSTaskCreate_which_implies_wit_2_split_goal_5 : OSTaskCreate_which_implies_wit_2_split_goal_5.
Proof. Abort.

Lemma proof_of_OSTaskCreate_which_implies_wit_2_split_goal_6 : OSTaskCreate_which_implies_wit_2_split_goal_6.
Proof. Abort.

Lemma proof_of_OSTaskCreate_which_implies_wit_2_split_goal_7 : OSTaskCreate_which_implies_wit_2_split_goal_7.
Proof. Abort.

Lemma proof_of_OSTaskCreate_which_implies_wit_2_split_goal_spatial : OSTaskCreate_which_implies_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSTaskCreate_which_implies_wit_12_split_goal_spatial : OSTaskCreate_which_implies_wit_12_split_goal_spatial.
Proof. Abort.

