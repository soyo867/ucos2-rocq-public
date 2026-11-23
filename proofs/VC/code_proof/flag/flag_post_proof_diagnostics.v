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
From Ucos2Verify.VC.code.flag Require Import flag_post_goal.
From Ucos2Verify.VC.code.flag Require Import flag_post_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import SimpleC.SL.Mem SimpleC.SL.SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt Ucos2Verify.lib.flag Ucos2Verify.lib.flag_node_fields Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_fields_spec Ucos2Verify.VC.code.flag.spec.flag_post_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec Ucos2Verify.VC.code.sched.spec.sched_fields_disabled_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope sac.

Lemma proof_of_OSFlagPost_entail_wit_1_split_goal_spatial : OSFlagPost_entail_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSFlagPost_entail_wit_2_split_goal_spatial : OSFlagPost_entail_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSFlagPost_entail_wit_5_split_goal_spatial : OSFlagPost_entail_wit_5_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSFlagPost_entail_wit_8_split_goal_spatial : OSFlagPost_entail_wit_8_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSFlagPost_entail_wit_17_split_goal_spatial : OSFlagPost_entail_wit_17_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSFlagPost_entail_wit_26_split_goal_spatial : OSFlagPost_entail_wit_26_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSFlagPost_partial_solve_wit_5_pure_split_goal_1 : OSFlagPost_partial_solve_wit_5_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_OSFlagPost_partial_solve_wit_10_pure_split_goal_1 : OSFlagPost_partial_solve_wit_10_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_OSFlagPost_partial_solve_wit_12_pure_split_goal_1 : OSFlagPost_partial_solve_wit_12_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_OSFlagPost_partial_solve_wit_13_pure_split_goal_1 : OSFlagPost_partial_solve_wit_13_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_OSFlagPost_partial_solve_wit_14_pure_split_goal_1 : OSFlagPost_partial_solve_wit_14_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_OSFlagPost_partial_solve_wit_16_pure_split_goal_1 : OSFlagPost_partial_solve_wit_16_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_OSFlagPost_partial_solve_wit_29_pure_split_goal_1 : OSFlagPost_partial_solve_wit_29_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_OSFlagPost_partial_solve_wit_33_pure_split_goal_1 : OSFlagPost_partial_solve_wit_33_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_OSFlagPost_partial_solve_wit_35_pure_split_goal_1 : OSFlagPost_partial_solve_wit_35_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_OSFlagPost_partial_solve_wit_35_pure_split_goal_2 : OSFlagPost_partial_solve_wit_35_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_OSFlagPost_partial_solve_wit_35_pure_split_goal_3 : OSFlagPost_partial_solve_wit_35_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_OSFlagPost_partial_solve_wit_42_pure_split_goal_1 : OSFlagPost_partial_solve_wit_42_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_OSFlagPost_which_implies_wit_1_split_goal_1 : OSFlagPost_which_implies_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_OSFlagPost_which_implies_wit_1_split_goal_2 : OSFlagPost_which_implies_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_OSFlagPost_which_implies_wit_1_split_goal_3 : OSFlagPost_which_implies_wit_1_split_goal_3.
Proof. Abort.

Lemma proof_of_OSFlagPost_which_implies_wit_1_split_goal_spatial : OSFlagPost_which_implies_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSFlagPost_which_implies_wit_3_split_goal_1 : OSFlagPost_which_implies_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_OSFlagPost_which_implies_wit_3_split_goal_spatial : OSFlagPost_which_implies_wit_3_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSFlagPost_which_implies_wit_22_split_goal_1 : OSFlagPost_which_implies_wit_22_split_goal_1.
Proof. Abort.

Lemma proof_of_OSFlagPost_which_implies_wit_22_split_goal_spatial : OSFlagPost_which_implies_wit_22_split_goal_spatial.
Proof. Abort.

