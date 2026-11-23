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
From Ucos2Verify.VC.code.sched Require Import sched_continuation_goal.
From Ucos2Verify.VC.code.sched Require Import sched_continuation_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
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
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OS_Sched_return_wit_1_split_goal_spatial : OS_Sched_return_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OS_Sched_partial_solve_wit_3_pure_split_goal_1 : OS_Sched_partial_solve_wit_3_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_OS_Sched_which_implies_wit_1_split_goal_1 : OS_Sched_which_implies_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_OS_Sched_which_implies_wit_1_split_goal_spatial : OS_Sched_which_implies_wit_1_split_goal_spatial.
Proof. Abort.

