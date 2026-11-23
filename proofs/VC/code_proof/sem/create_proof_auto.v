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
From Ucos2Verify.VC.code.sem Require Import create_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_api_spec.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.event_pool Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSSemCreate_safety_wit_1 : OSSemCreate_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_OSSemCreate_safety_wit_2 : OSSemCreate_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_OSSemCreate_safety_wit_3 : OSSemCreate_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_OSSemCreate_safety_wit_4 : OSSemCreate_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_OSSemCreate_safety_wit_5 : OSSemCreate_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_OSSemCreate_safety_wit_6 : OSSemCreate_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_OSSemCreate_entail_wit_6_1 : OSSemCreate_entail_wit_6_1.
Proof. Admitted. 

Lemma proof_of_OSSemCreate_return_wit_1 : OSSemCreate_return_wit_1.
Proof. Admitted. 

Lemma proof_of_OSSemCreate_partial_solve_wit_1 : OSSemCreate_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OSSemCreate_partial_solve_wit_2_pure : OSSemCreate_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_OSSemCreate_partial_solve_wit_2 : OSSemCreate_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OSSemCreate_partial_solve_wit_3_pure : OSSemCreate_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_OSSemCreate_partial_solve_wit_3 : OSSemCreate_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_OSSemCreate_partial_solve_wit_4 : OSSemCreate_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_OSSemCreate_partial_solve_wit_5 : OSSemCreate_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_OSSemCreate_partial_solve_wit_6_pure : OSSemCreate_partial_solve_wit_6_pure.
Proof. Admitted. 

Lemma proof_of_OSSemCreate_partial_solve_wit_6 : OSSemCreate_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_OSSemCreate_partial_solve_wit_7_pure : OSSemCreate_partial_solve_wit_7_pure.
Proof. Admitted. 

Lemma proof_of_OSSemCreate_partial_solve_wit_7 : OSSemCreate_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_OSSemCreate_partial_solve_wit_8 : OSSemCreate_partial_solve_wit_8.
Proof. Admitted. 

