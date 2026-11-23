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
From Ucos2Verify.VC.code.tick Require Import time_tick_hook_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_hook_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_api_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSTimeTickHook_safety_wit_1 : OSTimeTickHook_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_OSTimeTickHook_return_wit_1 : OSTimeTickHook_return_wit_1.
Proof. Admitted. 

Lemma proof_of_OSTimeTickHook_partial_solve_wit_1 : OSTimeTickHook_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OSTimeTickHook_partial_solve_wit_2 : OSTimeTickHook_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OSTimeTickHook_partial_solve_wit_3 : OSTimeTickHook_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_OSTimeTickHook_partial_solve_wit_4_pure : OSTimeTickHook_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTickHook_partial_solve_wit_4 : OSTimeTickHook_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_OSTimeTickHook_partial_solve_wit_5 : OSTimeTickHook_partial_solve_wit_5.
Proof. Admitted. 

