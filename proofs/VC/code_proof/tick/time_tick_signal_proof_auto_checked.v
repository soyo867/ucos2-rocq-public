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
From Ucos2Verify.VC.code.tick Require Import time_tick_signal_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_hook_isr_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OSTmrSignal_return_wit_1 : OSTmrSignal_return_wit_1.
Proof.
  unfold OSTmrSignal_return_wit_1; intros.
  Exists after_2.
  entailer!.
Qed.

Lemma proof_of_OSTmrSignal_partial_solve_wit_1_pure : OSTmrSignal_partial_solve_wit_1_pure.
Proof.
  unfold OSTmrSignal_partial_solve_wit_1_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTmrSignal_partial_solve_wit_1 : OSTmrSignal_partial_solve_wit_1.
Proof.
  unfold OSTmrSignal_partial_solve_wit_1, OSTmrSignal_partial_solve_wit_1_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTmrSignal_partial_solve_wit_2_pure : OSTmrSignal_partial_solve_wit_2_pure.
Proof.
  unfold OSTmrSignal_partial_solve_wit_2_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTmrSignal_partial_solve_wit_2 : OSTmrSignal_partial_solve_wit_2.
Proof.
  unfold OSTmrSignal_partial_solve_wit_2, OSTmrSignal_partial_solve_wit_2_aux; intros.
  entailer!.
Qed.
