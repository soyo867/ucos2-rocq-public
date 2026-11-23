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
From Ucos2Verify.VC.code.tick Require Import time_tick_complement_goal.
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
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_complement_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OSTimeTick_safety_wit_1 : OSTimeTick_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_safety_wit_2 : OSTimeTick_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_safety_wit_3 : OSTimeTick_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_safety_wit_4 : OSTimeTick_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_safety_wit_5 : OSTimeTick_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_safety_wit_6 : OSTimeTick_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_safety_wit_7 : OSTimeTick_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_safety_wit_8 : OSTimeTick_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_safety_wit_9 : OSTimeTick_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_safety_wit_10 : OSTimeTick_safety_wit_10.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_safety_wit_11 : OSTimeTick_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_safety_wit_12 : OSTimeTick_safety_wit_12.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_1 : OSTimeTick_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_2_pure : OSTimeTick_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_2 : OSTimeTick_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_3 : OSTimeTick_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_4_pure : OSTimeTick_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_4 : OSTimeTick_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_5 : OSTimeTick_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_6_pure : OSTimeTick_partial_solve_wit_6_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_6 : OSTimeTick_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_7_pure : OSTimeTick_partial_solve_wit_7_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_7 : OSTimeTick_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_8_pure : OSTimeTick_partial_solve_wit_8_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_8 : OSTimeTick_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_9_pure : OSTimeTick_partial_solve_wit_9_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_9 : OSTimeTick_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_10 : OSTimeTick_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_11 : OSTimeTick_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_12 : OSTimeTick_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_13 : OSTimeTick_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_14_pure : OSTimeTick_partial_solve_wit_14_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_14 : OSTimeTick_partial_solve_wit_14.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_15_pure : OSTimeTick_partial_solve_wit_15_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_15 : OSTimeTick_partial_solve_wit_15.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_16_pure : OSTimeTick_partial_solve_wit_16_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_16 : OSTimeTick_partial_solve_wit_16.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_17_pure : OSTimeTick_partial_solve_wit_17_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_17 : OSTimeTick_partial_solve_wit_17.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_18_pure : OSTimeTick_partial_solve_wit_18_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_18 : OSTimeTick_partial_solve_wit_18.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_19_pure : OSTimeTick_partial_solve_wit_19_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_19 : OSTimeTick_partial_solve_wit_19.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_20_pure : OSTimeTick_partial_solve_wit_20_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_20 : OSTimeTick_partial_solve_wit_20.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_21_pure : OSTimeTick_partial_solve_wit_21_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_21 : OSTimeTick_partial_solve_wit_21.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_22_pure : OSTimeTick_partial_solve_wit_22_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_22 : OSTimeTick_partial_solve_wit_22.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_23 : OSTimeTick_partial_solve_wit_23.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_24 : OSTimeTick_partial_solve_wit_24.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_25 : OSTimeTick_partial_solve_wit_25.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_26 : OSTimeTick_partial_solve_wit_26.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_27 : OSTimeTick_partial_solve_wit_27.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_28_pure : OSTimeTick_partial_solve_wit_28_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_28 : OSTimeTick_partial_solve_wit_28.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_29_pure : OSTimeTick_partial_solve_wit_29_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_29 : OSTimeTick_partial_solve_wit_29.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_30_pure : OSTimeTick_partial_solve_wit_30_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_30 : OSTimeTick_partial_solve_wit_30.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_31_pure : OSTimeTick_partial_solve_wit_31_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_31 : OSTimeTick_partial_solve_wit_31.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_32_pure : OSTimeTick_partial_solve_wit_32_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_32 : OSTimeTick_partial_solve_wit_32.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_33_pure : OSTimeTick_partial_solve_wit_33_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeTick_partial_solve_wit_33 : OSTimeTick_partial_solve_wit_33.
Proof. Admitted. 

