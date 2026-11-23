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
From Ucos2Verify.VC.code.mutex Require Import pend_native_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_api_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSMutexPend_safety_wit_1 : OSMutexPend_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_2 : OSMutexPend_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_3 : OSMutexPend_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_4 : OSMutexPend_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_5 : OSMutexPend_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_7 : OSMutexPend_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_8 : OSMutexPend_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_9 : OSMutexPend_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_10 : OSMutexPend_safety_wit_10.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_11 : OSMutexPend_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_12 : OSMutexPend_safety_wit_12.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_13 : OSMutexPend_safety_wit_13.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_20 : OSMutexPend_safety_wit_20.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_21 : OSMutexPend_safety_wit_21.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_22 : OSMutexPend_safety_wit_22.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_23 : OSMutexPend_safety_wit_23.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_24 : OSMutexPend_safety_wit_24.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_25 : OSMutexPend_safety_wit_25.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_26 : OSMutexPend_safety_wit_26.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_27 : OSMutexPend_safety_wit_27.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_28 : OSMutexPend_safety_wit_28.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_29 : OSMutexPend_safety_wit_29.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_safety_wit_30 : OSMutexPend_safety_wit_30.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_1 : OSMutexPend_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_2 : OSMutexPend_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_3_pure : OSMutexPend_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_3 : OSMutexPend_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_4 : OSMutexPend_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_5_pure : OSMutexPend_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_5 : OSMutexPend_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_6 : OSMutexPend_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_7_pure : OSMutexPend_partial_solve_wit_7_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_7 : OSMutexPend_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_8 : OSMutexPend_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_9_pure : OSMutexPend_partial_solve_wit_9_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_9 : OSMutexPend_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_10 : OSMutexPend_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_11 : OSMutexPend_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_12_pure : OSMutexPend_partial_solve_wit_12_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_12 : OSMutexPend_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_13_pure : OSMutexPend_partial_solve_wit_13_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_13 : OSMutexPend_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_14_pure : OSMutexPend_partial_solve_wit_14_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_14 : OSMutexPend_partial_solve_wit_14.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_15_pure : OSMutexPend_partial_solve_wit_15_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_15 : OSMutexPend_partial_solve_wit_15.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_16_pure : OSMutexPend_partial_solve_wit_16_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_16 : OSMutexPend_partial_solve_wit_16.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_17 : OSMutexPend_partial_solve_wit_17.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_18_pure : OSMutexPend_partial_solve_wit_18_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_18 : OSMutexPend_partial_solve_wit_18.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_19 : OSMutexPend_partial_solve_wit_19.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_20 : OSMutexPend_partial_solve_wit_20.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_21 : OSMutexPend_partial_solve_wit_21.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_22 : OSMutexPend_partial_solve_wit_22.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_23 : OSMutexPend_partial_solve_wit_23.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_24_pure : OSMutexPend_partial_solve_wit_24_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_24 : OSMutexPend_partial_solve_wit_24.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_25_pure : OSMutexPend_partial_solve_wit_25_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_25 : OSMutexPend_partial_solve_wit_25.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_26_pure : OSMutexPend_partial_solve_wit_26_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_26 : OSMutexPend_partial_solve_wit_26.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_27 : OSMutexPend_partial_solve_wit_27.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_28 : OSMutexPend_partial_solve_wit_28.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_29 : OSMutexPend_partial_solve_wit_29.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_30 : OSMutexPend_partial_solve_wit_30.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_31 : OSMutexPend_partial_solve_wit_31.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_32 : OSMutexPend_partial_solve_wit_32.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_33 : OSMutexPend_partial_solve_wit_33.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_34 : OSMutexPend_partial_solve_wit_34.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_35 : OSMutexPend_partial_solve_wit_35.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_36 : OSMutexPend_partial_solve_wit_36.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_37 : OSMutexPend_partial_solve_wit_37.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_38_pure : OSMutexPend_partial_solve_wit_38_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_38 : OSMutexPend_partial_solve_wit_38.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_39 : OSMutexPend_partial_solve_wit_39.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_40_pure : OSMutexPend_partial_solve_wit_40_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_40 : OSMutexPend_partial_solve_wit_40.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_41 : OSMutexPend_partial_solve_wit_41.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_42_pure : OSMutexPend_partial_solve_wit_42_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_42 : OSMutexPend_partial_solve_wit_42.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_43_pure : OSMutexPend_partial_solve_wit_43_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_43 : OSMutexPend_partial_solve_wit_43.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_44 : OSMutexPend_partial_solve_wit_44.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_45_pure : OSMutexPend_partial_solve_wit_45_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_45 : OSMutexPend_partial_solve_wit_45.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_46 : OSMutexPend_partial_solve_wit_46.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_47_pure : OSMutexPend_partial_solve_wit_47_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_47 : OSMutexPend_partial_solve_wit_47.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_48_pure : OSMutexPend_partial_solve_wit_48_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_48 : OSMutexPend_partial_solve_wit_48.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_49_pure : OSMutexPend_partial_solve_wit_49_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_49 : OSMutexPend_partial_solve_wit_49.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_50_pure : OSMutexPend_partial_solve_wit_50_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_50 : OSMutexPend_partial_solve_wit_50.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_51_pure : OSMutexPend_partial_solve_wit_51_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_51 : OSMutexPend_partial_solve_wit_51.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_52 : OSMutexPend_partial_solve_wit_52.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_53 : OSMutexPend_partial_solve_wit_53.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_54_pure : OSMutexPend_partial_solve_wit_54_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_54 : OSMutexPend_partial_solve_wit_54.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_55_pure : OSMutexPend_partial_solve_wit_55_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_55 : OSMutexPend_partial_solve_wit_55.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_56_pure : OSMutexPend_partial_solve_wit_56_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_56 : OSMutexPend_partial_solve_wit_56.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_57_pure : OSMutexPend_partial_solve_wit_57_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_57 : OSMutexPend_partial_solve_wit_57.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_58_pure : OSMutexPend_partial_solve_wit_58_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_58 : OSMutexPend_partial_solve_wit_58.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_59_pure : OSMutexPend_partial_solve_wit_59_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_59 : OSMutexPend_partial_solve_wit_59.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_60_pure : OSMutexPend_partial_solve_wit_60_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_60 : OSMutexPend_partial_solve_wit_60.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_61_pure : OSMutexPend_partial_solve_wit_61_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_61 : OSMutexPend_partial_solve_wit_61.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_62_pure : OSMutexPend_partial_solve_wit_62_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_62 : OSMutexPend_partial_solve_wit_62.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_63_pure : OSMutexPend_partial_solve_wit_63_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_63 : OSMutexPend_partial_solve_wit_63.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_64_pure : OSMutexPend_partial_solve_wit_64_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_64 : OSMutexPend_partial_solve_wit_64.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_65_pure : OSMutexPend_partial_solve_wit_65_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_65 : OSMutexPend_partial_solve_wit_65.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_66_pure : OSMutexPend_partial_solve_wit_66_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_66 : OSMutexPend_partial_solve_wit_66.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_67_pure : OSMutexPend_partial_solve_wit_67_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPend_partial_solve_wit_67 : OSMutexPend_partial_solve_wit_67.
Proof. Admitted. 

