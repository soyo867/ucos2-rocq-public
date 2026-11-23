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
From Ucos2Verify.VC.code.mutex Require Import mutex_post_native_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_parent_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
Local Open Scope sac_scope.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_spec.
Local Open Scope sac.

Lemma proof_of_OSMutexPost_safety_wit_1 : OSMutexPost_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_safety_wit_2 : OSMutexPost_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_safety_wit_4 : OSMutexPost_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_safety_wit_5 : OSMutexPost_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_safety_wit_6 : OSMutexPost_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_safety_wit_7 : OSMutexPost_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_safety_wit_8 : OSMutexPost_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_safety_wit_9 : OSMutexPost_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_safety_wit_10 : OSMutexPost_safety_wit_10.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_safety_wit_11 : OSMutexPost_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_safety_wit_12 : OSMutexPost_safety_wit_12.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_safety_wit_13 : OSMutexPost_safety_wit_13.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_safety_wit_14 : OSMutexPost_safety_wit_14.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_safety_wit_15 : OSMutexPost_safety_wit_15.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_safety_wit_16 : OSMutexPost_safety_wit_16.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_safety_wit_17 : OSMutexPost_safety_wit_17.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_safety_wit_18 : OSMutexPost_safety_wit_18.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_safety_wit_19 : OSMutexPost_safety_wit_19.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_safety_wit_20 : OSMutexPost_safety_wit_20.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_safety_wit_21 : OSMutexPost_safety_wit_21.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_safety_wit_22 : OSMutexPost_safety_wit_22.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_1 : OSMutexPost_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_2_pure : OSMutexPost_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_2 : OSMutexPost_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_3_pure : OSMutexPost_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_3 : OSMutexPost_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_4 : OSMutexPost_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_5_pure : OSMutexPost_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_5 : OSMutexPost_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_6 : OSMutexPost_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_7_pure : OSMutexPost_partial_solve_wit_7_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_7 : OSMutexPost_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_8_pure : OSMutexPost_partial_solve_wit_8_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_8 : OSMutexPost_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_9 : OSMutexPost_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_10_pure : OSMutexPost_partial_solve_wit_10_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_10 : OSMutexPost_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_11 : OSMutexPost_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_12_pure : OSMutexPost_partial_solve_wit_12_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_12 : OSMutexPost_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_13_pure : OSMutexPost_partial_solve_wit_13_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_13 : OSMutexPost_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_14 : OSMutexPost_partial_solve_wit_14.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_15_pure : OSMutexPost_partial_solve_wit_15_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_15 : OSMutexPost_partial_solve_wit_15.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_16_pure : OSMutexPost_partial_solve_wit_16_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_16 : OSMutexPost_partial_solve_wit_16.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_17_pure : OSMutexPost_partial_solve_wit_17_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_17 : OSMutexPost_partial_solve_wit_17.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_18 : OSMutexPost_partial_solve_wit_18.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_19 : OSMutexPost_partial_solve_wit_19.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_20 : OSMutexPost_partial_solve_wit_20.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_21_pure : OSMutexPost_partial_solve_wit_21_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_21 : OSMutexPost_partial_solve_wit_21.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_22_pure : OSMutexPost_partial_solve_wit_22_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_22 : OSMutexPost_partial_solve_wit_22.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_23_pure : OSMutexPost_partial_solve_wit_23_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_23 : OSMutexPost_partial_solve_wit_23.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_24 : OSMutexPost_partial_solve_wit_24.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_25_pure : OSMutexPost_partial_solve_wit_25_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_25 : OSMutexPost_partial_solve_wit_25.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_26_pure : OSMutexPost_partial_solve_wit_26_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_26 : OSMutexPost_partial_solve_wit_26.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_27_pure : OSMutexPost_partial_solve_wit_27_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_27 : OSMutexPost_partial_solve_wit_27.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_28 : OSMutexPost_partial_solve_wit_28.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_29 : OSMutexPost_partial_solve_wit_29.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_30_pure : OSMutexPost_partial_solve_wit_30_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_30 : OSMutexPost_partial_solve_wit_30.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_31 : OSMutexPost_partial_solve_wit_31.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_32_pure : OSMutexPost_partial_solve_wit_32_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_32 : OSMutexPost_partial_solve_wit_32.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_33_pure : OSMutexPost_partial_solve_wit_33_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_33 : OSMutexPost_partial_solve_wit_33.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_34_pure : OSMutexPost_partial_solve_wit_34_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_34 : OSMutexPost_partial_solve_wit_34.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_35 : OSMutexPost_partial_solve_wit_35.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_36_pure : OSMutexPost_partial_solve_wit_36_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_36 : OSMutexPost_partial_solve_wit_36.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_37_pure : OSMutexPost_partial_solve_wit_37_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_37 : OSMutexPost_partial_solve_wit_37.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_38_pure : OSMutexPost_partial_solve_wit_38_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_38 : OSMutexPost_partial_solve_wit_38.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_39_pure : OSMutexPost_partial_solve_wit_39_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_39 : OSMutexPost_partial_solve_wit_39.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_40_pure : OSMutexPost_partial_solve_wit_40_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_40 : OSMutexPost_partial_solve_wit_40.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_41 : OSMutexPost_partial_solve_wit_41.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_42 : OSMutexPost_partial_solve_wit_42.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_43 : OSMutexPost_partial_solve_wit_43.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_44_pure : OSMutexPost_partial_solve_wit_44_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_44 : OSMutexPost_partial_solve_wit_44.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_45_pure : OSMutexPost_partial_solve_wit_45_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_45 : OSMutexPost_partial_solve_wit_45.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_46_pure : OSMutexPost_partial_solve_wit_46_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_46 : OSMutexPost_partial_solve_wit_46.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_47_pure : OSMutexPost_partial_solve_wit_47_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_47 : OSMutexPost_partial_solve_wit_47.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_48_pure : OSMutexPost_partial_solve_wit_48_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_48 : OSMutexPost_partial_solve_wit_48.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_49_pure : OSMutexPost_partial_solve_wit_49_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_49 : OSMutexPost_partial_solve_wit_49.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_50_pure : OSMutexPost_partial_solve_wit_50_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_50 : OSMutexPost_partial_solve_wit_50.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_51_pure : OSMutexPost_partial_solve_wit_51_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_51 : OSMutexPost_partial_solve_wit_51.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_52_pure : OSMutexPost_partial_solve_wit_52_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_52 : OSMutexPost_partial_solve_wit_52.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_53 : OSMutexPost_partial_solve_wit_53.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_54 : OSMutexPost_partial_solve_wit_54.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_55 : OSMutexPost_partial_solve_wit_55.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_56_pure : OSMutexPost_partial_solve_wit_56_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_56 : OSMutexPost_partial_solve_wit_56.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_57_pure : OSMutexPost_partial_solve_wit_57_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_57 : OSMutexPost_partial_solve_wit_57.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_58_pure : OSMutexPost_partial_solve_wit_58_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_58 : OSMutexPost_partial_solve_wit_58.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_59 : OSMutexPost_partial_solve_wit_59.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_60 : OSMutexPost_partial_solve_wit_60.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_61 : OSMutexPost_partial_solve_wit_61.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_62_pure : OSMutexPost_partial_solve_wit_62_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_62 : OSMutexPost_partial_solve_wit_62.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_63_pure : OSMutexPost_partial_solve_wit_63_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_63 : OSMutexPost_partial_solve_wit_63.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_64_pure : OSMutexPost_partial_solve_wit_64_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_64 : OSMutexPost_partial_solve_wit_64.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_65_pure : OSMutexPost_partial_solve_wit_65_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_65 : OSMutexPost_partial_solve_wit_65.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_66_pure : OSMutexPost_partial_solve_wit_66_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_66 : OSMutexPost_partial_solve_wit_66.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_67_pure : OSMutexPost_partial_solve_wit_67_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_67 : OSMutexPost_partial_solve_wit_67.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_68_pure : OSMutexPost_partial_solve_wit_68_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_68 : OSMutexPost_partial_solve_wit_68.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_69_pure : OSMutexPost_partial_solve_wit_69_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_69 : OSMutexPost_partial_solve_wit_69.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_70_pure : OSMutexPost_partial_solve_wit_70_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_70 : OSMutexPost_partial_solve_wit_70.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_71_pure : OSMutexPost_partial_solve_wit_71_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_71 : OSMutexPost_partial_solve_wit_71.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_72_pure : OSMutexPost_partial_solve_wit_72_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_72 : OSMutexPost_partial_solve_wit_72.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_73 : OSMutexPost_partial_solve_wit_73.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_74 : OSMutexPost_partial_solve_wit_74.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_75_pure : OSMutexPost_partial_solve_wit_75_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_75 : OSMutexPost_partial_solve_wit_75.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_76_pure : OSMutexPost_partial_solve_wit_76_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_76 : OSMutexPost_partial_solve_wit_76.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_77_pure : OSMutexPost_partial_solve_wit_77_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_77 : OSMutexPost_partial_solve_wit_77.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_78_pure : OSMutexPost_partial_solve_wit_78_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_78 : OSMutexPost_partial_solve_wit_78.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_79_pure : OSMutexPost_partial_solve_wit_79_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_79 : OSMutexPost_partial_solve_wit_79.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_80_pure : OSMutexPost_partial_solve_wit_80_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_80 : OSMutexPost_partial_solve_wit_80.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_81_pure : OSMutexPost_partial_solve_wit_81_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_81 : OSMutexPost_partial_solve_wit_81.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_82_pure : OSMutexPost_partial_solve_wit_82_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_82 : OSMutexPost_partial_solve_wit_82.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_83_pure : OSMutexPost_partial_solve_wit_83_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_83 : OSMutexPost_partial_solve_wit_83.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_84_pure : OSMutexPost_partial_solve_wit_84_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_84 : OSMutexPost_partial_solve_wit_84.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_85_pure : OSMutexPost_partial_solve_wit_85_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_85 : OSMutexPost_partial_solve_wit_85.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_86_pure : OSMutexPost_partial_solve_wit_86_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_86 : OSMutexPost_partial_solve_wit_86.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_87 : OSMutexPost_partial_solve_wit_87.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_88 : OSMutexPost_partial_solve_wit_88.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_89 : OSMutexPost_partial_solve_wit_89.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_90_pure : OSMutexPost_partial_solve_wit_90_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_90 : OSMutexPost_partial_solve_wit_90.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_91_pure : OSMutexPost_partial_solve_wit_91_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_91 : OSMutexPost_partial_solve_wit_91.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_92_pure : OSMutexPost_partial_solve_wit_92_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_92 : OSMutexPost_partial_solve_wit_92.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_93 : OSMutexPost_partial_solve_wit_93.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_94 : OSMutexPost_partial_solve_wit_94.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_95 : OSMutexPost_partial_solve_wit_95.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_96_pure : OSMutexPost_partial_solve_wit_96_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_96 : OSMutexPost_partial_solve_wit_96.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_97_pure : OSMutexPost_partial_solve_wit_97_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_97 : OSMutexPost_partial_solve_wit_97.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_98_pure : OSMutexPost_partial_solve_wit_98_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_98 : OSMutexPost_partial_solve_wit_98.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_99 : OSMutexPost_partial_solve_wit_99.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_100 : OSMutexPost_partial_solve_wit_100.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_101 : OSMutexPost_partial_solve_wit_101.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_102_pure : OSMutexPost_partial_solve_wit_102_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_102 : OSMutexPost_partial_solve_wit_102.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_103_pure : OSMutexPost_partial_solve_wit_103_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_103 : OSMutexPost_partial_solve_wit_103.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_104_pure : OSMutexPost_partial_solve_wit_104_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_104 : OSMutexPost_partial_solve_wit_104.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_105_pure : OSMutexPost_partial_solve_wit_105_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_105 : OSMutexPost_partial_solve_wit_105.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_106_pure : OSMutexPost_partial_solve_wit_106_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_106 : OSMutexPost_partial_solve_wit_106.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_107_pure : OSMutexPost_partial_solve_wit_107_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_107 : OSMutexPost_partial_solve_wit_107.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_108_pure : OSMutexPost_partial_solve_wit_108_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_108 : OSMutexPost_partial_solve_wit_108.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_109_pure : OSMutexPost_partial_solve_wit_109_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_109 : OSMutexPost_partial_solve_wit_109.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_110_pure : OSMutexPost_partial_solve_wit_110_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_110 : OSMutexPost_partial_solve_wit_110.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_111 : OSMutexPost_partial_solve_wit_111.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_112 : OSMutexPost_partial_solve_wit_112.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_partial_solve_wit_113 : OSMutexPost_partial_solve_wit_113.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_which_implies_wit_38 : OSMutexPost_which_implies_wit_38.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_which_implies_wit_41 : OSMutexPost_which_implies_wit_41.
Proof. Admitted. 

