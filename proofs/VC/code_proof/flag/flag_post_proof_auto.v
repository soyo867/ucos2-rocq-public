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

Lemma proof_of_OSFlagPost_safety_wit_1 : OSFlagPost_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_2 : OSFlagPost_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_3 : OSFlagPost_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_4 : OSFlagPost_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_5 : OSFlagPost_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_6 : OSFlagPost_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_7 : OSFlagPost_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_8 : OSFlagPost_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_9 : OSFlagPost_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_10 : OSFlagPost_safety_wit_10.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_11 : OSFlagPost_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_12 : OSFlagPost_safety_wit_12.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_13 : OSFlagPost_safety_wit_13.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_14 : OSFlagPost_safety_wit_14.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_15 : OSFlagPost_safety_wit_15.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_16 : OSFlagPost_safety_wit_16.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_17 : OSFlagPost_safety_wit_17.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_18 : OSFlagPost_safety_wit_18.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_19 : OSFlagPost_safety_wit_19.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_20 : OSFlagPost_safety_wit_20.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_21 : OSFlagPost_safety_wit_21.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_22 : OSFlagPost_safety_wit_22.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_23 : OSFlagPost_safety_wit_23.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_24 : OSFlagPost_safety_wit_24.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_25 : OSFlagPost_safety_wit_25.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_26 : OSFlagPost_safety_wit_26.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_27 : OSFlagPost_safety_wit_27.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_safety_wit_28 : OSFlagPost_safety_wit_28.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_6_1 : OSFlagPost_entail_wit_6_1.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_6_2 : OSFlagPost_entail_wit_6_2.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_6_3 : OSFlagPost_entail_wit_6_3.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_6_4 : OSFlagPost_entail_wit_6_4.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_6_5 : OSFlagPost_entail_wit_6_5.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_6_6 : OSFlagPost_entail_wit_6_6.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_6_7 : OSFlagPost_entail_wit_6_7.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_6_8 : OSFlagPost_entail_wit_6_8.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_6_9 : OSFlagPost_entail_wit_6_9.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_1 : OSFlagPost_entail_wit_7_1.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_2 : OSFlagPost_entail_wit_7_2.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_3 : OSFlagPost_entail_wit_7_3.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_4 : OSFlagPost_entail_wit_7_4.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_5 : OSFlagPost_entail_wit_7_5.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_6 : OSFlagPost_entail_wit_7_6.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_7 : OSFlagPost_entail_wit_7_7.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_8 : OSFlagPost_entail_wit_7_8.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_9 : OSFlagPost_entail_wit_7_9.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_10 : OSFlagPost_entail_wit_7_10.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_11 : OSFlagPost_entail_wit_7_11.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_12 : OSFlagPost_entail_wit_7_12.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_13 : OSFlagPost_entail_wit_7_13.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_14 : OSFlagPost_entail_wit_7_14.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_15 : OSFlagPost_entail_wit_7_15.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_16 : OSFlagPost_entail_wit_7_16.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_17 : OSFlagPost_entail_wit_7_17.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_18 : OSFlagPost_entail_wit_7_18.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_19 : OSFlagPost_entail_wit_7_19.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_20 : OSFlagPost_entail_wit_7_20.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_21 : OSFlagPost_entail_wit_7_21.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_22 : OSFlagPost_entail_wit_7_22.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_23 : OSFlagPost_entail_wit_7_23.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_24 : OSFlagPost_entail_wit_7_24.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_25 : OSFlagPost_entail_wit_7_25.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_26 : OSFlagPost_entail_wit_7_26.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_7_27 : OSFlagPost_entail_wit_7_27.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_12 : OSFlagPost_entail_wit_12.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_entail_wit_21 : OSFlagPost_entail_wit_21.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_return_wit_1 : OSFlagPost_return_wit_1.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_return_wit_2 : OSFlagPost_return_wit_2.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_return_wit_3 : OSFlagPost_return_wit_3.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_return_wit_4 : OSFlagPost_return_wit_4.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_return_wit_5 : OSFlagPost_return_wit_5.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_return_wit_6 : OSFlagPost_return_wit_6.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_1 : OSFlagPost_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_2 : OSFlagPost_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_3_pure : OSFlagPost_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_3 : OSFlagPost_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_4 : OSFlagPost_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_5 : OSFlagPost_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_6 : OSFlagPost_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_7 : OSFlagPost_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_8_pure : OSFlagPost_partial_solve_wit_8_pure.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_8 : OSFlagPost_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_9 : OSFlagPost_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_10 : OSFlagPost_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_11 : OSFlagPost_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_12 : OSFlagPost_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_13 : OSFlagPost_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_14 : OSFlagPost_partial_solve_wit_14.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_15 : OSFlagPost_partial_solve_wit_15.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_16 : OSFlagPost_partial_solve_wit_16.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_17 : OSFlagPost_partial_solve_wit_17.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_18_pure : OSFlagPost_partial_solve_wit_18_pure.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_18 : OSFlagPost_partial_solve_wit_18.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_19_pure : OSFlagPost_partial_solve_wit_19_pure.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_19 : OSFlagPost_partial_solve_wit_19.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_20_pure : OSFlagPost_partial_solve_wit_20_pure.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_20 : OSFlagPost_partial_solve_wit_20.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_21_pure : OSFlagPost_partial_solve_wit_21_pure.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_21 : OSFlagPost_partial_solve_wit_21.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_22_pure : OSFlagPost_partial_solve_wit_22_pure.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_22 : OSFlagPost_partial_solve_wit_22.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_23_pure : OSFlagPost_partial_solve_wit_23_pure.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_23 : OSFlagPost_partial_solve_wit_23.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_24_pure : OSFlagPost_partial_solve_wit_24_pure.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_24 : OSFlagPost_partial_solve_wit_24.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_25_pure : OSFlagPost_partial_solve_wit_25_pure.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_25 : OSFlagPost_partial_solve_wit_25.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_26_pure : OSFlagPost_partial_solve_wit_26_pure.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_26 : OSFlagPost_partial_solve_wit_26.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_27_pure : OSFlagPost_partial_solve_wit_27_pure.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_27 : OSFlagPost_partial_solve_wit_27.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_28 : OSFlagPost_partial_solve_wit_28.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_29 : OSFlagPost_partial_solve_wit_29.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_30 : OSFlagPost_partial_solve_wit_30.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_31_pure : OSFlagPost_partial_solve_wit_31_pure.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_31 : OSFlagPost_partial_solve_wit_31.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_32 : OSFlagPost_partial_solve_wit_32.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_33 : OSFlagPost_partial_solve_wit_33.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_34 : OSFlagPost_partial_solve_wit_34.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_35 : OSFlagPost_partial_solve_wit_35.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_36_pure : OSFlagPost_partial_solve_wit_36_pure.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_36 : OSFlagPost_partial_solve_wit_36.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_37 : OSFlagPost_partial_solve_wit_37.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_38 : OSFlagPost_partial_solve_wit_38.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_39 : OSFlagPost_partial_solve_wit_39.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_40_pure : OSFlagPost_partial_solve_wit_40_pure.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_40 : OSFlagPost_partial_solve_wit_40.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_41_pure : OSFlagPost_partial_solve_wit_41_pure.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_41 : OSFlagPost_partial_solve_wit_41.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_42 : OSFlagPost_partial_solve_wit_42.
Proof. Admitted. 

Lemma proof_of_OSFlagPost_partial_solve_wit_43 : OSFlagPost_partial_solve_wit_43.
Proof. Admitted. 

