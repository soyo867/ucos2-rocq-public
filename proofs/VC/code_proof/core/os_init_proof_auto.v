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
From Ucos2Verify.VC.code.core Require Import os_init_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.interrupt.spec.os_init_hook_begin_spec.
Require Import Ucos2Verify.VC.code.core.spec.init_misc_spec.
Require Import Ucos2Verify.VC.code.sched.spec.init_rdy_list_spec.
Require Import Ucos2Verify.VC.code.core.spec.init_tcb_list_selected_spec.
Require Import Ucos2Verify.VC.code.event.spec.init_event_list_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_init_spec.
Require Import Ucos2Verify.VC.code.memory.spec.mem_init_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_init_generic_spec.
Require Import Ucos2Verify.VC.code.core.spec.init_task_idle_continuation_spec.
Require Import Ucos2Verify.VC.code.core.spec.init_task_stat_continuation_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_init_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.os_init_hook_end_spec.
Require Import Ucos2Verify.VC.code.core.spec.os_debug_init_spec.
Require Import Ucos2Verify.VC.code.core.spec.os_init_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OSInit_partial_solve_wit_1 : OSInit_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_2_pure : OSInit_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_2 : OSInit_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_3 : OSInit_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_4 : OSInit_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_5_pure : OSInit_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_5 : OSInit_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_6 : OSInit_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_7 : OSInit_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_8 : OSInit_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_9 : OSInit_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_10 : OSInit_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_11_pure : OSInit_partial_solve_wit_11_pure.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_11 : OSInit_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_12 : OSInit_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_13 : OSInit_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_14_pure : OSInit_partial_solve_wit_14_pure.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_14 : OSInit_partial_solve_wit_14.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_15 : OSInit_partial_solve_wit_15.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_16 : OSInit_partial_solve_wit_16.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_17_pure : OSInit_partial_solve_wit_17_pure.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_17 : OSInit_partial_solve_wit_17.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_18 : OSInit_partial_solve_wit_18.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_19 : OSInit_partial_solve_wit_19.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_20_pure : OSInit_partial_solve_wit_20_pure.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_20 : OSInit_partial_solve_wit_20.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_21 : OSInit_partial_solve_wit_21.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_22 : OSInit_partial_solve_wit_22.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_23_pure : OSInit_partial_solve_wit_23_pure.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_23 : OSInit_partial_solve_wit_23.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_24 : OSInit_partial_solve_wit_24.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_25 : OSInit_partial_solve_wit_25.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_26 : OSInit_partial_solve_wit_26.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_27_pure : OSInit_partial_solve_wit_27_pure.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_27 : OSInit_partial_solve_wit_27.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_28 : OSInit_partial_solve_wit_28.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_29 : OSInit_partial_solve_wit_29.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_30_pure : OSInit_partial_solve_wit_30_pure.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_30 : OSInit_partial_solve_wit_30.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_31 : OSInit_partial_solve_wit_31.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_32 : OSInit_partial_solve_wit_32.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_33 : OSInit_partial_solve_wit_33.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_34 : OSInit_partial_solve_wit_34.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_35 : OSInit_partial_solve_wit_35.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_36 : OSInit_partial_solve_wit_36.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_37 : OSInit_partial_solve_wit_37.
Proof. Admitted. 

Lemma proof_of_OSInit_partial_solve_wit_38 : OSInit_partial_solve_wit_38.
Proof. Admitted. 

