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
From Ucos2Verify.VC.code.tick Require Import time_tick_goal.
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

Lemma proof_of_OSTimeTick_safety_wit_1 : OSTimeTick_safety_wit_1.
Proof.
  unfold OSTimeTick_safety_wit_1; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSTimeTick_safety_wit_2 : OSTimeTick_safety_wit_2.
Proof.
  unfold OSTimeTick_safety_wit_2; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSTimeTick_safety_wit_3 : OSTimeTick_safety_wit_3.
Proof.
  unfold OSTimeTick_safety_wit_3; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSTimeTick_safety_wit_4 : OSTimeTick_safety_wit_4.
Proof.
  unfold OSTimeTick_safety_wit_4; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSTimeTick_safety_wit_5 : OSTimeTick_safety_wit_5.
Proof.
  unfold OSTimeTick_safety_wit_5; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSTimeTick_safety_wit_6 : OSTimeTick_safety_wit_6.
Proof.
  unfold OSTimeTick_safety_wit_6; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSTimeTick_safety_wit_7 : OSTimeTick_safety_wit_7.
Proof.
  unfold OSTimeTick_safety_wit_7; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSTimeTick_safety_wit_8 : OSTimeTick_safety_wit_8.
Proof.
  unfold OSTimeTick_safety_wit_8; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSTimeTick_safety_wit_9 : OSTimeTick_safety_wit_9.
Proof.
  unfold OSTimeTick_safety_wit_9; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSTimeTick_safety_wit_10 : OSTimeTick_safety_wit_10.
Proof.
  unfold OSTimeTick_safety_wit_10; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSTimeTick_safety_wit_11 : OSTimeTick_safety_wit_11.
Proof.
  unfold OSTimeTick_safety_wit_11; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSTimeTick_safety_wit_12 : OSTimeTick_safety_wit_12.
Proof.
  unfold OSTimeTick_safety_wit_12; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_1 : OSTimeTick_partial_solve_wit_1.
Proof.
  unfold OSTimeTick_partial_solve_wit_1; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_2_pure : OSTimeTick_partial_solve_wit_2_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_2_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_2 : OSTimeTick_partial_solve_wit_2.
Proof.
  unfold OSTimeTick_partial_solve_wit_2, OSTimeTick_partial_solve_wit_2_aux; intros.
  rewrite PreH5.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_3_pure : OSTimeTick_partial_solve_wit_3_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_3_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_3 : OSTimeTick_partial_solve_wit_3.
Proof.
  unfold OSTimeTick_partial_solve_wit_3, OSTimeTick_partial_solve_wit_3_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_4 : OSTimeTick_partial_solve_wit_4.
Proof.
  unfold OSTimeTick_partial_solve_wit_4; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_5_pure : OSTimeTick_partial_solve_wit_5_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_5_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_5 : OSTimeTick_partial_solve_wit_5.
Proof.
  unfold OSTimeTick_partial_solve_wit_5, OSTimeTick_partial_solve_wit_5_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_6 : OSTimeTick_partial_solve_wit_6.
Proof.
  unfold OSTimeTick_partial_solve_wit_6, OSTimeTick_partial_solve_wit_6_aux; intros.
  assert (Hrem : unsigned_last_nbits (time_tick_time hook_state + 1) 32 =
    Z.rem (time_tick_time hook_state + 1) 4294967296).
  { unfold unsigned_last_nbits.
    change ((time_tick_time hook_state + 1) mod 4294967296 =
      Z.rem (time_tick_time hook_state + 1) 4294967296).
    rewrite Z.rem_mod_nonneg by lia; reflexivity. }
  rewrite Hrem; entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_7_pure : OSTimeTick_partial_solve_wit_7_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_7_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_7 : OSTimeTick_partial_solve_wit_7.
Proof.
  unfold OSTimeTick_partial_solve_wit_7, OSTimeTick_partial_solve_wit_7_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_8_pure : OSTimeTick_partial_solve_wit_8_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_8_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_8 : OSTimeTick_partial_solve_wit_8.
Proof.
  unfold OSTimeTick_partial_solve_wit_8, OSTimeTick_partial_solve_wit_8_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_9_pure : OSTimeTick_partial_solve_wit_9_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_9_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_9 : OSTimeTick_partial_solve_wit_9.
Proof.
  unfold OSTimeTick_partial_solve_wit_9, OSTimeTick_partial_solve_wit_9_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_10_pure : OSTimeTick_partial_solve_wit_10_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_10_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_10 : OSTimeTick_partial_solve_wit_10.
Proof.
  unfold OSTimeTick_partial_solve_wit_10, OSTimeTick_partial_solve_wit_10_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_11 : OSTimeTick_partial_solve_wit_11.
Proof.
  unfold OSTimeTick_partial_solve_wit_11, OSTimeTick_partial_solve_wit_11_aux; intros.
  assert (Hrunning_byte : unsigned_last_nbits (time_tick_running hook_state) 32 = 1)
    by assumption.
  rewrite time_tick_running_unsigned__traversal_and_return in Hrunning_byte.
  assert (Hrun : hook_state.(SchedState).(isRunning) = true).
  { unfold time_tick_running in Hrunning_byte.
    destruct hook_state.(SchedState).(isRunning); [reflexivity|discriminate]. }
  pose proof (time_tick_running_step_cases hook_state Hrun) as Hdecision.
  assert (Hstep : tick_step_decision hook_state.(TickState).(tickStepState) =
    (true, 0)).
  { apply time_tick_step_invalid; unfold time_tick_step in *; lia. }
  rewrite Hstep in Hdecision.
  injection Hdecision as Hprocess Hnext.
  change (time_tick_step (time_tick_clock_step_state hook_state) = 0) in Hnext.
  unfold time_tick_process_byte, time_tick_running.
  rewrite Hprocess, Hnext, Hrun; entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_12 : OSTimeTick_partial_solve_wit_12.
Proof.
  unfold OSTimeTick_partial_solve_wit_12, OSTimeTick_partial_solve_wit_12_aux; intros.
  assert (Hrunning_byte : unsigned_last_nbits (time_tick_running hook_state) 32 = 1)
    by assumption.
  rewrite time_tick_running_unsigned__traversal_and_return in Hrunning_byte.
  assert (Hrun : hook_state.(SchedState).(isRunning) = true).
  { unfold time_tick_running in Hrunning_byte.
    destruct hook_state.(SchedState).(isRunning); [reflexivity|discriminate]. }
  pose proof (time_tick_running_step_cases hook_state Hrun) as Hdecision.
  assert (Hsource_step : time_tick_step hook_state = 2) by congruence.
  unfold time_tick_step in Hsource_step.
  rewrite Hsource_step in Hdecision; cbn [tick_step_decision] in Hdecision.
  injection Hdecision as Hprocess Hnext.
  change (time_tick_step (time_tick_clock_step_state hook_state) = 1) in Hnext.
  unfold time_tick_process_byte, time_tick_running.
  rewrite Hprocess, Hnext, Hrun; entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_13 : OSTimeTick_partial_solve_wit_13.
Proof.
  unfold OSTimeTick_partial_solve_wit_13, OSTimeTick_partial_solve_wit_13_aux; intros.
  assert (Hrunning_byte : unsigned_last_nbits (time_tick_running hook_state) 32 = 1)
    by assumption.
  rewrite time_tick_running_unsigned__traversal_and_return in Hrunning_byte.
  assert (Hrun : hook_state.(SchedState).(isRunning) = true).
  { unfold time_tick_running in Hrunning_byte.
    destruct hook_state.(SchedState).(isRunning); [reflexivity|discriminate]. }
  pose proof (time_tick_running_step_cases hook_state Hrun) as Hdecision.
  assert (Hsource_step : time_tick_step hook_state = 1) by congruence.
  unfold time_tick_step in Hsource_step.
  rewrite Hsource_step in Hdecision; cbn [tick_step_decision] in Hdecision.
  injection Hdecision as Hprocess Hnext.
  change (time_tick_step (time_tick_clock_step_state hook_state) = 1) in Hnext.
  change (time_tick_step hook_state = 1) in Hsource_step.
  unfold time_tick_process_byte, time_tick_running.
  rewrite Hprocess, Hnext, Hrun, Hsource_step; entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_14 : OSTimeTick_partial_solve_wit_14.
Proof.
  unfold OSTimeTick_partial_solve_wit_14, OSTimeTick_partial_solve_wit_14_aux; intros.
  assert (Hrunning_byte : unsigned_last_nbits (time_tick_running hook_state) 32 = 1)
    by assumption.
  rewrite time_tick_running_unsigned__traversal_and_return in Hrunning_byte.
  assert (Hrun : hook_state.(SchedState).(isRunning) = true).
  { unfold time_tick_running in Hrunning_byte.
    destruct hook_state.(SchedState).(isRunning); [reflexivity|discriminate]. }
  pose proof (time_tick_running_step_cases hook_state Hrun) as Hdecision.
  assert (Hsource_step : time_tick_step hook_state = 0) by congruence.
  unfold time_tick_step in Hsource_step.
  rewrite Hsource_step in Hdecision; cbn [tick_step_decision] in Hdecision.
  injection Hdecision as Hprocess Hnext.
  change (time_tick_step (time_tick_clock_step_state hook_state) = 0) in Hnext.
  change (time_tick_step hook_state = 0) in Hsource_step.
  unfold time_tick_process_byte, time_tick_running.
  rewrite Hprocess, Hnext, Hrun, Hsource_step; entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_15_pure : OSTimeTick_partial_solve_wit_15_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_15_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_15 : OSTimeTick_partial_solve_wit_15.
Proof.
  unfold OSTimeTick_partial_solve_wit_15, OSTimeTick_partial_solve_wit_15_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_16_pure : OSTimeTick_partial_solve_wit_16_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_16_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_16 : OSTimeTick_partial_solve_wit_16.
Proof.
  unfold OSTimeTick_partial_solve_wit_16, OSTimeTick_partial_solve_wit_16_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_17_pure : OSTimeTick_partial_solve_wit_17_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_17_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_17 : OSTimeTick_partial_solve_wit_17.
Proof.
  unfold OSTimeTick_partial_solve_wit_17, OSTimeTick_partial_solve_wit_17_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_18_pure : OSTimeTick_partial_solve_wit_18_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_18_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_18 : OSTimeTick_partial_solve_wit_18.
Proof.
  unfold OSTimeTick_partial_solve_wit_18, OSTimeTick_partial_solve_wit_18_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_19_pure : OSTimeTick_partial_solve_wit_19_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_19_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_19 : OSTimeTick_partial_solve_wit_19.
Proof.
  unfold OSTimeTick_partial_solve_wit_19, OSTimeTick_partial_solve_wit_19_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_20_pure : OSTimeTick_partial_solve_wit_20_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_20_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_20 : OSTimeTick_partial_solve_wit_20.
Proof.
  unfold OSTimeTick_partial_solve_wit_20, OSTimeTick_partial_solve_wit_20_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_21_pure : OSTimeTick_partial_solve_wit_21_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_21_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_21 : OSTimeTick_partial_solve_wit_21.
Proof.
  unfold OSTimeTick_partial_solve_wit_21, OSTimeTick_partial_solve_wit_21_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_22_pure : OSTimeTick_partial_solve_wit_22_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_22_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_22 : OSTimeTick_partial_solve_wit_22.
Proof.
  unfold OSTimeTick_partial_solve_wit_22, OSTimeTick_partial_solve_wit_22_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_23_pure : OSTimeTick_partial_solve_wit_23_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_23_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_23 : OSTimeTick_partial_solve_wit_23.
Proof.
  unfold OSTimeTick_partial_solve_wit_23, OSTimeTick_partial_solve_wit_23_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_24 : OSTimeTick_partial_solve_wit_24.
Proof.
  unfold OSTimeTick_partial_solve_wit_24; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_25 : OSTimeTick_partial_solve_wit_25.
Proof.
  unfold OSTimeTick_partial_solve_wit_25; intros.
  sep_apply (UCharArray.full_split_to_missing_i (&( "OSRdyTbl" ))
    (time_tick_y node) 8 (time_tick_ready_rows current) 0 ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_26 : OSTimeTick_partial_solve_wit_26.
Proof.
  unfold OSTimeTick_partial_solve_wit_26; intros.
  sep_apply (UCharArray.full_split_to_missing_i (&( "OSRdyTbl" ))
    (time_tick_y node) 8 (time_tick_ready_rows current) 0 ltac:(lia)).
  sep_apply (store_uchar_undef_store_uchar
    ((&( "OSRdyTbl" )) + time_tick_y node * sizeof(UCHAR))
    (Znth (time_tick_y node) (time_tick_ready_rows current) 0)).
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_27 : OSTimeTick_partial_solve_wit_27.
Proof.
  unfold OSTimeTick_partial_solve_wit_27; intros.
  sep_apply (UCharArray.full_split_to_missing_i (&( "OSRdyTbl" ))
    (time_tick_y node) 8 (time_tick_ready_rows current) 0 ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_28 : OSTimeTick_partial_solve_wit_28.
Proof.
  unfold OSTimeTick_partial_solve_wit_28; intros.
  sep_apply (UCharArray.full_split_to_missing_i (&( "OSRdyTbl" ))
    (time_tick_y node) 8 (time_tick_ready_rows current) 0 ltac:(lia)).
  sep_apply (store_uchar_undef_store_uchar
    ((&( "OSRdyTbl" )) + time_tick_y node * sizeof(UCHAR))
    (Znth (time_tick_y node) (time_tick_ready_rows current) 0)).
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_29_pure : OSTimeTick_partial_solve_wit_29_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_29_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_29 : OSTimeTick_partial_solve_wit_29.
Proof.
  unfold OSTimeTick_partial_solve_wit_29, OSTimeTick_partial_solve_wit_29_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_30_pure : OSTimeTick_partial_solve_wit_30_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_30_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_30 : OSTimeTick_partial_solve_wit_30.
Proof.
  unfold OSTimeTick_partial_solve_wit_30, OSTimeTick_partial_solve_wit_30_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_31_pure : OSTimeTick_partial_solve_wit_31_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_31_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_31 : OSTimeTick_partial_solve_wit_31.
Proof.
  unfold OSTimeTick_partial_solve_wit_31, OSTimeTick_partial_solve_wit_31_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_32_pure : OSTimeTick_partial_solve_wit_32_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_32_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_32 : OSTimeTick_partial_solve_wit_32.
Proof.
  unfold OSTimeTick_partial_solve_wit_32, OSTimeTick_partial_solve_wit_32_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_33_pure : OSTimeTick_partial_solve_wit_33_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_33_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_33 : OSTimeTick_partial_solve_wit_33.
Proof.
  unfold OSTimeTick_partial_solve_wit_33, OSTimeTick_partial_solve_wit_33_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_34_pure : OSTimeTick_partial_solve_wit_34_pure.
Proof.
  unfold OSTimeTick_partial_solve_wit_34_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSTimeTick_partial_solve_wit_34 : OSTimeTick_partial_solve_wit_34.
Proof.
  unfold OSTimeTick_partial_solve_wit_34, OSTimeTick_partial_solve_wit_34_aux; intros.
  entailer!.
Qed.
