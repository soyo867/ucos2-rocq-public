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
From Ucos2Verify.VC.code.tick Require Import time_tick_sem_goal.
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
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_sem_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.

Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.error_codes.

Lemma proof_of_OSSemPost_safety_wit_1 : OSSemPost_safety_wit_1.
Proof.
  unfold OSSemPost_safety_wit_1; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSSemPost_safety_wit_2 : OSSemPost_safety_wit_2.
Proof.
  unfold OSSemPost_safety_wit_2; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSSemPost_safety_wit_3 : OSSemPost_safety_wit_3.
Proof.
  unfold OSSemPost_safety_wit_3; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSSemPost_safety_wit_4 : OSSemPost_safety_wit_4.
Proof.
  unfold OSSemPost_safety_wit_4; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSSemPost_safety_wit_5 : OSSemPost_safety_wit_5.
Proof.
  unfold OSSemPost_safety_wit_5; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSSemPost_safety_wit_6 : OSSemPost_safety_wit_6.
Proof.
  unfold OSSemPost_safety_wit_6; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSSemPost_return_wit_3 : OSSemPost_return_wit_3.
Proof.
  unfold OSSemPost_return_wit_3; intros.
  match goal with Hresult : time_tick_sem_result sg pe before 0 ?after |- _ => Exists after end.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_1 : OSSemPost_partial_solve_wit_1.
Proof.
  unfold OSSemPost_partial_solve_wit_1; intros.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_2_pure : OSSemPost_partial_solve_wit_2_pure.
Proof.
  unfold OSSemPost_partial_solve_wit_2_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_2 : OSSemPost_partial_solve_wit_2.
Proof.
  unfold OSSemPost_partial_solve_wit_2, OSSemPost_partial_solve_wit_2_aux; intros.
  rewrite PreH3; entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_3_pure : OSSemPost_partial_solve_wit_3_pure.
Proof.
  unfold OSSemPost_partial_solve_wit_3_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_3 : OSSemPost_partial_solve_wit_3.
Proof.
  unfold OSSemPost_partial_solve_wit_3, OSSemPost_partial_solve_wit_3_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_4_pure : OSSemPost_partial_solve_wit_4_pure.
Proof.
  unfold OSSemPost_partial_solve_wit_4_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_4 : OSSemPost_partial_solve_wit_4.
Proof.
  unfold OSSemPost_partial_solve_wit_4, OSSemPost_partial_solve_wit_4_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_5 : OSSemPost_partial_solve_wit_5.
Proof.
  unfold OSSemPost_partial_solve_wit_5; intros.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_6_pure : OSSemPost_partial_solve_wit_6_pure.
Proof.
  unfold OSSemPost_partial_solve_wit_6_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_6 : OSSemPost_partial_solve_wit_6.
Proof.
  unfold OSSemPost_partial_solve_wit_6, OSSemPost_partial_solve_wit_6_aux; intros.
  match goal with Hpointer : pe = event_addr sg eid |- _ => rewrite Hpointer in * end.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_7 : OSSemPost_partial_solve_wit_7.
Proof.
  unfold OSSemPost_partial_solve_wit_7, OSSemPost_partial_solve_wit_7_aux; intros.
  assert (Hnonzero : sem_post_group before node <> 0).
  { intro Hz; rewrite Hz in PreH1; contradiction PreH1; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_8 : OSSemPost_partial_solve_wit_8.
Proof.
  unfold OSSemPost_partial_solve_wit_8, OSSemPost_partial_solve_wit_8_aux; intros.
  match goal with Haddr : time_tick_internal_addresses sg _ _ _ _ _ |- _ =>
    destruct Haddr as [Hint [Hprio [Hunmap [Hgroup Hrows]]]]
  end; unfold time_tick_internal_addresses; entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_9_pure : OSSemPost_partial_solve_wit_9_pure.
Proof.
  unfold OSSemPost_partial_solve_wit_9_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_9 : OSSemPost_partial_solve_wit_9.
Proof.
  unfold OSSemPost_partial_solve_wit_9, OSSemPost_partial_solve_wit_9_aux; intros.
  match goal with Hpointer : pe = event_addr sg eid |- _ => rewrite Hpointer in * end.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_10_pure : OSSemPost_partial_solve_wit_10_pure.
Proof.
  unfold OSSemPost_partial_solve_wit_10_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_10 : OSSemPost_partial_solve_wit_10.
Proof.
  unfold OSSemPost_partial_solve_wit_10, OSSemPost_partial_solve_wit_10_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_11_pure : OSSemPost_partial_solve_wit_11_pure.
Proof.
  unfold OSSemPost_partial_solve_wit_11_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_11 : OSSemPost_partial_solve_wit_11.
Proof.
  unfold OSSemPost_partial_solve_wit_11, OSSemPost_partial_solve_wit_11_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_12 : OSSemPost_partial_solve_wit_12.
Proof.
  unfold OSSemPost_partial_solve_wit_12, OSSemPost_partial_solve_wit_12_aux; intros.
  match goal with Haddr : time_tick_internal_addresses sg _ _ _ _ _ |- _ =>
    destruct Haddr as [Hint [Hprio [Hunmap [Hgroup Hrows]]]]
  end; unfold time_tick_internal_addresses; entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_13 : OSSemPost_partial_solve_wit_13.
Proof.
  unfold OSSemPost_partial_solve_wit_13, OSSemPost_partial_solve_wit_13_aux; intros.
  prop_apply_p (store_uchar_range
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp")) (sem_post_group before node)).
  Intros.
  match goal with Hrange : 0 <= sem_post_group before node <= Byte.max_unsigned |- _ =>
    change (0 <= sem_post_group before node <= 255) in Hrange end.
  pose proof PreH1 as Hzero.
  rewrite unsigned_last_nbits_eq in Hzero by
    (change (0 <= sem_post_group before node < 4294967296); lia).
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_14_pure : OSSemPost_partial_solve_wit_14_pure.
Proof.
  unfold OSSemPost_partial_solve_wit_14_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_14 : OSSemPost_partial_solve_wit_14.
Proof.
  unfold OSSemPost_partial_solve_wit_14, OSSemPost_partial_solve_wit_14_aux; intros.
  match goal with Hpointer : pe = event_addr sg eid |- _ => rewrite Hpointer in * end.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_15_pure : OSSemPost_partial_solve_wit_15_pure.
Proof.
  unfold OSSemPost_partial_solve_wit_15_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_15 : OSSemPost_partial_solve_wit_15.
Proof.
  unfold OSSemPost_partial_solve_wit_15, OSSemPost_partial_solve_wit_15_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_16_pure : OSSemPost_partial_solve_wit_16_pure.
Proof.
  unfold OSSemPost_partial_solve_wit_16_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_16 : OSSemPost_partial_solve_wit_16.
Proof.
  unfold OSSemPost_partial_solve_wit_16, OSSemPost_partial_solve_wit_16_aux; intros.
  match goal with Hpointer : pe = event_addr sg eid |- _ => rewrite Hpointer in * end.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_17_pure : OSSemPost_partial_solve_wit_17_pure.
Proof.
  unfold OSSemPost_partial_solve_wit_17_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_17 : OSSemPost_partial_solve_wit_17.
Proof.
  unfold OSSemPost_partial_solve_wit_17, OSSemPost_partial_solve_wit_17_aux; intros.
  entailer!.
Qed.
