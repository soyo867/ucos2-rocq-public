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

Lemma proof_of_OSSemPost_return_wit_1 : OSSemPost_return_wit_1.
Proof.
  unfold OSSemPost_return_wit_1; left; intros.
  Exists before; unfold time_tick_sched_owned; entailer!.
Qed.

Lemma proof_of_OSSemPost_return_wit_2 : OSSemPost_return_wit_2.
Proof.
  unfold OSSemPost_return_wit_2; left; intros.
  Exists (sem_post_count_checkpoint before eid node); unfold time_tick_sched_owned; entailer!.
Qed.

Lemma proof_of_OSSemPost_return_wit_4 : OSSemPost_return_wit_4.
Proof.
  unfold OSSemPost_return_wit_4; left; intros.
  Exists before; unfold time_tick_sched_owned; entailer!.
Qed.

Lemma proof_of_OSSemPost_return_wit_5 : OSSemPost_return_wit_5.
Proof.
  unfold OSSemPost_return_wit_5; left; intros.
  assert (Hpe : pe = 0) by congruence; rewrite Hpe in *.
  pose proof (time_tick_sem_null_result sg before PreH3) as Hresult.
  Exists before; entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_7_pure : OSSemPost_partial_solve_wit_7_pure.
Proof.
  unfold OSSemPost_partial_solve_wit_7_pure; left; intros.
  assert (Hnonzero : sem_post_group before node <> 0).
  { intro Hz; rewrite Hz in PreH1; contradiction PreH1; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_8_pure : OSSemPost_partial_solve_wit_8_pure.
Proof.
  unfold OSSemPost_partial_solve_wit_8_pure; left; intros.
  match goal with Haddr : time_tick_internal_addresses sg _ _ _ _ _ |- _ =>
    destruct Haddr as [Hint [Hprio [Hunmap [Hgroup Hrows]]]]
  end; entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_12_pure : OSSemPost_partial_solve_wit_12_pure.
Proof.
  unfold OSSemPost_partial_solve_wit_12_pure; left; intros.
  match goal with Haddr : time_tick_internal_addresses sg _ _ _ _ _ |- _ =>
    destruct Haddr as [Hint [Hprio [Hunmap [Hgroup Hrows]]]]
  end; entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_13_pure : OSSemPost_partial_solve_wit_13_pure.
Proof.
  unfold OSSemPost_partial_solve_wit_13_pure; left; intros.
  prop_apply_p (store_uchar_range
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp")) (sem_post_group before node)).
  Intros.
  match goal with Hrange : 0 <= sem_post_group before node <= Byte.max_unsigned |- _ =>
    change (0 <= sem_post_group before node <= 255) in Hrange end.
  rewrite unsigned_last_nbits_eq in PreH1 by
    (change (0 <= sem_post_group before node < 4294967296); lia).
  entailer!.
Qed.

Lemma proof_of_OSSemPost_which_implies_wit_1 : OSSemPost_which_implies_wit_1.
Proof.
  unfold OSSemPost_which_implies_wit_1; left; intros.
  unfold time_tick_sched_owned, UCOS2_inv; entailer!.
Qed.

Lemma proof_of_OSSemPost_which_implies_wit_2 : OSSemPost_which_implies_wit_2.
Proof.
  unfold OSSemPost_which_implies_wit_2; left; intros.
  destruct (time_tick_sem_readable_nonnull sg before pe PreH4 PreH2 PreH1)
    as [eid [node [Hpointer [Hrange Hlookup]]]].
  pose proof (event_table_layout_select sg eid PreH3 Hrange) as Hlayout.
  pose proof (time_tick_sem_type_range node) as Htype.
  Exists node eid; rewrite Hpointer, (proj1 (proj1 Hlayout)).
  sep_apply (time_tick_sem_type_split sg before eid node Hlookup); entailer!.
Qed.

Lemma proof_of_OSSemPost_which_implies_wit_3 : OSSemPost_which_implies_wit_3.
Proof.
  unfold OSSemPost_which_implies_wit_3; left; intros.
  pose proof (time_tick_sem_type_error_result sg pe before eid node PreH1 PreH2 PreH5 PreH6) as Hresult.
  rewrite PreH2 in *; rewrite (proj1 (proj1 PreH3)).
  sep_apply (time_tick_sem_type_merge sg before eid node PreH4 PreH5); entailer!.
Qed.

Lemma proof_of_OSSemPost_which_implies_wit_4 : OSSemPost_which_implies_wit_4.
Proof.
  unfold OSSemPost_which_implies_wit_4; left; intros.
  rewrite PreH2, (proj1 (proj1 PreH3)).
  sep_apply (time_tick_sem_type_merge sg before eid node PreH4 PreH5); entailer!.
Qed.

Lemma proof_of_OSSemPost_which_implies_wit_5 : OSSemPost_which_implies_wit_5.
Proof.
  unfold OSSemPost_which_implies_wit_5; left; intros.
  rewrite PreH1, (proj1 (proj2 PreH2)).
  sep_apply (time_tick_sem_group_split sg before eid node PreH3); entailer!.
Qed.

Lemma proof_of_OSSemPost_which_implies_wit_6 : OSSemPost_which_implies_wit_6.
Proof.
  unfold OSSemPost_which_implies_wit_6; left; intros.
  pose proof (time_tick_sem_type_is_sem node PreH5) as Htype.
  rewrite PreH1, (proj1 (proj2 PreH2)).
  sep_apply (time_tick_sem_group_merge sg before eid node PreH3 PreH4).
  sep_apply (sem_post_wake_split_full sg before eid node PreH3 PreH4 Htype PreH6 PreH2).
  Intros tid old; Exists tid old.
  unfold time_tick_sem_ready_group, time_tick_sem_ready_rows; entailer!.
Qed.

Lemma proof_of_OSSemPost_which_implies_wit_7 : OSSemPost_which_implies_wit_7.
Proof.
  unfold OSSemPost_which_implies_wit_7; left; intros.
  pose proof (time_tick_sem_type_is_sem node PreH3) as Htype.
  unfold time_tick_sem_ready_group, time_tick_sem_ready_rows.
  sep_apply (sem_post_wake_merge_full sg before eid node tid old priority PreH1 PreH2 Htype PreH7).
  Intros after.
  match goal with Hwake : sem_post_wake_result sg eid before after priority |- _ =>
    pose proof (sem_post_wake_result_critical sg eid before node after priority PreH2 PreH4 Hwake) as Hcritical
  end.
  pose proof (time_tick_sem_critical_result sg pe before eid node (OS_ERR_NONE, true) after
    PreH5 PreH6 PreH2 Htype Hcritical) as Hresult.
  change (time_tick_sem_result sg pe before 0 after) in Hresult.
  pose proof (time_tick_sem_result_interrupts sg pe before 0 after PreH1 Hresult) as Hinterrupt.
  Exists after; entailer!.
Qed.

Lemma proof_of_OSSemPost_which_implies_wit_8 : OSSemPost_which_implies_wit_8.
Proof.
  unfold OSSemPost_which_implies_wit_8; left; intros.
  unfold time_tick_sched_owned; entailer!; lia.
Qed.

Lemma proof_of_OSSemPost_which_implies_wit_9 : OSSemPost_which_implies_wit_9.
Proof.
  unfold OSSemPost_which_implies_wit_9; left; intros.
  pose proof (time_tick_sem_type_is_sem node PreH5) as Htype.
  rewrite PreH1, (proj1 (proj2 PreH2)), (proj2 (proj2 (proj1 PreH2))).
  sep_apply (time_tick_sem_group_merge sg before eid node PreH3 PreH4).
  sep_apply (sem_post_count_split_full sg before eid node PreH4 Htype); entailer!.
Qed.

Lemma proof_of_OSSemPost_which_implies_wit_10 : OSSemPost_which_implies_wit_10.
Proof.
  unfold OSSemPost_which_implies_wit_10; left; intros.
  pose proof (time_tick_sem_type_is_sem node PreH6) as Htype.
  assert (Htest : Z.ltb (encode_event_cnt_value node) 65535 = true) by (apply Z.ltb_lt; lia).
  pose proof (sem_post_count_checkpoint_critical sg before eid node PreH4 PreH5 Htype PreH7) as Hcritical.
  unfold sem_post_count_error in Hcritical; rewrite Htest in Hcritical.
  pose proof (time_tick_sem_critical_result sg pe before eid node (OS_ERR_NONE, false)
    (sem_post_count_checkpoint before eid node) PreH1 PreH2 PreH5 Htype Hcritical) as Hresult.
  change (time_tick_sem_result sg pe before 0 (sem_post_count_checkpoint before eid node)) in Hresult.
  pose proof (sem_post_count_merge_checkpoint sg before eid node PreH4 PreH5 Htype PreH7) as Hmerge.
  unfold sem_post_stored_count in Hmerge; rewrite Htest in Hmerge.
  rewrite PreH2 in *; rewrite (proj2 (proj2 (proj1 PreH3))).
  sep_apply Hmerge; entailer!.
Qed.

Lemma proof_of_OSSemPost_which_implies_wit_11 : OSSemPost_which_implies_wit_11.
Proof.
  unfold OSSemPost_which_implies_wit_11; left; intros.
  pose proof (time_tick_sem_type_is_sem node PreH6) as Htype.
  assert (Htest : Z.ltb (encode_event_cnt_value node) 65535 = false) by (apply Z.ltb_ge; lia).
  pose proof (sem_post_count_checkpoint_critical sg before eid node PreH4 PreH5 Htype PreH7) as Hcritical.
  unfold sem_post_count_error, sem_post_count_checkpoint in Hcritical; rewrite Htest in Hcritical.
  pose proof (time_tick_sem_critical_result sg pe before eid node (OS_ERR_SEM_OVF, false)
    before PreH1 PreH2 PreH5 Htype Hcritical) as Hresult.
  change (time_tick_sem_result sg pe before 51 before) in Hresult.
  pose proof (sem_post_count_merge_checkpoint sg before eid node PreH4 PreH5 Htype PreH7) as Hmerge.
  unfold sem_post_stored_count, sem_post_count_checkpoint in Hmerge; rewrite Htest in Hmerge.
  rewrite PreH2 in *; rewrite (proj2 (proj2 (proj1 PreH3))).
  sep_apply Hmerge; entailer!.
Qed.
