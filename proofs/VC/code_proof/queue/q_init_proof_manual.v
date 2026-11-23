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
From Ucos2Verify.VC.code.queue Require Import q_init_goal.
From Ucos2Verify.VC.code.queue Require Import q_init_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.VC.code.queue.spec.q_init_spec.
Local Open Scope sac.

Lemma proof_of_OS_QInit_entail_wit_1 : OS_QInit_entail_wit_1.
Proof.
  unfold OS_QInit_entail_wit_1.
  right.
  intros.
  unfold q_init_after_clear, q_init_loop_state,
    queue_table_zero, queue_all_ids.
  pre_process.
  entailer!.
  pose proof (q_init_profile_q_count sg PreH5) as Hcount.
  lia.
Qed.

Lemma proof_of_OS_QInit_entail_wit_2 : OS_QInit_entail_wit_2.
Proof.
  unfold OS_QInit_entail_wit_2.
  right.
  intros.
  unfold q_init_loop_residual, q_init_link_committed,
    q_init_zero_linked_node.
  pre_process.
  entailer!.
  - unfold queue_control_block_layout_prop in PreH6.
    destruct PreH6 as [Hptr _].
    rewrite <- Hptr.
    unfold qcb_addr.
    unfold os_q_table_addr in PreH3.
    destruct PreH2 as [_ Hsize].
    rewrite <- PreH3, <- Hsize.
    reflexivity.
  - pose proof (q_init_profile_q_count sg PreH9) as Hcount.
    assert (Hupper : ix < 4) by (rewrite <- Hcount; exact (proj2 H)).
    rewrite unsigned_last_nbits_eq in PreH7 by (cbn; lia).
    rewrite Hcount.
    lia.
Qed.

Lemma proof_of_OS_QInit_entail_wit_3 : OS_QInit_entail_wit_3.
Proof.
  unfold OS_QInit_entail_wit_3.
  right.
  intros.
  unfold q_init_link_committed, q_init_loop_state.
  pre_process.
  pose proof (q_init_profile_q_count sg PreH2) as Hcount.
  assert (ix = 0 \/ ix = 1 \/ ix = 2) as Hcases by lia.
  destruct Hcases as [-> | [-> | ->]].
  all: rewrite unsigned_last_nbits_eq by (cbn; lia).
  all: rewrite Hcount.
  - replace (ZRange.Zrange 0 0) with (@nil Z) by reflexivity.
    replace (ZRange.Zrange 0 (0 + 1)) with (0 :: nil) by reflexivity.
    cbn [q_init_linked_prefix].
    entailer!.
  - replace (ZRange.Zrange 0 1) with (0 :: nil) by reflexivity.
    replace (ZRange.Zrange 0 (1 + 1)) with (0 :: 1 :: nil) by reflexivity.
    cbn [q_init_linked_prefix].
    entailer!.
  - replace (ZRange.Zrange 0 2) with (0 :: 1 :: nil) by reflexivity.
    replace (ZRange.Zrange 0 (2 + 1)) with (0 :: 1 :: 2 :: nil) by reflexivity.
    cbn [q_init_linked_prefix].
    entailer!.
Qed.

Lemma proof_of_OS_QInit_entail_wit_4 : OS_QInit_entail_wit_4.
Proof.
  unfold OS_QInit_entail_wit_4.
  right.
  intros.
  subst ix.
  unfold q_init_last_link_residual, q_init_before_publish,
    q_init_zero_linked_node.
  pre_process.
  entailer!.
  unfold queue_control_block_layout_prop in PreH7.
  destruct PreH7 as [Hptr _].
  pose proof (q_init_profile_q_count sg PreH2) as Hcount.
  rewrite Hcount.
  replace (4 - 1) with 3 by lia.
  rewrite <- Hptr.
  reflexivity.
Qed.

Lemma proof_of_OS_QInit_return_wit_1 : OS_QInit_return_wit_1.
Proof.
  unfold OS_QInit_return_wit_1.
  right.
  intros.
  pose proof (queue_all_ids_valid sg) as Hvalid_ids.
  pose proof (q_init_profile_all_ids sg PreH7) as Hall.
  unfold OS_QInit_spec, store_q_init_zero_linked_list.
  rewrite Hall.
  unfold q_init_publish_residual.
  pose proof (q_init_profile_q_count sg PreH7) as Hcount.
  rewrite Hcount.
  replace (4 - 1) with 3 by lia.
  replace (ZRange.Zrange 0 3) with (0 :: 1 :: 2 :: nil) by reflexivity.
  cbn [q_init_linked_prefix store_q_init_zero_linked_nodes queue_free_head].
  pre_process.
  entailer!.
  - unfold os_q_free_list_addr in PreH9.
    unfold os_q_table_addr in PreH8.
    unfold qcb_addr.
    rewrite <- PreH9, <- PreH8.
    entailer!.
  - rewrite <- Hall.
    exact Hvalid_ids.
Qed.

Lemma proof_of_OS_QInit_partial_solve_wit_1_pure : OS_QInit_partial_solve_wit_1_pure.
Proof.
  unfold OS_QInit_partial_solve_wit_1_pure.
  right.
  intros.
  pre_process.
  entailer!.
  all: replace (&( "OSQTbl") + 0 * sizeof ("os_q")) with (&( "OSQTbl")) by lia;
    assumption.
Qed.

Lemma proof_of_OS_QInit_partial_solve_wit_2_pure : OS_QInit_partial_solve_wit_2_pure.
Proof.
  unfold OS_QInit_partial_solve_wit_2_pure.
  right.
  intros.
  unfold q_init_loop_state.
  pre_process.
  entailer!.
  all: pose proof (q_init_profile_q_count sg PreH3) as Hcount;
    rewrite (unsigned_last_nbits_eq ix 32) by (cbn; lia);
    rewrite (unsigned_last_nbits_eq (ix + 1) 16) by (cbn; lia);
    reflexivity.
Qed.

Lemma proof_of_OS_QInit_partial_solve_wit_3_pure : OS_QInit_partial_solve_wit_3_pure.
Proof.
  unfold OS_QInit_partial_solve_wit_3_pure.
  right.
  intros.
  unfold q_init_loop_state.
  pre_process.
  entailer!.
  pose proof (q_init_profile_q_count sg PreH3) as Hcount.
  rewrite unsigned_last_nbits_eq in PreH1 by (cbn; lia).
  lia.
Qed.

Lemma proof_of_OS_QInit_which_implies_wit_1 : OS_QInit_which_implies_wit_1.
Proof.
  unfold OS_QInit_which_implies_wit_1.
  right.
  intros.
  subst ix_next.
  subst pq1.
  subst pq2.
  unfold q_init_loop_state, q_init_loop_residual,
    zero_queue_control_block, q_init_zero_node_without_ptr.
  pre_process.
  pose proof (q_init_profile_q_count sg PreH2) as Hcount.
  assert (Hrange : 0 <= ix < osMaxQs sg) by lia.
  pose proof (queue_table_layout_select sg &("OSQTbl") ix PreH5 Hrange)
    as Hlayout.
  entailer!.
  unfold queue_control_block_layout_prop in Hlayout.
  destruct Hlayout as [Hptr _].
  assert (ix = 0 \/ ix = 1 \/ ix = 2 \/ ix = 3) as Hcases by lia.
  destruct Hcases as [-> | [-> | [-> | ->]]].
  all: rewrite Hcount.
  - replace (ZRange.Zrange 0 4) with (0 :: 1 :: 2 :: 3 :: nil) by reflexivity.
    replace (ZRange.Zrange (0 + 1) 4) with (1 :: 2 :: 3 :: nil) by reflexivity.
    cbn [store_zero_queue_nodes zero_queue_control_block].
    rewrite Hptr.
    entailer!.
    unfold zero_queue_control_block.
    entailer!.
  - replace (ZRange.Zrange 1 4) with (1 :: 2 :: 3 :: nil) by reflexivity.
    replace (ZRange.Zrange (1 + 1) 4) with (2 :: 3 :: nil) by reflexivity.
    cbn [store_zero_queue_nodes zero_queue_control_block].
    rewrite Hptr.
    entailer!.
    unfold zero_queue_control_block.
    entailer!.
  - replace (ZRange.Zrange 2 4) with (2 :: 3 :: nil) by reflexivity.
    replace (ZRange.Zrange (2 + 1) 4) with (3 :: nil) by reflexivity.
    cbn [store_zero_queue_nodes zero_queue_control_block].
    rewrite Hptr.
    entailer!.
    unfold zero_queue_control_block.
    entailer!.
  - replace (ZRange.Zrange 3 4) with (3 :: nil) by reflexivity.
    replace (ZRange.Zrange (3 + 1) 4) with (@nil Z) by reflexivity.
    cbn [store_zero_queue_nodes zero_queue_control_block].
    rewrite Hptr.
    entailer!.
    unfold zero_queue_control_block.
    entailer!.
Qed.

Lemma proof_of_OS_QInit_which_implies_wit_2 : OS_QInit_which_implies_wit_2.
Proof.
  unfold OS_QInit_which_implies_wit_2.
  right.
  intros.
  unfold q_init_loop_state, q_init_last_link_residual,
    q_init_zero_node_without_ptr.
  pre_process.
  pose proof (q_init_profile_q_count sg PreH2) as Hcount.
  assert (ix = 3) as Hix by lia.
  subst ix.
  assert (Hrange : 0 <= 3 < osMaxQs sg) by lia.
  pose proof (queue_table_layout_select sg &("OSQTbl") 3 PreH5 Hrange)
    as Hlayout.
  entailer!.
  unfold queue_control_block_layout_prop in Hlayout.
  destruct Hlayout as [Hptr _].
  rewrite Hcount.
  replace (4 - 1) with 3 by lia.
  replace (ZRange.Zrange 3 4) with (3 :: nil) by reflexivity.
  cbn [store_zero_queue_nodes].
  rewrite Hptr.
  entailer!.
  unfold zero_queue_control_block.
  entailer!.
Qed.

Lemma proof_of_OS_QInit_which_implies_wit_3 : OS_QInit_which_implies_wit_3.
Proof.
  unfold OS_QInit_which_implies_wit_3.
  left.
  intros.
  unfold q_init_before_publish, q_init_publish_residual.
  pre_process.
  entailer!.
  unfold os_q_free_list_addr in PreH4.
  rewrite PreH4.
  reflexivity.
Qed.
