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
From Ucos2Verify.VC.code.flag Require Import flag_task_rdy_fields_goal.
From Ucos2Verify.VC.code.flag Require Import flag_task_rdy_fields_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_fields_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope sac_scope.
Local Open Scope sac.

Lemma proof_of_OS_FlagTaskRdy_entail_wit_1 : OS_FlagTaskRdy_entail_wit_1.
Proof.
  right; intros.
  rewrite flag_task_rdy_status_cast_eq; entailer!.
Qed.

Lemma proof_of_OS_FlagTaskRdy_entail_wit_2 : OS_FlagTaskRdy_entail_wit_2.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range (&("OSRdyGrp")) (flag_task_rdy_ready_group s)).
  Intros.
  prop_apply_p (store_uchar_range
    (&("OSRdyTbl") + tcb_y_of_prio old.(curPrio) * sizeof(UCHAR))
    (flag_task_rdy_ready_row s old)).
  Intros.
  change (0 <= flag_task_rdy_ready_group s <= 255) in H.
  change (0 <= flag_task_rdy_ready_row s old <= 255) in H0.
  entailer!.
Qed.

Lemma proof_of_OS_FlagTaskRdy_entail_wit_3_1 : OS_FlagTaskRdy_entail_wit_3_1.
Proof.
  right; intros.
  rewrite flag_task_rdy_return_zero_status by assumption; entailer!.
Qed.

Lemma proof_of_OS_FlagTaskRdy_entail_wit_3_2 : OS_FlagTaskRdy_entail_wit_3_2.
Proof.
  right; intros.
  rewrite flag_task_rdy_return_nonzero_status by assumption; entailer!.
Qed.

Lemma proof_of_OS_FlagTaskRdy_partial_solve_wit_6_pure : OS_FlagTaskRdy_partial_solve_wit_6_pure.
Proof.
  right; intros.
  pose proof (flag_task_rdy_status_in_range old) as Hstatus.
  rewrite unsigned_last_nbits_eq in PreH8 by (change (0 <= flag_task_rdy_status old < 4294967296); lia).
  pose proof (bitmap_single_bit_in_range 8 (tcb_y_of_prio old.(curPrio))
    ltac:(split; assumption)) as HbitY.
  pose proof (bitmap_single_bit_in_range 8 (tcb_x_of_prio old.(curPrio))
    ltac:(unfold tcb_x_of_prio; apply Z.mod_pos_bound; lia)) as HbitX.
  change (0 <= tcb_bit_y_of_prio old.(curPrio) < 2 ^ 8) in HbitY.
  change (0 <= tcb_bit_x_of_prio old.(curPrio) < 2 ^ 8) in HbitX.
  rewrite (unsigned_last_nbits_eq _ 8 HbitY), (unsigned_last_nbits_eq _ 8 HbitX).
  entailer!.
Qed.

Lemma proof_of_OS_FlagTaskRdy_partial_solve_wit_7_pure : OS_FlagTaskRdy_partial_solve_wit_7_pure.
Proof.
  right; intros.
  pose proof (flag_task_rdy_status_in_range old) as Hstatus.
  rewrite unsigned_last_nbits_eq in PreH1 by (change (0 <= flag_task_rdy_status old < 4294967296); lia).
  entailer!.
Qed.

Lemma proof_of_OS_FlagTaskRdy_which_implies_wit_1 : OS_FlagTaskRdy_which_implies_wit_1.
Proof.
  left; intros bits old w p s sg.
  unfold flag_task_rdy_fields_pre, flag_task_rdy_fields_resources; Intros.
  pose proof H as [_ [[Hcfg _] [Hlookup _]]].
  sep_apply_l_atomic (task_public_storage_split_task sg s.(TskState)
    w.(flagTask) old Hlookup).
  rewrite (flag_task_rdy_task_rep_equiv sg w old Hcfg).
  entailer!.
Qed.

Lemma proof_of_OS_FlagTaskRdy_which_implies_wit_2 : OS_FlagTaskRdy_which_implies_wit_2.
Proof.
  left; intros bits old w p s sg Hdomain.
  pose proof Hdomain as [Hlayout [[_ [_ [Hlookup _]]] _]].
  sep_apply_l_atomic (flag_task_rdy_fields_node_split_tcb sg s.(FlagState) p w
    Hlayout Hlookup).
  entailer!.
Qed.

Lemma proof_of_OS_FlagTaskRdy_which_implies_wit_3 : OS_FlagTaskRdy_which_implies_wit_3.
Proof.
  left; intros bits old w p s sg Hdomain.
  pose proof Hdomain as [Hlayout [[_ [_ [Hlookup _]]] _]].
  sep_apply_l_atomic (flag_task_rdy_fields_node_merge_tcb sg s.(FlagState) p w
    Hlayout Hlookup).
  entailer!.
Qed.

Lemma proof_of_OS_FlagTaskRdy_which_implies_wit_4 : OS_FlagTaskRdy_which_implies_wit_4.
Proof.
  left; intros bits old w p s sg Hdomain.
  pose proof Hdomain as [_ [Hu [_ [Hprio _]]]].
  pose proof Hu as [_ [_ [_ [_ [_ [_ [Haddr _]]]]]]].
  assert (Hy : 0 <= tcb_y_of_prio old.(curPrio) < 8).
  { unfold tcb_y_of_prio; split;
      [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
  unfold flag_unlink_task_rep; rewrite <- Haddr.
  pose proof (flag_task_rdy_tcb_split (flag_unlink_tcb_addr w)
    (task_tcb64_image sg old)) as Hsplit.
  cbn [tcb_cell tcb_field_address task_tcb64_image] in Hsplit.
  sep_apply_l_atomic Hsplit; entailer!.
Qed.

Lemma proof_of_OS_FlagTaskRdy_which_implies_wit_5 : OS_FlagTaskRdy_which_implies_wit_5.
Proof.
  right; intros.
  rewrite PreH2, PreH3.
  apply flag_task_rdy_ready_split.
  destruct PreH1 as [_ [_ [_ [Hprio _]]]]; exact Hprio.
Qed.

Lemma proof_of_OS_FlagTaskRdy_which_implies_wit_6 : OS_FlagTaskRdy_which_implies_wit_6.
Proof.
  right; intros.
  rewrite PreH3, PreH4.
  destruct PreH1 as [_ [_ [Hlookup [Hprio _]]]].
  apply flag_task_rdy_ready_merge_written; assumption.
Qed.

Lemma proof_of_OS_FlagTaskRdy_which_implies_wit_7 : OS_FlagTaskRdy_which_implies_wit_7.
Proof.
  right; intros.
  destruct PreH1 as [_ [_ [Hlookup _]]].
  rewrite flag_task_rdy_ready_unchanged_eq by assumption; entailer!.
Qed.

Lemma proof_of_OS_FlagTaskRdy_which_implies_wit_8 : OS_FlagTaskRdy_which_implies_wit_8.
Proof.
  left; intros result bits old w p s sg Hdomain.
  pose proof Hdomain as [_ [Hu _]].
  pose proof Hu as [_ [_ [_ [_ [_ [_ [Haddr _]]]]]]].
  unfold flag_unlink_task_rep; rewrite <- Haddr.
  pose proof (flag_task_rdy_tcb_merge_middle sg old (flag_unlink_tcb_addr w)
    bits result) as Hmerge.
  cbn [tcb_cell tcb_field_address] in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma proof_of_OS_FlagTaskRdy_which_implies_wit_9 : OS_FlagTaskRdy_which_implies_wit_9.
Proof.
  left; intros result bits old w p s sg Hdomain.
  pose proof (flag_task_rdy_middle_unlink_domain sg s p w old bits result Hdomain)
    as Hmiddle.
  pose proof Hdomain as [Hlayout _].
  unfold flag_unlink_fields_pre; entailer!.
Qed.

Lemma proof_of_OS_FlagTaskRdy_which_implies_wit_10 : OS_FlagTaskRdy_which_implies_wit_10.
Proof.
  left; intros; unfold flag_task_rdy_call_frame; entailer!.
Qed.

Lemma proof_of_OS_FlagTaskRdy_which_implies_wit_11 : OS_FlagTaskRdy_which_implies_wit_11.
Proof.
  left; intros F result bits old w p s sg Hdomain.
  exact (flag_task_rdy_fields_unlink_finish sg s p w old bits result F Hdomain).
Qed.

