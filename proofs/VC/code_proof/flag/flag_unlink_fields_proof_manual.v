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
From Ucos2Verify.VC.code.flag Require Import flag_unlink_fields_goal.
From Ucos2Verify.VC.code.flag Require Import flag_unlink_fields_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.flag Ucos2Verify.lib.task Ucos2Verify.lib.flag_node_fields Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.flag.spec.flag_unlink_spec Ucos2Verify.VC.code.flag.spec.flag_unlink_fields_spec.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope sac.

Lemma proof_of_OS_FlagUnlink_entail_wit_1_1 : OS_FlagUnlink_entail_wit_1_1.
Proof.
  unfold OS_FlagUnlink_entail_wit_1_1; left; intros.
  unfold flag_unlink_fields_after_next_store_rep.
  apply Z.eqb_neq in PreH3; rewrite PreH3, PreH8; entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_entail_wit_1_2 : OS_FlagUnlink_entail_wit_1_2.
Proof.
  unfold OS_FlagUnlink_entail_wit_1_2; left; intros.
  unfold flag_unlink_fields_after_next_store_rep.
  rewrite PreH1, Z.eqb_refl, PreH4; entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_entail_wit_2_1 : OS_FlagUnlink_entail_wit_2_1.
Proof.
  unfold OS_FlagUnlink_entail_wit_2_1; left; intros.
  unfold flag_unlink_fields_after_next_store_rep.
  apply Z.eqb_neq in PreH3; rewrite PreH3; entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_entail_wit_2_2 : OS_FlagUnlink_entail_wit_2_2.
Proof.
  unfold OS_FlagUnlink_entail_wit_2_2; left; intros.
  unfold flag_unlink_fields_after_next_store_rep.
  rewrite PreH1, Z.eqb_refl; entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_which_implies_wit_1 : OS_FlagUnlink_which_implies_wit_1.
Proof.
  left; intros t w p flags sg.
  unfold flag_unlink_fields_pre; Intros.
  match goal with
  | H : flag_unlink_layout /\ flag_unlink_domain sg flags p w t |- _ =>
      destruct H as [Hlayout Hdomain]
  end.
  destruct (flag_unlink_domain_post_exists sg flags p w t Hdomain) as [post Hstep].
  pose proof Hdomain as [_ [_ [Hlookup _]]].
  assert (Hcontext : flag_unlink_context sg flags p w t post).
  { unfold flag_unlink_context; auto. }
  Exists post.
  sep_apply_l_atomic (flag_unlink_fields_read_fields_split sg flags p w Hlayout Hlookup).
  entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_which_implies_wit_2 : OS_FlagUnlink_which_implies_wit_2.
Proof.
  left; intros t w p flags sg post Hcontext.
  pose proof Hcontext as [Hlayout [Hdomain Hstep]].
  pose proof Hdomain as [_ [_ [Hlookup _]]].
  sep_apply_l_atomic (flag_unlink_fields_read_fields_merge sg flags p w Hlayout Hlookup).
  entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_which_implies_wit_3 : OS_FlagUnlink_which_implies_wit_3.
Proof.
  unfold OS_FlagUnlink_which_implies_wit_3; left.
  intros t w p flags sg post Hctx Hprev.
  pose proof Hctx as [Hlayout [[_ [Hvalid [Hw _]]] Hstep]].
  destruct Hlayout as [_ [_ [_ [_ Hhead]]]].
  destruct (flag_unlink_fields_split_head_store sg flags p w Hvalid Hw Hprev)
    as [image [Himage Hsplit]].
  unfold flag_unlink_group_addr; rewrite Hhead.
  sep_apply_l_atomic Hsplit; Exists image.
  unfold flag_unlink_group_lookup; entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_which_implies_wit_4 : OS_FlagUnlink_which_implies_wit_4.
Proof.
  unfold OS_FlagUnlink_which_implies_wit_4; left.
  intros t w p flags sg post image Hctx Hprev Himage.
  pose proof Hctx as [Hlayout [[_ [Hvalid _]] Hstep]].
  destruct Hlayout as [_ [_ [_ [_ Hhead]]]].
  unfold flag_unlink_group_addr, flag_unlink_next; rewrite Hhead.
  unfold flag_unlink_group_lookup in Himage.
  sep_apply_l_atomic (flag_unlink_fields_merge_head_store sg flags p w post image
    Hvalid Hstep Hprev Himage); entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_which_implies_wit_5 : OS_FlagUnlink_which_implies_wit_5.
Proof.
  unfold OS_FlagUnlink_which_implies_wit_5; left.
  intros t w p flags sg post Hctx Hnext.
  pose proof Hctx as [Hlayout [[_ [Hvalid _]] Hstep]].
  destruct Hlayout as [_ [Hprev _]].
  destruct (flag_unlink_fields_split_next_store sg flags p w post Hvalid Hstep Hnext)
    as [following [Hfollowing Hsplit]].
  rewrite Hprev; unfold flag_unlink_next.
  sep_apply_l_atomic Hsplit; Exists following.
  unfold flag_unlink_next_lookup, flag_unlink_next; entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_which_implies_wit_6 : OS_FlagUnlink_which_implies_wit_6.
Proof.
  unfold OS_FlagUnlink_which_implies_wit_6; left.
  intros t w p flags sg post following Hctx Hprev0 Hnext Hfollowing.
  pose proof Hctx as [Hlayout [[_ [Hvalid _]] Hstep]].
  destruct Hlayout as [_ [Hprev _]].
  rewrite Hprev, <- Hprev0.
  unfold flag_unlink_next, flag_unlink_prev, flag_unlink_fields_loan.
  unfold flag_unlink_next_lookup, flag_unlink_next in Hfollowing.
  sep_apply_l_atomic (flag_unlink_fields_merge_next_store sg flags p w post following
    Hvalid Hstep Hnext Hfollowing); entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_which_implies_wit_7 : OS_FlagUnlink_which_implies_wit_7.
Proof.
  left; intros t w p flags sg post Hcontext.
  pose proof Hcontext as [_ [Hdomain Hstep]].
  pose proof Hdomain as [_ [Hvalid _]].
  sep_apply_l_atomic (flag_unlink_fields_after_next_store_reconstructs_raw_rep
    sg flags p w post Hvalid Hstep).
  entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_which_implies_wit_8 : OS_FlagUnlink_which_implies_wit_8.
Proof.
  left; intros t w p flags sg post Hcontext.
  pose proof Hcontext as [Hlayout [Hdomain Hstep]].
  pose proof Hdomain as [_ [_ [Hlookup _]]].
  sep_apply_l_atomic (flag_unlink_fields_read_fields_merge sg flags p w Hlayout Hlookup).
  entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_which_implies_wit_9 : OS_FlagUnlink_which_implies_wit_9.
Proof.
  unfold OS_FlagUnlink_which_implies_wit_9; left.
  intros t w p flags sg post Hctx Hprev.
  pose proof Hctx as [Hlayout [[_ [Hvalid [Hw _]]] Hstep]].
  destruct Hlayout as [Hnext _].
  destruct (flag_unlink_fields_split_prev_store sg flags p w Hvalid Hw Hprev)
    as [previous [Hprevious Hsplit]].
  rewrite Hnext; unfold flag_unlink_prev.
  sep_apply_l_atomic Hsplit; Exists previous.
  unfold flag_unlink_prev_lookup, flag_unlink_prev; entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_which_implies_wit_10 : OS_FlagUnlink_which_implies_wit_10.
Proof.
  unfold OS_FlagUnlink_which_implies_wit_10; left.
  intros t w p flags sg post previous Hctx Hprev Hprevious.
  pose proof Hctx as [Hlayout [[_ [Hvalid _]] Hstep]].
  destruct Hlayout as [Hnext _].
  rewrite Hnext; unfold flag_unlink_prev, flag_unlink_next.
  unfold flag_unlink_prev_lookup, flag_unlink_prev in Hprevious.
  sep_apply_l_atomic (flag_unlink_fields_merge_prev_store sg flags p w post previous
    Hvalid Hstep Hprev Hprevious); entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_which_implies_wit_11 : OS_FlagUnlink_which_implies_wit_11.
Proof.
  unfold OS_FlagUnlink_which_implies_wit_11; left.
  intros t w p flags sg post Hctx Hnext.
  pose proof Hctx as [Hlayout [[_ [Hvalid _]] Hstep]].
  destruct Hlayout as [_ [Hprev _]].
  destruct (flag_unlink_fields_split_next_store sg flags p w post Hvalid Hstep Hnext)
    as [following [Hfollowing Hsplit]].
  rewrite Hprev; unfold flag_unlink_next.
  sep_apply_l_atomic Hsplit; Exists following.
  unfold flag_unlink_next_lookup, flag_unlink_next; entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_which_implies_wit_12 : OS_FlagUnlink_which_implies_wit_12.
Proof.
  unfold OS_FlagUnlink_which_implies_wit_12; left.
  intros t w p flags sg post following Hctx Hnext Hfollowing.
  pose proof Hctx as [Hlayout [[_ [Hvalid _]] Hstep]].
  destruct Hlayout as [_ [Hprev _]].
  rewrite Hprev; unfold flag_unlink_next, flag_unlink_prev, flag_unlink_fields_loan.
  unfold flag_unlink_next_lookup, flag_unlink_next in Hfollowing.
  sep_apply_l_atomic (flag_unlink_fields_merge_next_store sg flags p w post following
    Hvalid Hstep Hnext Hfollowing); entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_which_implies_wit_13 : OS_FlagUnlink_which_implies_wit_13.
Proof.
  left; intros t w p flags sg post Hcontext.
  pose proof Hcontext as [_ [Hdomain Hstep]].
  pose proof Hdomain as [_ [Hvalid _]].
  sep_apply_l_atomic (flag_unlink_fields_after_next_store_reconstructs_raw_rep
    sg flags p w post Hvalid Hstep).
  entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_which_implies_wit_14 : OS_FlagUnlink_which_implies_wit_14.
Proof.
  left; intros t w p flags sg post Hcontext.
  pose proof Hcontext as [Hlayout [Hdomain Hstep]].
  pose proof Hdomain as [_ [_ [_ [Haddr _]]]].
  unfold flag_unlink_fields_loan.
  sep_apply_l_atomic (flag_unlink_fields_loan_split_tcb sg p w Hlayout Haddr).
  entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_which_implies_wit_15 : OS_FlagUnlink_which_implies_wit_15.
Proof.
  left; intros t w p flags sg post Hcontext.
  pose proof Hcontext as [Hlayout [Hdomain Hstep]].
  pose proof Hdomain as [_ [_ [_ [Haddr _]]]].
  unfold flag_unlink_fields_loan.
  sep_apply_l_atomic (flag_unlink_fields_loan_merge_tcb sg p w Hlayout Haddr).
  entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_which_implies_wit_16 : OS_FlagUnlink_which_implies_wit_16.
Proof.
  left; intros t w p flags sg post Hcontext.
  pose proof Hcontext as [_ [Hdomain _]].
  pose proof (flag_unlink_task_split_node sg flags p w t Hdomain) as Hsplit.
  cbn [tcb_field_address] in Hsplit.
  sep_apply_l_atomic Hsplit.
  entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_which_implies_wit_17 : OS_FlagUnlink_which_implies_wit_17.
Proof.
  left; intros t w p flags sg post Hcontext.
  pose proof Hcontext as [_ [Hdomain _]].
  pose proof Hdomain as [_ [_ [_ [_ [_ [_ [Htcb _]]]]]]].
  pose proof (flag_unlink_task_merge_cleared_node sg w t Htcb) as Hmerge.
  cbn [tcb_field_address] in Hmerge.
  sep_apply_l_atomic Hmerge.
  entailer!.
Qed. 

Lemma proof_of_OS_FlagUnlink_which_implies_wit_18 : OS_FlagUnlink_which_implies_wit_18.
Proof.
  left; intros t w p flags sg post Hcontext.
  unfold flag_unlink_fields_loan.
  apply (flag_unlink_fields_finish_post sg flags p w t post Hcontext).
Qed. 

