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
From Ucos2Verify.VC.code.flag Require Import flag_block_call_fields_goal.
From Ucos2Verify.VC.code.flag Require Import flag_block_call_fields_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_storage Ucos2Verify.lib.sched Ucos2Verify.lib.flag Ucos2Verify.lib.flag_execution.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_fields_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope sac.

Lemma proof_of_OS_FlagBlock_entail_wit_1_1 : OS_FlagBlock_entail_wit_1_1.
Proof.
  left; intros.
  pose proof PreH1 as [Hlayout [Hconfig [_ Hprotocol]]].
  pose proof (proj1 PreH7) as Hstatus.
  rewrite unsigned_last_nbits_eq by exact Hstatus.
  unfold flag_block_call_node, flag_block_call_mask, flag_block_call_mode,
    flag_block_call_head.
  sepcon_assoc_change.
  sep_apply_l_atomic (flag_block_call_fields_node_merge sg w v Hlayout Hconfig).
  unfold flag_block_call_fields_ready_stage, flag_block_call_fields_ready_frame.
  cbn [tcb_cell tcb_field_address].
  destruct Hlayout as [_ [_ [_ [_ [_ [_ Hhead]]]]]].
  rewrite Hhead, PreH8, PreH9, PreH10.
  entailer!.
Qed. 

Lemma proof_of_OS_FlagBlock_entail_wit_1_2 : OS_FlagBlock_entail_wit_1_2.
Proof.
  left; intros.
  pose proof PreH2 as [Hlayout [Hconfig [_ Hprotocol]]].
  pose proof (proj1 PreH3) as Hstatus.
  rewrite unsigned_last_nbits_eq by exact Hstatus.
  unfold flag_block_call_node, flag_block_call_mask, flag_block_call_mode,
    flag_block_call_head.
  sepcon_assoc_change.
  sep_apply_l_atomic (flag_block_call_fields_node_merge sg w v Hlayout Hconfig).
  unfold flag_block_call_fields_ready_stage, flag_block_call_fields_ready_frame.
  cbn [tcb_cell tcb_field_address].
  unfold flag_block_call_fields_old_nodes, flag_block_old_nodes, flag_block_call_fields_nodes.
  change (flagImageHead v = 0) in PreH1.
  rewrite (proj2 (Z.eqb_eq _ _) PreH1).
  destruct Hlayout as [_ [_ [_ [_ [_ [_ Hhead]]]]]].
  rewrite Hhead, PreH4, PreH5, PreH6.
  entailer!.
Qed. 

Lemma proof_of_OS_FlagBlock_entail_wit_2_1 : OS_FlagBlock_entail_wit_2_1.
Proof.
  left; intros.
  unfold flag_block_call_fields_written, flag_block_call_grp_cleared,
    flag_block_call_row_cleared.
  rewrite (proj2 (Z.eqb_eq _ _) PreH1).
  cbn [tcb_cell tcb_field_address].
  rewrite PreH2, PreH3, PreH4.
  entailer!.
Qed. 

Lemma proof_of_OS_FlagBlock_entail_wit_2_2 : OS_FlagBlock_entail_wit_2_2.
Proof.
  left; intros.
  unfold flag_block_call_fields_written, flag_block_call_grp_cleared,
    flag_block_call_row_cleared.
  rewrite (proj2 (Z.eqb_neq _ _) PreH1).
  cbn [tcb_cell tcb_field_address].
  rewrite PreH2, PreH3, PreH4.
  entailer!.
Qed. 

Lemma proof_of_OS_FlagBlock_which_implies_wit_1 : OS_FlagBlock_which_implies_wit_1.
Proof.
  left; intros.
  rewrite (flag_block_call_fields_pre_split sg s w t g v delay).
  apply coq_prop_andp_left; intros [Hcontext Hranges].
  pose proof Hcontext as [Hlayout [Hconfig _]].
  unfold flag_block_call_fields_entry.
  sep_apply_l_atomic (flag_block_call_fields_node_split sg w Hlayout Hconfig).
  cbn [tcb_cell tcb_field_address].
  destruct Hlayout as [_ [_ [_ [_ [_ [_ Hhead]]]]]].
  rewrite Hhead, PreH1, PreH2, PreH3.
  unfold flag_block_call_node, flag_block_call_head.
  entailer!.
Qed. 

Lemma proof_of_OS_FlagBlock_which_implies_wit_2 : OS_FlagBlock_which_implies_wit_2.
Proof.
  left; intros.
  rewrite (flag_block_call_fields_head_split sg s w t g v delay PreH1 PreH2).
  Intros previous.
  Exists previous; entailer!.
Qed. 

Lemma proof_of_OS_FlagBlock_which_implies_wit_3 : OS_FlagBlock_which_implies_wit_3.
Proof.
  left; intros.
  unfold flag_block_call_node.
  sep_apply_l_atomic
    (flag_block_call_fields_head_merge sg s w t g v delay previous PreH1 PreH2 PreH3).
  entailer!.
Qed. 

Lemma proof_of_OS_FlagBlock_which_implies_wit_4 : OS_FlagBlock_which_implies_wit_4.
Proof.
  left; intros.
  unfold flag_block_call_fields_ready_stage.
  cbn [tcb_cell tcb_field_address].
  rewrite PreH1, PreH2, PreH3.
  entailer!.
Qed. 

Lemma proof_of_OS_FlagBlock_which_implies_wit_5 : OS_FlagBlock_which_implies_wit_5.
Proof.
  left; intros.
  exact (flag_block_call_fields_written_merge sg s w t g v delay PreH1).
Qed. 

