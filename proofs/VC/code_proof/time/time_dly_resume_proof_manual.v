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
From Ucos2Verify.VC.code.time Require Import time_dly_resume_goal.
From Ucos2Verify.VC.code.time Require Import time_dly_resume_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.time.spec.time_dly_resume_spec.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_status Ucos2Verify.lib.sched Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTimeDlyResume_entail_wit_1 : OSTimeDlyResume_entail_wit_1.
Proof.
  left; intros; subst prio_pre.
  sep_apply_l_atomic (time_dly_resume_save_output_acquire environment critical
    saved_local sg caller mask retval initial PreH9 PreH10 PreH11 PreH12).
  Intros active acquired.
  Exists active acquired; entailer!.
Qed. 

Lemma proof_of_OSTimeDlyResume_entail_wit_2 : OSTimeDlyResume_entail_wit_2.
Proof.
  left; intros X initial mask caller priority sg critical saved_local environment saved active acquired
    Hnull Hvalid Hlo Hhi Hprofile Haligned Hpool Haddr Hacquire Hsafe.
  pose proof (task_resume_entry_addr_eq_null__resume_storage sg acquired priority
    Hvalid ltac:(lia) Hnull) as Hfree.
  pose proof (time_dly_resume_critical_free sg priority acquired ltac:(lia) Hfree) as Hcritical.
  pose proof Haddr as Haddresses.
  destruct Haddresses as [_ [_ [_ [_ [_ [Htable _]]]]]].
  pose proof (task_resume_priority_cell_merge__resume_storage sg acquired priority
    ltac:(lia) Hvalid) as Hmerge.
  rewrite <- Htable in Hmerge.
  sep_apply_l_atomic Hmerge.
  rewrite task_resume_masked_split_inv__resume_storage.
  rewrite Hnull; entailer!.
Qed. 

Lemma proof_of_OSTimeDlyResume_entail_wit_3 : OSTimeDlyResume_entail_wit_3.
Proof.
  left; intros.
  sep_apply_l_atomic (time_dly_resume_restore_output_return environment critical
    saved_local sg caller active mask initial acquired saved priority 67 false
    acquired PreH1 PreH5).
  Intros returned restored.
  Exists returned restored; entailer!.
Qed. 

Lemma proof_of_OSTimeDlyResume_entail_wit_4 : OSTimeDlyResume_entail_wit_4.
Proof.
  left; intros X initial mask caller priority sg critical saved_local environment saved active acquired
    Hreserved Hnonnull Hvalid Hlo Hhi Hprofile Haligned Hpool Haddr Hacquire Hsafe.
  pose proof (task_resume_entry_addr_eq_reserved sg (prioTbl (TskState acquired) priority)
    Hprofile Haligned Hreserved) as Hentry.
  pose proof (time_dly_resume_critical_reserved sg priority acquired ltac:(lia) Hentry) as Hcritical.
  pose proof Haddr as Haddresses.
  destruct Haddresses as [_ [_ [_ [_ [_ [Htable _]]]]]].
  pose proof (task_resume_priority_cell_merge__resume_storage sg acquired priority
    ltac:(lia) Hvalid) as Hmerge.
  rewrite <- Htable in Hmerge.
  sep_apply_l_atomic Hmerge.
  rewrite task_resume_masked_split_inv__resume_storage.
  rewrite Hreserved; entailer!.
Qed. 

Lemma proof_of_OSTimeDlyResume_entail_wit_5 : OSTimeDlyResume_entail_wit_5.
Proof.
  left; intros.
  sep_apply_l_atomic (time_dly_resume_restore_output_return environment critical
    saved_local sg caller active mask initial acquired saved priority 67 false
    acquired PreH1 PreH5).
  Intros returned restored.
  Exists returned restored; entailer!.
Qed. 

Lemma proof_of_OSTimeDlyResume_entail_wit_6 : OSTimeDlyResume_entail_wit_6.
Proof.
  left; intros X initial mask caller priority sg critical saved_local environment saved active acquired
    Hnotreserved Hnonnull Hvalid Hlo Hhi Hprofile Haligned Hpool Haddr Hacquire Hsafe.
  pose proof Haddr as Haddresses.
  destruct Haddresses as [_ [_ [_ [_ [_ [Htable [_ Hnew]]]]]]].
  destruct Hnew as [_ [Hgroup [Hrows _]]].
  pose proof (task_resume_priority_cell_merge__resume_storage sg acquired priority
    ltac:(lia) Hvalid) as Hmerge.
  rewrite <- Htable in Hmerge.
  destruct (prioTbl (TskState acquired) priority) as [| |tid] eqn:Hentry;
    [exfalso; apply Hnonnull; reflexivity|exfalso; apply Hnotreserved; reflexivity|].
  destruct (task_resume_priority_task_live__resume_storage sg acquired priority tid
    Hvalid ltac:(lia) Hentry) as [node Hnode].
  destruct (proj2 (task_resume_live_priority_range__resume_storage sg acquired tid node
    Hvalid Hnode)) as [Hylo Hyhi].
  sep_apply_l_atomic Hmerge.
  sep_apply_l_atomic (time_dly_resume_node_split sg acquired tid node Hvalid Hnode).
  Exists node tid.
  unfold time_dly_resume_node_cells.
  cbn [prio_tbl_entry_to_addr tcb_layout_cell tcb_cell tcb_field_address].
  rewrite <- Hgroup, <- Hrows; entailer!.
Qed. 

Lemma proof_of_OSTimeDlyResume_entail_wit_7 : OSTimeDlyResume_entail_wit_7.
Proof.
  left; intros X initial mask caller priority sg critical saved_local environment saved active acquired ptcb tid node
    Hd Hlo Hhi Hprofile Hpool Haddr Hacquire Hvalid Hentry Hnode Hptcb Hylo Hyhi Hsafe.
  pose proof (time_dly_resume_critical_zero_delay sg priority acquired tid node
    ltac:(lia) Hentry Hnode Hd) as Hcritical.
  pose proof Haddr as Haddresses.
  destruct Haddresses as [_ [_ [_ [_ [_ [_ [_ Hnew]]]]]]].
  destruct Hnew as [_ [Hgroup [Hrows _]]].
  pose proof (time_dly_resume_node_merge sg acquired tid node Hvalid Hnode) as Hmerge.
  unfold time_dly_resume_node_cells in Hmerge.
  cbn [tcb_layout_cell tcb_cell tcb_field_address] in Hmerge.
  rewrite <- Hgroup, <- Hrows in Hmerge.
  subst ptcb; sep_apply_l_atomic Hmerge.
  rewrite task_resume_masked_split_inv__resume_storage; entailer!.
Qed. 

Lemma proof_of_OSTimeDlyResume_entail_wit_8 : OSTimeDlyResume_entail_wit_8.
Proof.
  left; intros.
  sep_apply_l_atomic (time_dly_resume_restore_output_return environment critical
    saved_local sg caller active mask initial acquired saved priority 80 false
    acquired PreH1 PreH5).
  Intros returned restored.
  Exists returned restored; entailer!.
Qed. 

Lemma proof_of_OSTimeDlyResume_entail_wit_9_1 : OSTimeDlyResume_entail_wit_9_1.
Proof.
  left; intros X initial mask caller priority sg critical saved_local environment saved active acquired ptcb tid node
    Hpending Hd Hlo Hhi Hprofile Hpool Haddr Hacquire Hvalid Hentry Hnode Hptcb Hylo Hyhi Hsafe.
  assert (Htest : task_status_has_pending (encode_task_status (stat node)) = true).
  { unfold task_status_has_pending, task_pend_any_mask.
    rewrite (proj2 (Z.eqb_neq _ _) Hpending); reflexivity. }
  destruct (time_dly_resume_pending_fields node) as [Hstat [Hpend Hdly]].
  rewrite Htest in Hstat, Hpend.
  rewrite Hstat, Hpend.
  change (unsigned_last_nbits (Z.lnot 55) 8) with 200.
  entailer!.
Qed. 

Lemma proof_of_OSTimeDlyResume_entail_wit_9_2 : OSTimeDlyResume_entail_wit_9_2.
Proof.
  left; intros X initial mask caller priority sg critical saved_local environment saved active acquired ptcb tid node
    Hpending Hd Hlo Hhi Hprofile Hpool Haddr Hacquire Hvalid Hentry Hnode Hptcb Hylo Hyhi Hsafe.
  assert (Htest : task_status_has_pending (encode_task_status (stat node)) = false).
  { unfold task_status_has_pending, task_pend_any_mask.
    rewrite Hpending; reflexivity. }
  destruct (time_dly_resume_pending_fields node) as [Hstat [Hpend Hdly]].
  rewrite Htest in Hstat, Hpend.
  rewrite Hstat, Hpend; entailer!.
Qed. 

Lemma proof_of_OSTimeDlyResume_entail_wit_10 : OSTimeDlyResume_entail_wit_10.
Proof.
  left; intros X initial mask caller priority sg critical saved_local environment saved active acquired tid node ptcb
    Hguard Hlo Hhi Hprofile Haddr Hacquire Hvalid Hentry Hnode Hd Hptcb Hylo Hyhi Hsafe.
  assert (Hsuspended : task_is_suspended (stat node) = false).
  { rewrite <- (task_expire_delay_preserves_suspension node).
    change (negb (Z.eqb (Z.land (encode_task_status (stat (task_expire_delay node))) 8) 0) = false).
    rewrite Hguard; reflexivity. }
  pose proof (time_dly_resume_critical_success sg priority acquired tid node
    ltac:(lia) Hentry Hnode Hd) as Hcritical.
  rewrite Hsuspended in Hcritical; cbn [negb] in Hcritical.
  pose proof Haddr as Haddresses.
  destruct Haddresses as [_ [_ [_ [_ [_ [_ [_ Hnew]]]]]]].
  destruct Hnew as [_ [Hgroup [Hrows _]]].
  destruct (task_resume_bitmap_bytes__resume_storage sg acquired tid node Hvalid Hnode)
    as [Hgrp [Hrow [Hbx Hby]]].
  rewrite Hgrp, Hrow, Hbx, Hby.
  pose proof (time_dly_resume_updated_fields_merge sg (TskState acquired) tid node) as Hfields.
  cbn [tcb_layout_cell tcb_cell tcb_field_address] in Hfields.
  pose proof (time_dly_resume_sched_storage_merge sg acquired tid node Hvalid Hnode) as Hsched.
  rewrite Hsuspended, <- Hgroup, <- Hrows in Hsched.
  subst ptcb.
  sep_apply_l_atomic (time_dly_resume_mask_frame_update environment critical saved_local sg active saved
    acquired acquired tid node Hnode).
  rewrite task_resume_masked_split_inv__resume_storage; entailer!.
  sep_apply_r_atomic (time_dly_resume_task_sched_resources_merge sg acquired tid node Hvalid Hnode Hd).
  sepcon_assoc_change.
  sep_apply_r_atomic Hfields.
  sepcon_assoc_change.
  sep_apply_r_atomic Hsched.
  unfold time_dly_resume_node_frame; entailer!.
  rewrite <- Hrows; reflexivity.
Qed. 

Lemma proof_of_OSTimeDlyResume_entail_wit_11 : OSTimeDlyResume_entail_wit_11.
Proof.
  left; intros.
  sep_apply_l_atomic (time_dly_resume_restore_output_return environment critical
    saved_local sg caller active mask initial acquired saved priority 0 true
    (time_dly_resume_state sg acquired tid node) PreH1 PreH5).
  Intros returned restored.
  Exists returned restored; entailer!.
Qed. 

Lemma proof_of_OSTimeDlyResume_entail_wit_12 : OSTimeDlyResume_entail_wit_12.
Proof.
  left; intros.
  pose proof (time_dly_resume_return_facts_sched_safe environment critical sg
    caller returned mask initial priority 0 restored X PreH2 PreH4 PreH5)
    as Hsched.
  sep_apply_l_atomic (time_dly_resume_closed_sched_pre environment critical
    saved_local sg caller returned mask initial priority restored PreH4).
  entailer!.
Qed. 

Lemma proof_of_OSTimeDlyResume_entail_wit_13 : OSTimeDlyResume_entail_wit_13.
Proof.
  left; intros X initial mask caller priority sg critical saved_local environment saved active acquired tid node ptcb
    Hguard Hlo Hhi Hprofile Haddr Hacquire Hvalid Hentry Hnode Hd Hptcb Hylo Hyhi Hsafe.
  assert (Hsuspended : task_is_suspended (stat node) = true).
  { rewrite <- (task_expire_delay_preserves_suspension node).
    change (negb (Z.eqb (Z.land (encode_task_status (stat (task_expire_delay node))) 8) 0) = true).
    rewrite (proj2 (Z.eqb_neq _ _) Hguard); reflexivity. }
  pose proof (time_dly_resume_critical_success sg priority acquired tid node
    ltac:(lia) Hentry Hnode Hd) as Hcritical.
  rewrite Hsuspended in Hcritical; cbn [negb] in Hcritical.
  pose proof Haddr as Haddresses.
  destruct Haddresses as [_ [_ [_ [_ [_ [_ [_ Hnew]]]]]]].
  destruct Hnew as [_ [Hgroup [Hrows _]]].
  pose proof (time_dly_resume_updated_fields_merge sg (TskState acquired) tid node) as Hfields.
  cbn [tcb_layout_cell tcb_cell tcb_field_address] in Hfields.
  pose proof (time_dly_resume_sched_storage_merge sg acquired tid node Hvalid Hnode) as Hsched.
  rewrite Hsuspended, <- Hgroup, <- Hrows in Hsched.
  subst ptcb.
  sep_apply_l_atomic (time_dly_resume_mask_frame_update environment critical saved_local sg active saved
    acquired acquired tid node Hnode).
  rewrite task_resume_masked_split_inv__resume_storage; entailer!.
  sep_apply_r_atomic (time_dly_resume_task_sched_resources_merge sg acquired tid node Hvalid Hnode Hd).
  sepcon_assoc_change.
  sep_apply_r_atomic Hfields.
  sepcon_assoc_change.
  sep_apply_r_atomic Hsched.
  unfold time_dly_resume_node_frame; entailer!.
  rewrite <- Hrows; reflexivity.
Qed. 

Lemma proof_of_OSTimeDlyResume_entail_wit_14 : OSTimeDlyResume_entail_wit_14.
Proof.
  left; intros.
  sep_apply_l_atomic (time_dly_resume_restore_output_return environment critical
    saved_local sg caller active mask initial acquired saved priority 0 false
    (time_dly_resume_state sg acquired tid node) PreH1 PreH5).
  Intros returned restored.
  Exists returned restored; entailer!.
Qed. 

Lemma proof_of_OSTimeDlyResume_return_wit_1 : OSTimeDlyResume_return_wit_1.
Proof.
  left; intros.
  eapply time_dly_resume_sched_return_post; [lia | eassumption | eassumption].
Qed. 

Lemma proof_of_OSTimeDlyResume_return_wit_2 : OSTimeDlyResume_return_wit_2.
Proof.
  left; intros.
  eapply time_dly_resume_closed_return_post; [lia | eassumption | eassumption].
Qed. 

Lemma proof_of_OSTimeDlyResume_return_wit_3 : OSTimeDlyResume_return_wit_3.
Proof.
  left; intros.
  eapply time_dly_resume_closed_return_post; [lia | eassumption | eassumption].
Qed. 

Lemma proof_of_OSTimeDlyResume_return_wit_4 : OSTimeDlyResume_return_wit_4.
Proof.
  left; intros.
  eapply time_dly_resume_closed_return_post; [lia | eassumption | eassumption].
Qed. 

Lemma proof_of_OSTimeDlyResume_return_wit_5 : OSTimeDlyResume_return_wit_5.
Proof.
  left; intros.
  eapply time_dly_resume_closed_return_post; [lia | eassumption | eassumption].
Qed. 

Lemma proof_of_OSTimeDlyResume_return_wit_6 : OSTimeDlyResume_return_wit_6.
Proof.
  left; intros.
  eapply time_dly_resume_early_return_post; [lia | eassumption].
Qed. 

Lemma proof_of_OSTimeDlyResume_return_wit_7 : OSTimeDlyResume_return_wit_7.
Proof.
  left; intros.
  eapply time_dly_resume_early_return_post; [lia | eassumption].
Qed. 

Lemma proof_of_OSTimeDlyResume_which_implies_wit_1 : OSTimeDlyResume_which_implies_wit_1.
Proof.
  left; intros sg critical saved_local environment saved active acquired.
  apply (proj1 (task_resume_masked_split_inv__resume_storage
    environment critical saved_local sg active saved acquired acquired)).
Qed. 

Lemma proof_of_OSTimeDlyResume_which_implies_wit_2 : OSTimeDlyResume_which_implies_wit_2.
Proof.
  left; intros priority sg acquired Hlo Hhi Haddr.
  destruct Haddr as [_ [_ [_ [_ [_ [Htable _]]]]]].
  unfold UCOS2_inv; Intros.
  rewrite UCOS2_raw_rep_priority_table_equiv.
  sep_apply_l_atomic (store_prio_tbl_split_cell sg (prioTbl (TskState acquired)) priority ltac:(lia)).
  unfold task_resume_priority_frame; rewrite <- Htable; entailer!.
Qed. 

