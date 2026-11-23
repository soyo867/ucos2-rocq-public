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
From Ucos2Verify.VC.code.mutex Require Import rdyatprio_full_goal.
From Ucos2Verify.VC.code.mutex Require Import rdyatprio_full_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.mutex_rdyatprio_spec.
Require Import Ucos2Verify.lib.array_abstraction.
Local Open Scope sac.

Lemma proof_of_OSMutex_RdyAtPrio_full_safety_wit_1_current_owner : OSMutex_RdyAtPrio_full_safety_wit_1_current_owner.
Proof.
  pre_process; entailer!; unfold valid_priority_index in *; lia.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_safety_wit_2_current_owner : OSMutex_RdyAtPrio_full_safety_wit_2_current_owner.
Proof.
  pre_process; entailer!; unfold valid_priority_index in *; lia.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_safety_wit_3_noncurrent_owner : OSMutex_RdyAtPrio_full_safety_wit_3_noncurrent_owner.
Proof.
  pre_process; entailer!; unfold valid_priority_index in *; lia.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_safety_wit_4_noncurrent_owner : OSMutex_RdyAtPrio_full_safety_wit_4_noncurrent_owner.
Proof.
  pre_process; entailer!; unfold valid_priority_index in *; lia.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_safety_wit_5_current_owner : OSMutex_RdyAtPrio_full_safety_wit_5_current_owner.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg; right; lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      change (Z.shiftr prio_pre 3 mod 8 <= 63);
      pose proof (Z.mod_pos_bound (Z.shiftr prio_pre 3) 8 ltac:(lia));
      lia ]
  ).
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_safety_wit_6_current_owner : OSMutex_RdyAtPrio_full_safety_wit_6_current_owner.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg; right; lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      change (Z.shiftr prio_pre 3 mod 8 <= 63);
      pose proof (Z.mod_pos_bound (Z.shiftr prio_pre 3) 8 ltac:(lia));
      lia ]
  ).
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_safety_wit_7_noncurrent_owner : OSMutex_RdyAtPrio_full_safety_wit_7_noncurrent_owner.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg; right; lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      change (Z.shiftr prio_pre 3 mod 8 <= 63);
      pose proof (Z.mod_pos_bound (Z.shiftr prio_pre 3) 8 ltac:(lia));
      lia ]
  ).
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_safety_wit_8_noncurrent_owner : OSMutex_RdyAtPrio_full_safety_wit_8_noncurrent_owner.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg; right; lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      change (Z.shiftr prio_pre 3 mod 8 <= 63);
      pose proof (Z.mod_pos_bound (Z.shiftr prio_pre 3) 8 ltac:(lia));
      lia ]
  ).
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_safety_wit_9_current_owner : OSMutex_RdyAtPrio_full_safety_wit_9_current_owner.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg; right; lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      change (prio_pre mod 8 <= 63);
      pose proof (Z.mod_pos_bound prio_pre 8 ltac:(lia));
      lia ]
  ).
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_safety_wit_10_current_owner : OSMutex_RdyAtPrio_full_safety_wit_10_current_owner.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg; right; lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      change (prio_pre mod 8 <= 63);
      pose proof (Z.mod_pos_bound prio_pre 8 ltac:(lia));
      lia ]
  ).
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_safety_wit_11_noncurrent_owner : OSMutex_RdyAtPrio_full_safety_wit_11_noncurrent_owner.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg; right; lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      change (prio_pre mod 8 <= 63);
      pose proof (Z.mod_pos_bound prio_pre 8 ltac:(lia));
      lia ]
  ).
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_safety_wit_12_noncurrent_owner : OSMutex_RdyAtPrio_full_safety_wit_12_noncurrent_owner.
Proof.
  pre_process;
  try (
    entailer!;
    [ apply Z.land_nonneg; right; lia
    | replace 7 with (Z.ones 3) by reflexivity;
      rewrite Z.land_ones by lia;
      change (prio_pre mod 8 <= 63);
      pose proof (Z.mod_pos_bound prio_pre 8 ltac:(lia));
      lia ]
  ).
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_return_wit_1_noncurrent_owner : OSMutex_RdyAtPrio_full_return_wit_1_noncurrent_owner.
Proof.
  pre_process.
  unfold task_rdy_snapshot_of_prop in H3.
  destruct H3 as
    (Hget & Hpt & Holdprio & Holdx & Holdy & Holdbitx & Holdbity).
  unfold task_priority_fields_layout_prop in H2.
  destruct H2 as (Hprioaddr & Hxaddr & Hyaddr & Hbitxaddr & Hbityaddr).
  unfold sched_tcb_cur_snapshot_prop in H1.
  unfold os_tcb_cur_addr in H4.
  unfold os_prio_cur_addr in H5.
  unfold os_rdy_grp_addr in H6.
  unfold os_rdy_tbl_addr in H10.
  unfold os_tcb_prio_tbl_addr in H12.
  destruct H9 as (Hrdygrp & Hrdytbl & Hpriocur).
  rewrite H4.
  sep_apply_l_atomic
    (Ucos2Verify.lib.mutex_rdyatprio_spec.OSMutex_RdyAtPrio_sched_rest_fold__return_transition_rebuild
       sg (TskState ls0) (SchedState ls0) tcbcur_in H1).
  sep_apply_l_atomic
    (debug_extract_relocation_validities__relocation_semantics sg ls0 tid).
  Intros_p Hvalids.
  destruct Hvalids as (Htask & Hsched & Hevent).
  pose proof
    (debug_priority_encoding__relocation_semantics sg prio_in H7 H0)
    as (Hencx & Hency & Hencbitx & Hencbity).
  destruct
    (OSMutex_RdyAtPrio_ready_owner_transition_exists
       sg ls0 tid old_t prio_in H)
    as (new_t_ignored & ls_post & Hraw).
  clear new_t_ignored.
  pose proof Hraw as Hraw_keep.
  unfold atomic_task_set_curPrio_ready_owner_exec in Hraw.
  destruct Hraw as
    (new_t & Hraw_in & Hraw_get & Hraw_lo & Hraw_hi & Hnew & Hpost).
  assert (Hguarantee :
    OSMutex_RdyAtPrio_guarantee sg ptcb_pre prio_pre ls0 ls_post).
  {
    unfold OSMutex_RdyAtPrio_guarantee, OSMutex_RdyAtPrio_sem.
    exists tid, old_t.
    split.
    - rewrite <- PreH4. exact Hpt.
    - split.
      + rewrite PreH3. exact H.
      + rewrite PreH3. exact Hraw_keep.
  }
  pose proof
    (OSMutex_RdyAtPrio_safe_return
       sg ls0 ptcb_pre prio_pre ls_post X Hguarantee PreH6)
    as Hsafe.
  pose proof
    (OSMutex_RdyAtPrio_owner_effect_conditional_preservation
       sg ls0 ls_post tid old_t prio_in
       H7 Htask Hsched Hevent H8 Hraw_keep)
    as Hpreserved.
  pose proof
    (OSMutex_RdyAtPrio_owner_effect_conditional_cross
       sg ls0 ls_post restore_mid tid old_t prio_in
       H7 Htask Hsched Hevent H8 Hraw_keep)
    as Hcrossed.
  assert (Hsnapshot :
    sched_ready_prio_snapshot_prop sg (TskState ls0) (SchedState ls0)
      rdy_grp_in rdyL_in prio_cur_in).
  {
    unfold sched_ready_prio_snapshot_prop.
    split; [exact Hrdygrp|].
    split; [exact Hrdytbl|exact Hpriocur].
  }
  assert (Hnewbitx :
    tcb_bitx_out = Z.shiftl 1 (Z.land prio_in 7)).
  { rewrite PreH13, PreH11. reflexivity. }
  pose proof
    (OSMutex_RdyAtPrio_owner_effect_conditional_ready_snapshot__owner_transition_return
       sg ls0 ls_post tid old_t prio_in
       rdy_grp_in rdyL_in prio_cur_in
       tcb_y_in tcb_bitx_in tcb_bity_in
       tcb_y_out tcb_bitx_out tcb_bity_out
       rdy_tbl_y_in rdy_tbl_y_out
       rdy_tbl_new_y_in rdy_tbl_new_y_out
       rdy_grp_out rdyL_out
       H7 Htask Hsched Hevent H8 Hsnapshot
       Holdy Holdbitx Holdbity PreH10 Hnewbitx PreH12
       PreH7 PreH14 PreH15 PreH16 PreH17 PreH18 Hraw_keep)
    as Hready_snapshot.
  assert (Hpost_task_snapshot :
    task_rdy_snapshot_of_prop sg (TskState ls_post) tid new_t pt prio_in
      tcb_x_out tcb_y_out tcb_bitx_out tcb_bity_out).
  {
    unfold task_rdy_snapshot_of_prop.
    repeat split.
    - rewrite Hpost. cbn. rewrite Z.eqb_refl. reflexivity.
    - exact Hpt.
    - rewrite Hnew. reflexivity.
    - rewrite Hnew, PreH11. exact Hencx.
    - rewrite Hnew, PreH10. exact Hency.
    - rewrite Hnew, PreH13, PreH11.
      unfold tcb_bit_x_of_prio. rewrite Hencx. reflexivity.
    - rewrite Hnew, PreH12, PreH10.
      unfold tcb_bit_y_of_prio. rewrite Hency. reflexivity.
  }
  assert (Hpost_priotbl :
    prio_tbl_list_rel sg (TskState ls_post) prioL_out).
  {
    rewrite PreH19, Hpt.
    eapply debug_priotbl_rel_update_task__relocation_semantics.
    - exact H7.
    - exact H0.
    - rewrite Hpost. reflexivity.
    - exact H11.
  }
  first
    [ assert (Hcurvalue :
        ready_owner_cur_prio_value_after (SchedState ls0) tid prio_in =
          prio_cur_in)
      by (
        unfold ready_owner_cur_prio_value_after,
          ready_owner_cur_prio_after;
        destruct (curTaskID (SchedState ls0))
          as [current_tid |] eqn:Hcurtid;
        [ assert (Hne : current_tid <> tid)
          by (
            intro Heq; subst current_tid; apply PreH1;
            rewrite Hpt, H1; reflexivity);
          rewrite (proj2 (Z.eqb_neq current_tid tid) Hne);
          rewrite Hpriocur; reflexivity
        | rewrite Hpriocur; reflexivity ])
    | assert (Hcurvalue :
        ready_owner_cur_prio_value_after (SchedState ls0) tid prio_in =
          prio_in)
      by (
        unfold ready_owner_cur_prio_value_after,
          ready_owner_cur_prio_after;
        destruct (curTaskID (SchedState ls0))
          as [current_tid |] eqn:Hcurtid;
        [ assert (Heq : current_tid = tid)
          by (
            unfold tcb_addr, sizeof_OS_TCB in H1, Hpt;
            lia);
          subst current_tid;
          rewrite Z.eqb_refl; reflexivity
        | exfalso; apply PreH5;
          rewrite PreH1, H1; reflexivity ])
    ].
  pose proof Htask as Htask_parts.
  unfold task_vaild_cond_prop in Htask_parts.
  destruct Htask_parts as (Htask_global & Htask_derived).
  unfold valid_GlobTaskAbstractState, task_in_range in Htask_global.
  destruct Htask_global as
    (_ & _ & _ & _ & _ & _ & Htask_unique).
  pose proof Hsched as Hsched_parts.
  unfold sched_in_range in Hsched_parts.
  destruct Hsched_parts as
    (_ & _ & _ & Hready_nodup & _ & _ & _).
  pose proof H7 as Hsg_parts.
  unfold valid_stable_glob_vars in Hsg_parts.
  destruct Hsg_parts as (_ & _ & _ & _ & _ & Hlowest & _).
  pose proof H0 as Hprio_bounds.
  unfold valid_priority_index in Hprio_bounds.
  rewrite Hlowest in Hprio_bounds.
  destruct Hrdytbl as (Hrdylen & Hrdynth).
  destruct H11 as (Hpriolen & Hprionth).
  assert (Hnewxrange : 0 <= tcb_x_out < 8).
  {
    rewrite PreH11, Hencx.
    unfold tcb_x_of_prio.
    apply Z.mod_pos_bound. lia.
  }
  assert (Hnewyrange : 0 <= tcb_y_out < 8).
  {
    rewrite PreH10, Hency.
    unfold tcb_y_of_prio.
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia.
  }
  assert (Hrdybyte : forall y, 0 <= y < 8 ->
    0 <= Znth y rdyL_in 0 < 2 ^ 8).
  {
    intros y Hy.
    rewrite Hrdynth by exact Hy.
    apply debug_encode_tbl_byte__relocation_semantics.
    - exact Hready_nodup.
    - exact Htask_unique.
    - intros tid0 t0 Hin Hget0.
      destruct (Htask_derived tid0 t0 Hget0) as (Hvalid0 & _).
      exact (proj1 Hvalid0).
  }
  assert (Hrdygrpbyte : 0 <= rdy_grp_in < 2 ^ 8).
  {
    rewrite Hrdygrp.
    apply debug_encode_grp_byte__relocation_semantics.
    intros tid0 t0 Hin Hget0.
    destruct (Htask_derived tid0 t0 Hget0) as (_ & Hderived0).
    unfold valid_derived_fields in Hderived0.
    tauto.
  }
  assert (Hunsignedgrp :
    unsigned_last_nbits rdy_grp_in 8 = rdy_grp_in).
  { apply unsigned_last_nbits_eq. exact Hrdygrpbyte. }
  assert (Hbitxbyte :
    0 <= Z.shiftl 1 (Z.land prio_pre 7) < 2 ^ 8).
  {
    rewrite PreH3, <- PreH11.
    apply debug_shiftl_bit_byte__relocation_semantics.
    exact Hnewxrange.
  }
  assert (Hbitybyte :
    0 <= Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7) < 2 ^ 8).
  {
    rewrite PreH3, <- PreH10.
    apply debug_shiftl_bit_byte__relocation_semantics.
    exact Hnewyrange.
  }
  assert (Hunsignedbitx :
    unsigned_last_nbits (Z.shiftl 1 (Z.land prio_pre 7)) 8 =
      tcb_bitx_out).
  {
    rewrite unsigned_last_nbits_eq by exact Hbitxbyte.
    rewrite PreH3, PreH13, PreH11. reflexivity.
  }
  assert (Hunsignedbity :
    unsigned_last_nbits
      (Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7)) 8 =
      tcb_bity_out).
  {
    rewrite unsigned_last_nbits_eq by exact Hbitybyte.
    rewrite PreH3, PreH12, PreH10. reflexivity.
  }
  assert (Holdrowbyte : 0 <= rdy_tbl_y_in < 2 ^ 8).
  { rewrite <- PreH7. apply Hrdybyte. lia. }
  assert (Hunsignedcleared :
    unsigned_last_nbits rdy_tbl_y_out 8 = rdy_tbl_y_out).
  {
    rewrite PreH14.
    apply unsigned_last_nbits_land_missing_l; [lia|exact Holdrowbyte].
  }
  assert (Hclearedbyte : 0 <= rdy_tbl_y_out < 2 ^ 8).
  {
    pose proof (unsigned_Lastnbits_range rdy_tbl_y_out 8 ltac:(lia))
      as Hclearedrange.
    rewrite Hunsignedcleared in Hclearedrange.
    exact Hclearedrange.
  }
  assert (Hnewinputbyte : 0 <= rdy_tbl_new_y_in < 2 ^ 8).
  {
    rewrite PreH16.
    rewrite (debug_zlist_replace__relocation_semantics
      rdyL_in tcb_y_in rdy_tbl_y_out tcb_y_out).
    - destruct (Z.eqb tcb_y_in tcb_y_out); [exact Hclearedbyte|].
      apply Hrdybyte. exact Hnewyrange.
    - rewrite Hrdylen. unfold OS_RDY_TBL_SIZE. lia.
    - rewrite Hrdylen. unfold OS_RDY_TBL_SIZE. exact Hnewyrange.
  }
  assert (Hunsignednewinput :
    unsigned_last_nbits rdy_tbl_new_y_in 8 = rdy_tbl_new_y_in).
  { apply unsigned_last_nbits_eq. exact Hnewinputbyte. }
  assert (Hrdycell :
    Z.lor (unsigned_last_nbits rdy_tbl_new_y_in 8)
      (unsigned_last_nbits (Z.shiftl 1 (Z.land prio_pre 7)) 8) =
    rdy_tbl_new_y_out).
  {
    rewrite Hunsignednewinput, Hunsignedbitx.
    symmetry. exact PreH17.
  }
  first
    [ assert (Hrdyoutne : rdy_tbl_y_out <> 0)
      by (rewrite PreH14; exact PreH2);
      assert (Hgroupcell :
        Z.lor (unsigned_last_nbits rdy_grp_in 8)
          (unsigned_last_nbits
            (Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7)) 8) =
        rdy_grp_out)
      by (
        rewrite Hunsignedgrp, Hunsignedbity, PreH15;
        unfold ready_group_after_relocation;
        rewrite (proj2 (Z.eqb_neq rdy_tbl_y_out 0) Hrdyoutne);
        reflexivity)
    | assert (Hrdyoutzero : rdy_tbl_y_out = 0)
      by (rewrite PreH14; exact PreH2);
      assert (Hgroupcell :
        Z.lor
          (Z.land rdy_grp_in
            (unsigned_last_nbits (Z.lnot tcb_bity_in) 8))
          (unsigned_last_nbits
            (Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7)) 8) =
        rdy_grp_out)
      by (
        rewrite Hunsignedbity, PreH15;
        unfold ready_group_after_relocation;
        rewrite (proj2 (Z.eqb_eq rdy_tbl_y_out 0) Hrdyoutzero);
        reflexivity)
    ].
  assert (Hprioindex : priotbl_index_in_range prio_in).
  {
    unfold priotbl_index_in_range, OS_PRIO_TBL_SIZE.
    lia.
  }
  assert (Hrdyindex : osrdytbl_index_in_range tcb_y_out).
  {
    unfold osrdytbl_index_in_range, OS_RDY_TBL_SIZE.
    exact Hnewyrange.
  }
  assert (Hinterlen :
    Zlength (replace_Znth tcb_y_in rdy_tbl_y_out rdyL_in) =
      OS_RDY_TBL_SIZE).
  {
    rewrite Zlength_replace_Znth, Hrdylen. reflexivity.
  }
  assert (Hprioout :
    prioL_out = replace_Znth prio_in (tcb_addr sg tid) prioL_in).
  { rewrite <- Hpt. exact PreH19. }
  Exists new_t ls_post.
  unfold OSMutex_RdyAtPrio_raw_stage.
  rewrite Hprioaddr, Hxaddr, Hyaddr, Hbitxaddr, Hbityaddr, Hpt.
  rewrite H12, H10, H6, H5.
  rewrite Hrdycell, Hgroupcell.
  rewrite Hunsignedbitx, Hunsignedbity, PreH3.
  rewrite <- PreH11.
  rewrite Hcurvalue.
  rewrite Hprioout.
  sep_apply_l_atomic
    (debug_store_priotbl_merge_c_cell__relocation_semantics
       sg prioL_in prio_in (tcb_addr sg tid) Hprioindex Hpriolen).
  sep_apply_l_atomic
    (debug_store_osrdytbl_merge_c_cell__relocation_semantics
       sg (replace_Znth tcb_y_in rdy_tbl_y_out rdyL_in)
       tcb_y_out rdy_tbl_new_y_out Hrdyindex Hinterlen).
  rewrite <- PreH18.
  repeat rewrite
    Ucos2Verify.lib.mutex_rdyatprio_spec.OSMutex_RdyAtPrio_truep_contract_across__return_transition_rebuild.
  entailer!.
  - repeat lazymatch goal with
    | |- ?L |-- TT ** ?R =>
        apply
          (Ucos2Verify.lib.mutex_rdyatprio_spec.OSMutex_RdyAtPrio_entail_add_truep__return_transition_rebuild
             L R)
    end.
    entailer!.
  - rewrite <- PreH3. exact Hguarantee.
  - rewrite <- Hpt. exact Hpost_task_snapshot.
  - rewrite <- Hprioout. exact Hpost_priotbl.
  - rewrite <- PreH3. exact Hsafe.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_return_wit_2_noncurrent_owner : OSMutex_RdyAtPrio_full_return_wit_2_noncurrent_owner.
Proof.
  pre_process.
  unfold task_rdy_snapshot_of_prop in H3.
  destruct H3 as
    (Hget & Hpt & Holdprio & Holdx & Holdy & Holdbitx & Holdbity).
  unfold task_priority_fields_layout_prop in H2.
  destruct H2 as (Hprioaddr & Hxaddr & Hyaddr & Hbitxaddr & Hbityaddr).
  unfold sched_tcb_cur_snapshot_prop in H1.
  unfold os_tcb_cur_addr in H4.
  unfold os_prio_cur_addr in H5.
  unfold os_rdy_grp_addr in H6.
  unfold os_rdy_tbl_addr in H10.
  unfold os_tcb_prio_tbl_addr in H12.
  destruct H9 as (Hrdygrp & Hrdytbl & Hpriocur).
  rewrite H4.
  sep_apply_l_atomic
    (Ucos2Verify.lib.mutex_rdyatprio_spec.OSMutex_RdyAtPrio_sched_rest_fold__return_transition_rebuild
       sg (TskState ls0) (SchedState ls0) tcbcur_in H1).
  sep_apply_l_atomic
    (debug_extract_relocation_validities__relocation_semantics sg ls0 tid).
  Intros_p Hvalids.
  destruct Hvalids as (Htask & Hsched & Hevent).
  pose proof
    (debug_priority_encoding__relocation_semantics sg prio_in H7 H0)
    as (Hencx & Hency & Hencbitx & Hencbity).
  destruct
    (OSMutex_RdyAtPrio_ready_owner_transition_exists
       sg ls0 tid old_t prio_in H)
    as (new_t_ignored & ls_post & Hraw).
  clear new_t_ignored.
  pose proof Hraw as Hraw_keep.
  unfold atomic_task_set_curPrio_ready_owner_exec in Hraw.
  destruct Hraw as
    (new_t & Hraw_in & Hraw_get & Hraw_lo & Hraw_hi & Hnew & Hpost).
  assert (Hguarantee :
    OSMutex_RdyAtPrio_guarantee sg ptcb_pre prio_pre ls0 ls_post).
  {
    unfold OSMutex_RdyAtPrio_guarantee, OSMutex_RdyAtPrio_sem.
    exists tid, old_t.
    split.
    - rewrite <- PreH4. exact Hpt.
    - split.
      + rewrite PreH3. exact H.
      + rewrite PreH3. exact Hraw_keep.
  }
  pose proof
    (OSMutex_RdyAtPrio_safe_return
       sg ls0 ptcb_pre prio_pre ls_post X Hguarantee PreH6)
    as Hsafe.
  pose proof
    (OSMutex_RdyAtPrio_owner_effect_conditional_preservation
       sg ls0 ls_post tid old_t prio_in
       H7 Htask Hsched Hevent H8 Hraw_keep)
    as Hpreserved.
  pose proof
    (OSMutex_RdyAtPrio_owner_effect_conditional_cross
       sg ls0 ls_post restore_mid tid old_t prio_in
       H7 Htask Hsched Hevent H8 Hraw_keep)
    as Hcrossed.
  assert (Hsnapshot :
    sched_ready_prio_snapshot_prop sg (TskState ls0) (SchedState ls0)
      rdy_grp_in rdyL_in prio_cur_in).
  {
    unfold sched_ready_prio_snapshot_prop.
    split; [exact Hrdygrp|].
    split; [exact Hrdytbl|exact Hpriocur].
  }
  assert (Hnewbitx :
    tcb_bitx_out = Z.shiftl 1 (Z.land prio_in 7)).
  { rewrite PreH13, PreH11. reflexivity. }
  pose proof
    (OSMutex_RdyAtPrio_owner_effect_conditional_ready_snapshot__owner_transition_return
       sg ls0 ls_post tid old_t prio_in
       rdy_grp_in rdyL_in prio_cur_in
       tcb_y_in tcb_bitx_in tcb_bity_in
       tcb_y_out tcb_bitx_out tcb_bity_out
       rdy_tbl_y_in rdy_tbl_y_out
       rdy_tbl_new_y_in rdy_tbl_new_y_out
       rdy_grp_out rdyL_out
       H7 Htask Hsched Hevent H8 Hsnapshot
       Holdy Holdbitx Holdbity PreH10 Hnewbitx PreH12
       PreH7 PreH14 PreH15 PreH16 PreH17 PreH18 Hraw_keep)
    as Hready_snapshot.
  assert (Hpost_task_snapshot :
    task_rdy_snapshot_of_prop sg (TskState ls_post) tid new_t pt prio_in
      tcb_x_out tcb_y_out tcb_bitx_out tcb_bity_out).
  {
    unfold task_rdy_snapshot_of_prop.
    repeat split.
    - rewrite Hpost. cbn. rewrite Z.eqb_refl. reflexivity.
    - exact Hpt.
    - rewrite Hnew. reflexivity.
    - rewrite Hnew, PreH11. exact Hencx.
    - rewrite Hnew, PreH10. exact Hency.
    - rewrite Hnew, PreH13, PreH11.
      unfold tcb_bit_x_of_prio. rewrite Hencx. reflexivity.
    - rewrite Hnew, PreH12, PreH10.
      unfold tcb_bit_y_of_prio. rewrite Hency. reflexivity.
  }
  assert (Hpost_priotbl :
    prio_tbl_list_rel sg (TskState ls_post) prioL_out).
  {
    rewrite PreH19, Hpt.
    eapply debug_priotbl_rel_update_task__relocation_semantics.
    - exact H7.
    - exact H0.
    - rewrite Hpost. reflexivity.
    - exact H11.
  }
  first
    [ assert (Hcurvalue :
        ready_owner_cur_prio_value_after (SchedState ls0) tid prio_in =
          prio_cur_in)
      by (
        unfold ready_owner_cur_prio_value_after,
          ready_owner_cur_prio_after;
        destruct (curTaskID (SchedState ls0))
          as [current_tid |] eqn:Hcurtid;
        [ assert (Hne : current_tid <> tid)
          by (
            intro Heq; subst current_tid; apply PreH1;
            rewrite Hpt, H1; reflexivity);
          rewrite (proj2 (Z.eqb_neq current_tid tid) Hne);
          rewrite Hpriocur; reflexivity
        | rewrite Hpriocur; reflexivity ])
    | assert (Hcurvalue :
        ready_owner_cur_prio_value_after (SchedState ls0) tid prio_in =
          prio_in)
      by (
        unfold ready_owner_cur_prio_value_after,
          ready_owner_cur_prio_after;
        destruct (curTaskID (SchedState ls0))
          as [current_tid |] eqn:Hcurtid;
        [ assert (Heq : current_tid = tid)
          by (
            unfold tcb_addr, sizeof_OS_TCB in H1, Hpt;
            lia);
          subst current_tid;
          rewrite Z.eqb_refl; reflexivity
        | exfalso; apply PreH5;
          rewrite PreH1, H1; reflexivity ])
    ].
  pose proof Htask as Htask_parts.
  unfold task_vaild_cond_prop in Htask_parts.
  destruct Htask_parts as (Htask_global & Htask_derived).
  unfold valid_GlobTaskAbstractState, task_in_range in Htask_global.
  destruct Htask_global as
    (_ & _ & _ & _ & _ & _ & Htask_unique).
  pose proof Hsched as Hsched_parts.
  unfold sched_in_range in Hsched_parts.
  destruct Hsched_parts as
    (_ & _ & _ & Hready_nodup & _ & _ & _).
  pose proof H7 as Hsg_parts.
  unfold valid_stable_glob_vars in Hsg_parts.
  destruct Hsg_parts as (_ & _ & _ & _ & _ & Hlowest & _).
  pose proof H0 as Hprio_bounds.
  unfold valid_priority_index in Hprio_bounds.
  rewrite Hlowest in Hprio_bounds.
  destruct Hrdytbl as (Hrdylen & Hrdynth).
  destruct H11 as (Hpriolen & Hprionth).
  assert (Hnewxrange : 0 <= tcb_x_out < 8).
  {
    rewrite PreH11, Hencx.
    unfold tcb_x_of_prio.
    apply Z.mod_pos_bound. lia.
  }
  assert (Hnewyrange : 0 <= tcb_y_out < 8).
  {
    rewrite PreH10, Hency.
    unfold tcb_y_of_prio.
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia.
  }
  assert (Hrdybyte : forall y, 0 <= y < 8 ->
    0 <= Znth y rdyL_in 0 < 2 ^ 8).
  {
    intros y Hy.
    rewrite Hrdynth by exact Hy.
    apply debug_encode_tbl_byte__relocation_semantics.
    - exact Hready_nodup.
    - exact Htask_unique.
    - intros tid0 t0 Hin Hget0.
      destruct (Htask_derived tid0 t0 Hget0) as (Hvalid0 & _).
      exact (proj1 Hvalid0).
  }
  assert (Hrdygrpbyte : 0 <= rdy_grp_in < 2 ^ 8).
  {
    rewrite Hrdygrp.
    apply debug_encode_grp_byte__relocation_semantics.
    intros tid0 t0 Hin Hget0.
    destruct (Htask_derived tid0 t0 Hget0) as (_ & Hderived0).
    unfold valid_derived_fields in Hderived0.
    tauto.
  }
  assert (Hunsignedgrp :
    unsigned_last_nbits rdy_grp_in 8 = rdy_grp_in).
  { apply unsigned_last_nbits_eq. exact Hrdygrpbyte. }
  assert (Hbitxbyte :
    0 <= Z.shiftl 1 (Z.land prio_pre 7) < 2 ^ 8).
  {
    rewrite PreH3, <- PreH11.
    apply debug_shiftl_bit_byte__relocation_semantics.
    exact Hnewxrange.
  }
  assert (Hbitybyte :
    0 <= Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7) < 2 ^ 8).
  {
    rewrite PreH3, <- PreH10.
    apply debug_shiftl_bit_byte__relocation_semantics.
    exact Hnewyrange.
  }
  assert (Hunsignedbitx :
    unsigned_last_nbits (Z.shiftl 1 (Z.land prio_pre 7)) 8 =
      tcb_bitx_out).
  {
    rewrite unsigned_last_nbits_eq by exact Hbitxbyte.
    rewrite PreH3, PreH13, PreH11. reflexivity.
  }
  assert (Hunsignedbity :
    unsigned_last_nbits
      (Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7)) 8 =
      tcb_bity_out).
  {
    rewrite unsigned_last_nbits_eq by exact Hbitybyte.
    rewrite PreH3, PreH12, PreH10. reflexivity.
  }
  assert (Holdrowbyte : 0 <= rdy_tbl_y_in < 2 ^ 8).
  { rewrite <- PreH7. apply Hrdybyte. lia. }
  assert (Hunsignedcleared :
    unsigned_last_nbits rdy_tbl_y_out 8 = rdy_tbl_y_out).
  {
    rewrite PreH14.
    apply unsigned_last_nbits_land_missing_l; [lia|exact Holdrowbyte].
  }
  assert (Hclearedbyte : 0 <= rdy_tbl_y_out < 2 ^ 8).
  {
    pose proof (unsigned_Lastnbits_range rdy_tbl_y_out 8 ltac:(lia))
      as Hclearedrange.
    rewrite Hunsignedcleared in Hclearedrange.
    exact Hclearedrange.
  }
  assert (Hnewinputbyte : 0 <= rdy_tbl_new_y_in < 2 ^ 8).
  {
    rewrite PreH16.
    rewrite (debug_zlist_replace__relocation_semantics
      rdyL_in tcb_y_in rdy_tbl_y_out tcb_y_out).
    - destruct (Z.eqb tcb_y_in tcb_y_out); [exact Hclearedbyte|].
      apply Hrdybyte. exact Hnewyrange.
    - rewrite Hrdylen. unfold OS_RDY_TBL_SIZE. lia.
    - rewrite Hrdylen. unfold OS_RDY_TBL_SIZE. exact Hnewyrange.
  }
  assert (Hunsignednewinput :
    unsigned_last_nbits rdy_tbl_new_y_in 8 = rdy_tbl_new_y_in).
  { apply unsigned_last_nbits_eq. exact Hnewinputbyte. }
  assert (Hrdycell :
    Z.lor (unsigned_last_nbits rdy_tbl_new_y_in 8)
      (unsigned_last_nbits (Z.shiftl 1 (Z.land prio_pre 7)) 8) =
    rdy_tbl_new_y_out).
  {
    rewrite Hunsignednewinput, Hunsignedbitx.
    symmetry. exact PreH17.
  }
  first
    [ assert (Hrdyoutne : rdy_tbl_y_out <> 0)
      by (rewrite PreH14; exact PreH2);
      assert (Hgroupcell :
        Z.lor (unsigned_last_nbits rdy_grp_in 8)
          (unsigned_last_nbits
            (Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7)) 8) =
        rdy_grp_out)
      by (
        rewrite Hunsignedgrp, Hunsignedbity, PreH15;
        unfold ready_group_after_relocation;
        rewrite (proj2 (Z.eqb_neq rdy_tbl_y_out 0) Hrdyoutne);
        reflexivity)
    | assert (Hrdyoutzero : rdy_tbl_y_out = 0)
      by (rewrite PreH14; exact PreH2);
      assert (Hgroupcell :
        Z.lor
          (Z.land rdy_grp_in
            (unsigned_last_nbits (Z.lnot tcb_bity_in) 8))
          (unsigned_last_nbits
            (Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7)) 8) =
        rdy_grp_out)
      by (
        rewrite Hunsignedbity, PreH15;
        unfold ready_group_after_relocation;
        rewrite (proj2 (Z.eqb_eq rdy_tbl_y_out 0) Hrdyoutzero);
        reflexivity)
    ].
  assert (Hprioindex : priotbl_index_in_range prio_in).
  {
    unfold priotbl_index_in_range, OS_PRIO_TBL_SIZE.
    lia.
  }
  assert (Hrdyindex : osrdytbl_index_in_range tcb_y_out).
  {
    unfold osrdytbl_index_in_range, OS_RDY_TBL_SIZE.
    exact Hnewyrange.
  }
  assert (Hinterlen :
    Zlength (replace_Znth tcb_y_in rdy_tbl_y_out rdyL_in) =
      OS_RDY_TBL_SIZE).
  {
    rewrite Zlength_replace_Znth, Hrdylen. reflexivity.
  }
  assert (Hprioout :
    prioL_out = replace_Znth prio_in (tcb_addr sg tid) prioL_in).
  { rewrite <- Hpt. exact PreH19. }
  Exists new_t ls_post.
  unfold OSMutex_RdyAtPrio_raw_stage.
  rewrite Hprioaddr, Hxaddr, Hyaddr, Hbitxaddr, Hbityaddr, Hpt.
  rewrite H12, H10, H6, H5.
  rewrite Hrdycell, Hgroupcell.
  rewrite Hunsignedbitx, Hunsignedbity, PreH3.
  rewrite <- PreH11.
  rewrite Hcurvalue.
  rewrite Hprioout.
  sep_apply_l_atomic
    (debug_store_priotbl_merge_c_cell__relocation_semantics
       sg prioL_in prio_in (tcb_addr sg tid) Hprioindex Hpriolen).
  sep_apply_l_atomic
    (debug_store_osrdytbl_merge_c_cell__relocation_semantics
       sg (replace_Znth tcb_y_in rdy_tbl_y_out rdyL_in)
       tcb_y_out rdy_tbl_new_y_out Hrdyindex Hinterlen).
  rewrite <- PreH18.
  repeat rewrite
    Ucos2Verify.lib.mutex_rdyatprio_spec.OSMutex_RdyAtPrio_truep_contract_across__return_transition_rebuild.
  entailer!.
  - repeat lazymatch goal with
    | |- ?L |-- TT ** ?R =>
        apply
          (Ucos2Verify.lib.mutex_rdyatprio_spec.OSMutex_RdyAtPrio_entail_add_truep__return_transition_rebuild
             L R)
    end.
    entailer!.
  - rewrite <- PreH3. exact Hguarantee.
  - rewrite <- Hpt. exact Hpost_task_snapshot.
  - rewrite <- Hprioout. exact Hpost_priotbl.
  - rewrite <- PreH3. exact Hsafe.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_return_wit_3_current_owner : OSMutex_RdyAtPrio_full_return_wit_3_current_owner.
Proof.
  pre_process.
  unfold task_rdy_snapshot_of_prop in H3.
  destruct H3 as
    (Hget & Hpt & Holdprio & Holdx & Holdy & Holdbitx & Holdbity).
  unfold task_priority_fields_layout_prop in H2.
  destruct H2 as (Hprioaddr & Hxaddr & Hyaddr & Hbitxaddr & Hbityaddr).
  unfold sched_tcb_cur_snapshot_prop in H1.
  unfold os_tcb_cur_addr in H4.
  unfold os_prio_cur_addr in H5.
  unfold os_rdy_grp_addr in H6.
  unfold os_rdy_tbl_addr in H10.
  unfold os_tcb_prio_tbl_addr in H12.
  destruct H9 as (Hrdygrp & Hrdytbl & Hpriocur).
  rewrite H4.
  sep_apply_l_atomic
    (Ucos2Verify.lib.mutex_rdyatprio_spec.OSMutex_RdyAtPrio_sched_rest_fold__return_transition_rebuild
       sg (TskState ls0) (SchedState ls0) tcbcur_in H1).
  sep_apply_l_atomic
    (debug_extract_relocation_validities__relocation_semantics sg ls0 tid).
  Intros_p Hvalids.
  destruct Hvalids as (Htask & Hsched & Hevent).
  pose proof
    (debug_priority_encoding__relocation_semantics sg prio_in H7 H0)
    as (Hencx & Hency & Hencbitx & Hencbity).
  destruct
    (OSMutex_RdyAtPrio_ready_owner_transition_exists
       sg ls0 tid old_t prio_in H)
    as (new_t_ignored & ls_post & Hraw).
  clear new_t_ignored.
  pose proof Hraw as Hraw_keep.
  unfold atomic_task_set_curPrio_ready_owner_exec in Hraw.
  destruct Hraw as
    (new_t & Hraw_in & Hraw_get & Hraw_lo & Hraw_hi & Hnew & Hpost).
  assert (Hguarantee :
    OSMutex_RdyAtPrio_guarantee sg ptcb_pre prio_pre ls0 ls_post).
  {
    unfold OSMutex_RdyAtPrio_guarantee, OSMutex_RdyAtPrio_sem.
    exists tid, old_t.
    split.
    - rewrite <- PreH4. exact Hpt.
    - split.
      + rewrite PreH3. exact H.
      + rewrite PreH3. exact Hraw_keep.
  }
  pose proof
    (OSMutex_RdyAtPrio_safe_return
       sg ls0 ptcb_pre prio_pre ls_post X Hguarantee PreH6)
    as Hsafe.
  pose proof
    (OSMutex_RdyAtPrio_owner_effect_conditional_preservation
       sg ls0 ls_post tid old_t prio_in
       H7 Htask Hsched Hevent H8 Hraw_keep)
    as Hpreserved.
  pose proof
    (OSMutex_RdyAtPrio_owner_effect_conditional_cross
       sg ls0 ls_post restore_mid tid old_t prio_in
       H7 Htask Hsched Hevent H8 Hraw_keep)
    as Hcrossed.
  assert (Hsnapshot :
    sched_ready_prio_snapshot_prop sg (TskState ls0) (SchedState ls0)
      rdy_grp_in rdyL_in prio_cur_in).
  {
    unfold sched_ready_prio_snapshot_prop.
    split; [exact Hrdygrp|].
    split; [exact Hrdytbl|exact Hpriocur].
  }
  assert (Hnewbitx :
    tcb_bitx_out = Z.shiftl 1 (Z.land prio_in 7)).
  { rewrite PreH13, PreH11. reflexivity. }
  pose proof
    (OSMutex_RdyAtPrio_owner_effect_conditional_ready_snapshot__owner_transition_return
       sg ls0 ls_post tid old_t prio_in
       rdy_grp_in rdyL_in prio_cur_in
       tcb_y_in tcb_bitx_in tcb_bity_in
       tcb_y_out tcb_bitx_out tcb_bity_out
       rdy_tbl_y_in rdy_tbl_y_out
       rdy_tbl_new_y_in rdy_tbl_new_y_out
       rdy_grp_out rdyL_out
       H7 Htask Hsched Hevent H8 Hsnapshot
       Holdy Holdbitx Holdbity PreH10 Hnewbitx PreH12
       PreH7 PreH14 PreH15 PreH16 PreH17 PreH18 Hraw_keep)
    as Hready_snapshot.
  assert (Hpost_task_snapshot :
    task_rdy_snapshot_of_prop sg (TskState ls_post) tid new_t pt prio_in
      tcb_x_out tcb_y_out tcb_bitx_out tcb_bity_out).
  {
    unfold task_rdy_snapshot_of_prop.
    repeat split.
    - rewrite Hpost. cbn. rewrite Z.eqb_refl. reflexivity.
    - exact Hpt.
    - rewrite Hnew. reflexivity.
    - rewrite Hnew, PreH11. exact Hencx.
    - rewrite Hnew, PreH10. exact Hency.
    - rewrite Hnew, PreH13, PreH11.
      unfold tcb_bit_x_of_prio. rewrite Hencx. reflexivity.
    - rewrite Hnew, PreH12, PreH10.
      unfold tcb_bit_y_of_prio. rewrite Hency. reflexivity.
  }
  assert (Hpost_priotbl :
    prio_tbl_list_rel sg (TskState ls_post) prioL_out).
  {
    rewrite PreH19, Hpt.
    eapply debug_priotbl_rel_update_task__relocation_semantics.
    - exact H7.
    - exact H0.
    - rewrite Hpost. reflexivity.
    - exact H11.
  }
  first
    [ assert (Hcurvalue :
        ready_owner_cur_prio_value_after (SchedState ls0) tid prio_in =
          prio_cur_in)
      by (
        unfold ready_owner_cur_prio_value_after,
          ready_owner_cur_prio_after;
        destruct (curTaskID (SchedState ls0))
          as [current_tid |] eqn:Hcurtid;
        [ assert (Hne : current_tid <> tid)
          by (
            intro Heq; subst current_tid; apply PreH1;
            rewrite Hpt, H1; reflexivity);
          rewrite (proj2 (Z.eqb_neq current_tid tid) Hne);
          rewrite Hpriocur; reflexivity
        | rewrite Hpriocur; reflexivity ])
    | assert (Hcurvalue :
        ready_owner_cur_prio_value_after (SchedState ls0) tid prio_in =
          prio_in)
      by (
        unfold ready_owner_cur_prio_value_after,
          ready_owner_cur_prio_after;
        destruct (curTaskID (SchedState ls0))
          as [current_tid |] eqn:Hcurtid;
        [ assert (Heq : current_tid = tid)
          by (
            unfold tcb_addr, sizeof_OS_TCB in H1, Hpt;
            lia);
          subst current_tid;
          rewrite Z.eqb_refl; reflexivity
        | exfalso; apply PreH5;
          rewrite PreH1, H1; reflexivity ])
    ].
  pose proof Htask as Htask_parts.
  unfold task_vaild_cond_prop in Htask_parts.
  destruct Htask_parts as (Htask_global & Htask_derived).
  unfold valid_GlobTaskAbstractState, task_in_range in Htask_global.
  destruct Htask_global as
    (_ & _ & _ & _ & _ & _ & Htask_unique).
  pose proof Hsched as Hsched_parts.
  unfold sched_in_range in Hsched_parts.
  destruct Hsched_parts as
    (_ & _ & _ & Hready_nodup & _ & _ & _).
  pose proof H7 as Hsg_parts.
  unfold valid_stable_glob_vars in Hsg_parts.
  destruct Hsg_parts as (_ & _ & _ & _ & _ & Hlowest & _).
  pose proof H0 as Hprio_bounds.
  unfold valid_priority_index in Hprio_bounds.
  rewrite Hlowest in Hprio_bounds.
  destruct Hrdytbl as (Hrdylen & Hrdynth).
  destruct H11 as (Hpriolen & Hprionth).
  assert (Hnewxrange : 0 <= tcb_x_out < 8).
  {
    rewrite PreH11, Hencx.
    unfold tcb_x_of_prio.
    apply Z.mod_pos_bound. lia.
  }
  assert (Hnewyrange : 0 <= tcb_y_out < 8).
  {
    rewrite PreH10, Hency.
    unfold tcb_y_of_prio.
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia.
  }
  assert (Hrdybyte : forall y, 0 <= y < 8 ->
    0 <= Znth y rdyL_in 0 < 2 ^ 8).
  {
    intros y Hy.
    rewrite Hrdynth by exact Hy.
    apply debug_encode_tbl_byte__relocation_semantics.
    - exact Hready_nodup.
    - exact Htask_unique.
    - intros tid0 t0 Hin Hget0.
      destruct (Htask_derived tid0 t0 Hget0) as (Hvalid0 & _).
      exact (proj1 Hvalid0).
  }
  assert (Hrdygrpbyte : 0 <= rdy_grp_in < 2 ^ 8).
  {
    rewrite Hrdygrp.
    apply debug_encode_grp_byte__relocation_semantics.
    intros tid0 t0 Hin Hget0.
    destruct (Htask_derived tid0 t0 Hget0) as (_ & Hderived0).
    unfold valid_derived_fields in Hderived0.
    tauto.
  }
  assert (Hunsignedgrp :
    unsigned_last_nbits rdy_grp_in 8 = rdy_grp_in).
  { apply unsigned_last_nbits_eq. exact Hrdygrpbyte. }
  assert (Hbitxbyte :
    0 <= Z.shiftl 1 (Z.land prio_pre 7) < 2 ^ 8).
  {
    rewrite PreH3, <- PreH11.
    apply debug_shiftl_bit_byte__relocation_semantics.
    exact Hnewxrange.
  }
  assert (Hbitybyte :
    0 <= Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7) < 2 ^ 8).
  {
    rewrite PreH3, <- PreH10.
    apply debug_shiftl_bit_byte__relocation_semantics.
    exact Hnewyrange.
  }
  assert (Hunsignedbitx :
    unsigned_last_nbits (Z.shiftl 1 (Z.land prio_pre 7)) 8 =
      tcb_bitx_out).
  {
    rewrite unsigned_last_nbits_eq by exact Hbitxbyte.
    rewrite PreH3, PreH13, PreH11. reflexivity.
  }
  assert (Hunsignedbity :
    unsigned_last_nbits
      (Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7)) 8 =
      tcb_bity_out).
  {
    rewrite unsigned_last_nbits_eq by exact Hbitybyte.
    rewrite PreH3, PreH12, PreH10. reflexivity.
  }
  assert (Holdrowbyte : 0 <= rdy_tbl_y_in < 2 ^ 8).
  { rewrite <- PreH7. apply Hrdybyte. lia. }
  assert (Hunsignedcleared :
    unsigned_last_nbits rdy_tbl_y_out 8 = rdy_tbl_y_out).
  {
    rewrite PreH14.
    apply unsigned_last_nbits_land_missing_l; [lia|exact Holdrowbyte].
  }
  assert (Hclearedbyte : 0 <= rdy_tbl_y_out < 2 ^ 8).
  {
    pose proof (unsigned_Lastnbits_range rdy_tbl_y_out 8 ltac:(lia))
      as Hclearedrange.
    rewrite Hunsignedcleared in Hclearedrange.
    exact Hclearedrange.
  }
  assert (Hnewinputbyte : 0 <= rdy_tbl_new_y_in < 2 ^ 8).
  {
    rewrite PreH16.
    rewrite (debug_zlist_replace__relocation_semantics
      rdyL_in tcb_y_in rdy_tbl_y_out tcb_y_out).
    - destruct (Z.eqb tcb_y_in tcb_y_out); [exact Hclearedbyte|].
      apply Hrdybyte. exact Hnewyrange.
    - rewrite Hrdylen. unfold OS_RDY_TBL_SIZE. lia.
    - rewrite Hrdylen. unfold OS_RDY_TBL_SIZE. exact Hnewyrange.
  }
  assert (Hunsignednewinput :
    unsigned_last_nbits rdy_tbl_new_y_in 8 = rdy_tbl_new_y_in).
  { apply unsigned_last_nbits_eq. exact Hnewinputbyte. }
  assert (Hrdycell :
    Z.lor (unsigned_last_nbits rdy_tbl_new_y_in 8)
      (unsigned_last_nbits (Z.shiftl 1 (Z.land prio_pre 7)) 8) =
    rdy_tbl_new_y_out).
  {
    rewrite Hunsignednewinput, Hunsignedbitx.
    symmetry. exact PreH17.
  }
  first
    [ assert (Hrdyoutne : rdy_tbl_y_out <> 0)
      by (rewrite PreH14; exact PreH2);
      assert (Hgroupcell :
        Z.lor (unsigned_last_nbits rdy_grp_in 8)
          (unsigned_last_nbits
            (Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7)) 8) =
        rdy_grp_out)
      by (
        rewrite Hunsignedgrp, Hunsignedbity, PreH15;
        unfold ready_group_after_relocation;
        rewrite (proj2 (Z.eqb_neq rdy_tbl_y_out 0) Hrdyoutne);
        reflexivity)
    | assert (Hrdyoutzero : rdy_tbl_y_out = 0)
      by (rewrite PreH14; exact PreH2);
      assert (Hgroupcell :
        Z.lor
          (Z.land rdy_grp_in
            (unsigned_last_nbits (Z.lnot tcb_bity_in) 8))
          (unsigned_last_nbits
            (Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7)) 8) =
        rdy_grp_out)
      by (
        rewrite Hunsignedbity, PreH15;
        unfold ready_group_after_relocation;
        rewrite (proj2 (Z.eqb_eq rdy_tbl_y_out 0) Hrdyoutzero);
        reflexivity)
    ].
  assert (Hprioindex : priotbl_index_in_range prio_in).
  {
    unfold priotbl_index_in_range, OS_PRIO_TBL_SIZE.
    lia.
  }
  assert (Hrdyindex : osrdytbl_index_in_range tcb_y_out).
  {
    unfold osrdytbl_index_in_range, OS_RDY_TBL_SIZE.
    exact Hnewyrange.
  }
  assert (Hinterlen :
    Zlength (replace_Znth tcb_y_in rdy_tbl_y_out rdyL_in) =
      OS_RDY_TBL_SIZE).
  {
    rewrite Zlength_replace_Znth, Hrdylen. reflexivity.
  }
  assert (Hprioout :
    prioL_out = replace_Znth prio_in (tcb_addr sg tid) prioL_in).
  { rewrite <- Hpt. exact PreH19. }
  Exists new_t ls_post.
  unfold OSMutex_RdyAtPrio_raw_stage.
  rewrite Hprioaddr, Hxaddr, Hyaddr, Hbitxaddr, Hbityaddr, Hpt.
  rewrite H12, H10, H6, H5.
  rewrite Hrdycell, Hgroupcell.
  rewrite Hunsignedbitx, Hunsignedbity, PreH3.
  rewrite <- PreH11.
  rewrite Hcurvalue.
  rewrite Hprioout.
  sep_apply_l_atomic
    (debug_store_priotbl_merge_c_cell__relocation_semantics
       sg prioL_in prio_in (tcb_addr sg tid) Hprioindex Hpriolen).
  sep_apply_l_atomic
    (debug_store_osrdytbl_merge_c_cell__relocation_semantics
       sg (replace_Znth tcb_y_in rdy_tbl_y_out rdyL_in)
       tcb_y_out rdy_tbl_new_y_out Hrdyindex Hinterlen).
  rewrite <- PreH18.
  repeat rewrite
    Ucos2Verify.lib.mutex_rdyatprio_spec.OSMutex_RdyAtPrio_truep_contract_across__return_transition_rebuild.
  entailer!.
  - repeat lazymatch goal with
    | |- ?L |-- TT ** ?R =>
        apply
          (Ucos2Verify.lib.mutex_rdyatprio_spec.OSMutex_RdyAtPrio_entail_add_truep__return_transition_rebuild
             L R)
    end.
    entailer!.
  - rewrite <- PreH3. exact Hguarantee.
  - rewrite <- Hpt. exact Hpost_task_snapshot.
  - rewrite <- Hprioout. exact Hpost_priotbl.
  - rewrite <- PreH3. exact Hsafe.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_return_wit_4_current_owner : OSMutex_RdyAtPrio_full_return_wit_4_current_owner.
Proof.
  pre_process.
  unfold task_rdy_snapshot_of_prop in H3.
  destruct H3 as
    (Hget & Hpt & Holdprio & Holdx & Holdy & Holdbitx & Holdbity).
  unfold task_priority_fields_layout_prop in H2.
  destruct H2 as (Hprioaddr & Hxaddr & Hyaddr & Hbitxaddr & Hbityaddr).
  unfold sched_tcb_cur_snapshot_prop in H1.
  unfold os_tcb_cur_addr in H4.
  unfold os_prio_cur_addr in H5.
  unfold os_rdy_grp_addr in H6.
  unfold os_rdy_tbl_addr in H10.
  unfold os_tcb_prio_tbl_addr in H12.
  destruct H9 as (Hrdygrp & Hrdytbl & Hpriocur).
  rewrite H4.
  sep_apply_l_atomic
    (Ucos2Verify.lib.mutex_rdyatprio_spec.OSMutex_RdyAtPrio_sched_rest_fold__return_transition_rebuild
       sg (TskState ls0) (SchedState ls0) tcbcur_in H1).
  sep_apply_l_atomic
    (debug_extract_relocation_validities__relocation_semantics sg ls0 tid).
  Intros_p Hvalids.
  destruct Hvalids as (Htask & Hsched & Hevent).
  pose proof
    (debug_priority_encoding__relocation_semantics sg prio_in H7 H0)
    as (Hencx & Hency & Hencbitx & Hencbity).
  destruct
    (OSMutex_RdyAtPrio_ready_owner_transition_exists
       sg ls0 tid old_t prio_in H)
    as (new_t_ignored & ls_post & Hraw).
  clear new_t_ignored.
  pose proof Hraw as Hraw_keep.
  unfold atomic_task_set_curPrio_ready_owner_exec in Hraw.
  destruct Hraw as
    (new_t & Hraw_in & Hraw_get & Hraw_lo & Hraw_hi & Hnew & Hpost).
  assert (Hguarantee :
    OSMutex_RdyAtPrio_guarantee sg ptcb_pre prio_pre ls0 ls_post).
  {
    unfold OSMutex_RdyAtPrio_guarantee, OSMutex_RdyAtPrio_sem.
    exists tid, old_t.
    split.
    - rewrite <- PreH4. exact Hpt.
    - split.
      + rewrite PreH3. exact H.
      + rewrite PreH3. exact Hraw_keep.
  }
  pose proof
    (OSMutex_RdyAtPrio_safe_return
       sg ls0 ptcb_pre prio_pre ls_post X Hguarantee PreH6)
    as Hsafe.
  pose proof
    (OSMutex_RdyAtPrio_owner_effect_conditional_preservation
       sg ls0 ls_post tid old_t prio_in
       H7 Htask Hsched Hevent H8 Hraw_keep)
    as Hpreserved.
  pose proof
    (OSMutex_RdyAtPrio_owner_effect_conditional_cross
       sg ls0 ls_post restore_mid tid old_t prio_in
       H7 Htask Hsched Hevent H8 Hraw_keep)
    as Hcrossed.
  assert (Hsnapshot :
    sched_ready_prio_snapshot_prop sg (TskState ls0) (SchedState ls0)
      rdy_grp_in rdyL_in prio_cur_in).
  {
    unfold sched_ready_prio_snapshot_prop.
    split; [exact Hrdygrp|].
    split; [exact Hrdytbl|exact Hpriocur].
  }
  assert (Hnewbitx :
    tcb_bitx_out = Z.shiftl 1 (Z.land prio_in 7)).
  { rewrite PreH13, PreH11. reflexivity. }
  pose proof
    (OSMutex_RdyAtPrio_owner_effect_conditional_ready_snapshot__owner_transition_return
       sg ls0 ls_post tid old_t prio_in
       rdy_grp_in rdyL_in prio_cur_in
       tcb_y_in tcb_bitx_in tcb_bity_in
       tcb_y_out tcb_bitx_out tcb_bity_out
       rdy_tbl_y_in rdy_tbl_y_out
       rdy_tbl_new_y_in rdy_tbl_new_y_out
       rdy_grp_out rdyL_out
       H7 Htask Hsched Hevent H8 Hsnapshot
       Holdy Holdbitx Holdbity PreH10 Hnewbitx PreH12
       PreH7 PreH14 PreH15 PreH16 PreH17 PreH18 Hraw_keep)
    as Hready_snapshot.
  assert (Hpost_task_snapshot :
    task_rdy_snapshot_of_prop sg (TskState ls_post) tid new_t pt prio_in
      tcb_x_out tcb_y_out tcb_bitx_out tcb_bity_out).
  {
    unfold task_rdy_snapshot_of_prop.
    repeat split.
    - rewrite Hpost. cbn. rewrite Z.eqb_refl. reflexivity.
    - exact Hpt.
    - rewrite Hnew. reflexivity.
    - rewrite Hnew, PreH11. exact Hencx.
    - rewrite Hnew, PreH10. exact Hency.
    - rewrite Hnew, PreH13, PreH11.
      unfold tcb_bit_x_of_prio. rewrite Hencx. reflexivity.
    - rewrite Hnew, PreH12, PreH10.
      unfold tcb_bit_y_of_prio. rewrite Hency. reflexivity.
  }
  assert (Hpost_priotbl :
    prio_tbl_list_rel sg (TskState ls_post) prioL_out).
  {
    rewrite PreH19, Hpt.
    eapply debug_priotbl_rel_update_task__relocation_semantics.
    - exact H7.
    - exact H0.
    - rewrite Hpost. reflexivity.
    - exact H11.
  }
  first
    [ assert (Hcurvalue :
        ready_owner_cur_prio_value_after (SchedState ls0) tid prio_in =
          prio_cur_in)
      by (
        unfold ready_owner_cur_prio_value_after,
          ready_owner_cur_prio_after;
        destruct (curTaskID (SchedState ls0))
          as [current_tid |] eqn:Hcurtid;
        [ assert (Hne : current_tid <> tid)
          by (
            intro Heq; subst current_tid; apply PreH1;
            rewrite Hpt, H1; reflexivity);
          rewrite (proj2 (Z.eqb_neq current_tid tid) Hne);
          rewrite Hpriocur; reflexivity
        | rewrite Hpriocur; reflexivity ])
    | assert (Hcurvalue :
        ready_owner_cur_prio_value_after (SchedState ls0) tid prio_in =
          prio_in)
      by (
        unfold ready_owner_cur_prio_value_after,
          ready_owner_cur_prio_after;
        destruct (curTaskID (SchedState ls0))
          as [current_tid |] eqn:Hcurtid;
        [ assert (Heq : current_tid = tid)
          by (
            unfold tcb_addr, sizeof_OS_TCB in H1, Hpt;
            lia);
          subst current_tid;
          rewrite Z.eqb_refl; reflexivity
        | exfalso; apply PreH5;
          rewrite PreH1, H1; reflexivity ])
    ].
  pose proof Htask as Htask_parts.
  unfold task_vaild_cond_prop in Htask_parts.
  destruct Htask_parts as (Htask_global & Htask_derived).
  unfold valid_GlobTaskAbstractState, task_in_range in Htask_global.
  destruct Htask_global as
    (_ & _ & _ & _ & _ & _ & Htask_unique).
  pose proof Hsched as Hsched_parts.
  unfold sched_in_range in Hsched_parts.
  destruct Hsched_parts as
    (_ & _ & _ & Hready_nodup & _ & _ & _).
  pose proof H7 as Hsg_parts.
  unfold valid_stable_glob_vars in Hsg_parts.
  destruct Hsg_parts as (_ & _ & _ & _ & _ & Hlowest & _).
  pose proof H0 as Hprio_bounds.
  unfold valid_priority_index in Hprio_bounds.
  rewrite Hlowest in Hprio_bounds.
  destruct Hrdytbl as (Hrdylen & Hrdynth).
  destruct H11 as (Hpriolen & Hprionth).
  assert (Hnewxrange : 0 <= tcb_x_out < 8).
  {
    rewrite PreH11, Hencx.
    unfold tcb_x_of_prio.
    apply Z.mod_pos_bound. lia.
  }
  assert (Hnewyrange : 0 <= tcb_y_out < 8).
  {
    rewrite PreH10, Hency.
    unfold tcb_y_of_prio.
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia.
  }
  assert (Hrdybyte : forall y, 0 <= y < 8 ->
    0 <= Znth y rdyL_in 0 < 2 ^ 8).
  {
    intros y Hy.
    rewrite Hrdynth by exact Hy.
    apply debug_encode_tbl_byte__relocation_semantics.
    - exact Hready_nodup.
    - exact Htask_unique.
    - intros tid0 t0 Hin Hget0.
      destruct (Htask_derived tid0 t0 Hget0) as (Hvalid0 & _).
      exact (proj1 Hvalid0).
  }
  assert (Hrdygrpbyte : 0 <= rdy_grp_in < 2 ^ 8).
  {
    rewrite Hrdygrp.
    apply debug_encode_grp_byte__relocation_semantics.
    intros tid0 t0 Hin Hget0.
    destruct (Htask_derived tid0 t0 Hget0) as (_ & Hderived0).
    unfold valid_derived_fields in Hderived0.
    tauto.
  }
  assert (Hunsignedgrp :
    unsigned_last_nbits rdy_grp_in 8 = rdy_grp_in).
  { apply unsigned_last_nbits_eq. exact Hrdygrpbyte. }
  assert (Hbitxbyte :
    0 <= Z.shiftl 1 (Z.land prio_pre 7) < 2 ^ 8).
  {
    rewrite PreH3, <- PreH11.
    apply debug_shiftl_bit_byte__relocation_semantics.
    exact Hnewxrange.
  }
  assert (Hbitybyte :
    0 <= Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7) < 2 ^ 8).
  {
    rewrite PreH3, <- PreH10.
    apply debug_shiftl_bit_byte__relocation_semantics.
    exact Hnewyrange.
  }
  assert (Hunsignedbitx :
    unsigned_last_nbits (Z.shiftl 1 (Z.land prio_pre 7)) 8 =
      tcb_bitx_out).
  {
    rewrite unsigned_last_nbits_eq by exact Hbitxbyte.
    rewrite PreH3, PreH13, PreH11. reflexivity.
  }
  assert (Hunsignedbity :
    unsigned_last_nbits
      (Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7)) 8 =
      tcb_bity_out).
  {
    rewrite unsigned_last_nbits_eq by exact Hbitybyte.
    rewrite PreH3, PreH12, PreH10. reflexivity.
  }
  assert (Holdrowbyte : 0 <= rdy_tbl_y_in < 2 ^ 8).
  { rewrite <- PreH7. apply Hrdybyte. lia. }
  assert (Hunsignedcleared :
    unsigned_last_nbits rdy_tbl_y_out 8 = rdy_tbl_y_out).
  {
    rewrite PreH14.
    apply unsigned_last_nbits_land_missing_l; [lia|exact Holdrowbyte].
  }
  assert (Hclearedbyte : 0 <= rdy_tbl_y_out < 2 ^ 8).
  {
    pose proof (unsigned_Lastnbits_range rdy_tbl_y_out 8 ltac:(lia))
      as Hclearedrange.
    rewrite Hunsignedcleared in Hclearedrange.
    exact Hclearedrange.
  }
  assert (Hnewinputbyte : 0 <= rdy_tbl_new_y_in < 2 ^ 8).
  {
    rewrite PreH16.
    rewrite (debug_zlist_replace__relocation_semantics
      rdyL_in tcb_y_in rdy_tbl_y_out tcb_y_out).
    - destruct (Z.eqb tcb_y_in tcb_y_out); [exact Hclearedbyte|].
      apply Hrdybyte. exact Hnewyrange.
    - rewrite Hrdylen. unfold OS_RDY_TBL_SIZE. lia.
    - rewrite Hrdylen. unfold OS_RDY_TBL_SIZE. exact Hnewyrange.
  }
  assert (Hunsignednewinput :
    unsigned_last_nbits rdy_tbl_new_y_in 8 = rdy_tbl_new_y_in).
  { apply unsigned_last_nbits_eq. exact Hnewinputbyte. }
  assert (Hrdycell :
    Z.lor (unsigned_last_nbits rdy_tbl_new_y_in 8)
      (unsigned_last_nbits (Z.shiftl 1 (Z.land prio_pre 7)) 8) =
    rdy_tbl_new_y_out).
  {
    rewrite Hunsignednewinput, Hunsignedbitx.
    symmetry. exact PreH17.
  }
  first
    [ assert (Hrdyoutne : rdy_tbl_y_out <> 0)
      by (rewrite PreH14; exact PreH2);
      assert (Hgroupcell :
        Z.lor (unsigned_last_nbits rdy_grp_in 8)
          (unsigned_last_nbits
            (Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7)) 8) =
        rdy_grp_out)
      by (
        rewrite Hunsignedgrp, Hunsignedbity, PreH15;
        unfold ready_group_after_relocation;
        rewrite (proj2 (Z.eqb_neq rdy_tbl_y_out 0) Hrdyoutne);
        reflexivity)
    | assert (Hrdyoutzero : rdy_tbl_y_out = 0)
      by (rewrite PreH14; exact PreH2);
      assert (Hgroupcell :
        Z.lor
          (Z.land rdy_grp_in
            (unsigned_last_nbits (Z.lnot tcb_bity_in) 8))
          (unsigned_last_nbits
            (Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7)) 8) =
        rdy_grp_out)
      by (
        rewrite Hunsignedbity, PreH15;
        unfold ready_group_after_relocation;
        rewrite (proj2 (Z.eqb_eq rdy_tbl_y_out 0) Hrdyoutzero);
        reflexivity)
    ].
  assert (Hprioindex : priotbl_index_in_range prio_in).
  {
    unfold priotbl_index_in_range, OS_PRIO_TBL_SIZE.
    lia.
  }
  assert (Hrdyindex : osrdytbl_index_in_range tcb_y_out).
  {
    unfold osrdytbl_index_in_range, OS_RDY_TBL_SIZE.
    exact Hnewyrange.
  }
  assert (Hinterlen :
    Zlength (replace_Znth tcb_y_in rdy_tbl_y_out rdyL_in) =
      OS_RDY_TBL_SIZE).
  {
    rewrite Zlength_replace_Znth, Hrdylen. reflexivity.
  }
  assert (Hprioout :
    prioL_out = replace_Znth prio_in (tcb_addr sg tid) prioL_in).
  { rewrite <- Hpt. exact PreH19. }
  Exists new_t ls_post.
  unfold OSMutex_RdyAtPrio_raw_stage.
  rewrite Hprioaddr, Hxaddr, Hyaddr, Hbitxaddr, Hbityaddr, Hpt.
  rewrite H12, H10, H6, H5.
  rewrite Hrdycell, Hgroupcell.
  rewrite Hunsignedbitx, Hunsignedbity, PreH3.
  rewrite <- PreH11.
  rewrite Hcurvalue.
  rewrite Hprioout.
  sep_apply_l_atomic
    (debug_store_priotbl_merge_c_cell__relocation_semantics
       sg prioL_in prio_in (tcb_addr sg tid) Hprioindex Hpriolen).
  sep_apply_l_atomic
    (debug_store_osrdytbl_merge_c_cell__relocation_semantics
       sg (replace_Znth tcb_y_in rdy_tbl_y_out rdyL_in)
       tcb_y_out rdy_tbl_new_y_out Hrdyindex Hinterlen).
  rewrite <- PreH18.
  repeat rewrite
    Ucos2Verify.lib.mutex_rdyatprio_spec.OSMutex_RdyAtPrio_truep_contract_across__return_transition_rebuild.
  entailer!.
  - repeat lazymatch goal with
    | |- ?L |-- TT ** ?R =>
        apply
          (Ucos2Verify.lib.mutex_rdyatprio_spec.OSMutex_RdyAtPrio_entail_add_truep__return_transition_rebuild
             L R)
    end.
    entailer!.
  - rewrite <- PreH3. exact Hguarantee.
  - rewrite <- Hpt. exact Hpost_task_snapshot.
  - rewrite <- Hprioout. exact Hpost_priotbl.
  - rewrite <- PreH3. exact Hsafe.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_3_noncurrent_owner_pure : OSMutex_RdyAtPrio_full_partial_solve_wit_3_noncurrent_owner_pure.
Proof.
  pre_process.
  assert (Hmask : forall z, 0 <= Z.land z 7 < 8).
  {
    intro z.
    replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia.
    change (0 <= z mod 8 < 8).
    apply Z.mod_pos_bound.
    lia.
  }
  split_pures.
  - dump_pre_spatial. subst tcb_y_out. apply Hmask.
  - dump_pre_spatial. subst tcb_y_out. apply Hmask.
  - dump_pre_spatial. exact PreH16.
  - dump_pre_spatial. apply Hmask.
  - dump_pre_spatial. apply Hmask.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_4_noncurrent_owner_pure : OSMutex_RdyAtPrio_full_partial_solve_wit_4_noncurrent_owner_pure.
Proof.
  pre_process.
  assert (Hmask : forall z, 0 <= Z.land z 7 < 8).
  {
    intro z.
    replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia.
    change (0 <= z mod 8 < 8).
    apply Z.mod_pos_bound.
    lia.
  }
  split_pures.
  - dump_pre_spatial. subst tcb_y_out. apply Hmask.
  - dump_pre_spatial. subst tcb_y_out. apply Hmask.
  - dump_pre_spatial. exact PreH16.
  - dump_pre_spatial. apply Hmask.
  - dump_pre_spatial. apply Hmask.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_5_current_owner_pure : OSMutex_RdyAtPrio_full_partial_solve_wit_5_current_owner_pure.
Proof.
  pre_process.
  assert (Hmask : forall z, 0 <= Z.land z 7 < 8).
  {
    intro z.
    replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia.
    change (0 <= z mod 8 < 8).
    apply Z.mod_pos_bound.
    lia.
  }
  split_pures.
  - dump_pre_spatial. subst tcb_y_out. apply Hmask.
  - dump_pre_spatial. subst tcb_y_out. apply Hmask.
  - dump_pre_spatial. exact PreH16.
  - dump_pre_spatial. apply Hmask.
  - dump_pre_spatial. apply Hmask.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_6_current_owner_pure : OSMutex_RdyAtPrio_full_partial_solve_wit_6_current_owner_pure.
Proof.
  pre_process.
  assert (Hmask : forall z, 0 <= Z.land z 7 < 8).
  {
    intro z.
    replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia.
    change (0 <= z mod 8 < 8).
    apply Z.mod_pos_bound.
    lia.
  }
  split_pures.
  - dump_pre_spatial. subst tcb_y_out. apply Hmask.
  - dump_pre_spatial. subst tcb_y_out. apply Hmask.
  - dump_pre_spatial. exact PreH16.
  - dump_pre_spatial. apply Hmask.
  - dump_pre_spatial. apply Hmask.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_7_current_owner_pure : OSMutex_RdyAtPrio_full_partial_solve_wit_7_current_owner_pure.
Proof.
  pre_process.
  sepcon_lift (coq_prop (valid_priority_index sg prio_in)).
  match goal with
  | H : valid_priority_index _ _ |- _ => rename H into Hvalid
  end.
  match goal with
  | H : valid_stable_glob_vars _ |- _ => rename H into Hstable
  end.
  unfold valid_priority_index in Hvalid.
  destruct Hvalid as [Hprio_lo Hprio_hi].
  unfold valid_stable_glob_vars in Hstable.
  decompose [and] Hstable.
  split_pures.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_8_current_owner_pure : OSMutex_RdyAtPrio_full_partial_solve_wit_8_current_owner_pure.
Proof.
  pre_process.
  sepcon_lift (coq_prop (valid_priority_index sg prio_in)).
  match goal with
  | H : valid_priority_index _ _ |- _ => rename H into Hvalid
  end.
  match goal with
  | H : valid_stable_glob_vars _ |- _ => rename H into Hstable
  end.
  unfold valid_priority_index in Hvalid.
  destruct Hvalid as [Hprio_lo Hprio_hi].
  unfold valid_stable_glob_vars in Hstable.
  decompose [and] Hstable.
  split_pures.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_9_noncurrent_owner_pure : OSMutex_RdyAtPrio_full_partial_solve_wit_9_noncurrent_owner_pure.
Proof.
  pre_process.
  sepcon_lift (coq_prop (valid_priority_index sg prio_in)).
  match goal with
  | H : valid_priority_index _ _ |- _ => rename H into Hvalid
  end.
  match goal with
  | H : valid_stable_glob_vars _ |- _ => rename H into Hstable
  end.
  unfold valid_priority_index in Hvalid.
  destruct Hvalid as [Hprio_lo Hprio_hi].
  unfold valid_stable_glob_vars in Hstable.
  decompose [and] Hstable.
  split_pures.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_10_noncurrent_owner_pure : OSMutex_RdyAtPrio_full_partial_solve_wit_10_noncurrent_owner_pure.
Proof.
  pre_process.
  sepcon_lift (coq_prop (valid_priority_index sg prio_in)).
  match goal with
  | H : valid_priority_index _ _ |- _ => rename H into Hvalid
  end.
  match goal with
  | H : valid_stable_glob_vars _ |- _ => rename H into Hstable
  end.
  unfold valid_priority_index in Hvalid.
  destruct Hvalid as [Hprio_lo Hprio_hi].
  unfold valid_stable_glob_vars in Hstable.
  decompose [and] Hstable.
  split_pures.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_which_implies_wit_1 : OSMutex_RdyAtPrio_full_which_implies_wit_1.
Proof.
  pre_process.
  all: pureIntros.
  all: subst ptcb_v.
  all: match goal with
  | Hsnap : task_rdy_snapshot_of_prop _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold task_rdy_snapshot_of_prop in Hsnap;
      destruct Hsnap as (Hmap & Hpt & Hprio & Hx & Hy & Hbitx & Hbity)
  end.
  all: subst pt.
  all: subst tcb_prio_in.
  all: subst tcb_x_in.
  all: subst tcb_y_in.
  all: subst tcb_bitx_in.
  all: subst tcb_bity_in.
  all: match goal with
  | Hsnap : sched_ready_prio_snapshot_prop _ _ _ _ _ _ |- _ =>
      unfold sched_ready_prio_snapshot_prop in Hsnap;
      destruct Hsnap as (Hgrp & Hrdyrel & Hcur)
  end.
  all: match goal with
  | Hcurptr : sched_tcb_cur_snapshot_prop _ _ _ |- _ =>
      unfold sched_tcb_cur_snapshot_prop in Hcurptr
  end.
  all: subst rdy_grp_in.
  all: subst prio_cur_in.
  all: subst tcbcur_in.
  all: match goal with
  | Hprio : prio_tbl_list_rel ?sg0 ?tsk0 ?prioL0 |- _ =>
      pose proof
        (debug_prio_canonical__relocation_semantics
           sg0 tsk0 prioL0 Hprio) as HprioCanon
  end.
  all: subst prioL_in.
  all: match goal with
  | Hrdyrel : osrdytbl_list_rel ?sgR ?tskR ?sched0 ?rdyL0 |- _ =>
      pose proof
        (debug_rdy_canonical__relocation_semantics
           sgR tskR sched0 rdyL0 Hrdyrel) as HrdyCanon;
      pose proof
        (sched_ready_current_split__spatial_localization
           sgR tskR sched0) as HschedSplit
  end.
  all: match goal with
  | Hmap : inUsedTaskStates ?tskT ?tid0 = Some ?t0 |- _ =>
      match goal with
      | Hlayout : task_priority_fields_layout_prop
          (tcb_addr ?sgT ?tid1) ?pa ?xa ?ya ?bxa ?bya |- _ =>
          pose proof
            (task_inv_split_priority_fields_priotbl_at
               sgT tskT tid0 t0 pa xa ya bxa bya Hmap Hlayout) as HtaskSplit
      end
  end.
  all: subst rdyL_in.
  all: unfold UCOS2_Verify_inv.
  all: pureIntros.
  all: sep_apply_l_atomic HtaskSplit.
  all: lazymatch type of HschedSplit with
  | sched_inv ?sg0 ?tsk0 ?sched0 |-- _ =>
      sepcon_lift (sched_inv sg0 tsk0 sched0);
      sep_apply_l_atomic HschedSplit
  end.
  all: unfold used_task_priority_fields_at, store_prio_tbl.
  all: match goal with
  | Hprioaddr : os_tcb_prio_tbl_addr ?sg0 ?prioaddr,
    Hcuraddr : os_tcb_cur_addr ?sg0 ?curaddr,
    Hpriocuraddr : os_prio_cur_addr ?sg0 ?priocuraddr,
    Hrdyaddr : os_rdy_tbl_addr ?sg0 ?rdyaddr,
    Hgrpaddr : os_rdy_grp_addr ?sg0 ?grpaddr |- _ =>
      unfold os_tcb_prio_tbl_addr in Hprioaddr;
      unfold os_tcb_cur_addr in Hcuraddr;
      unfold os_prio_cur_addr in Hpriocuraddr;
      unfold os_rdy_tbl_addr in Hrdyaddr;
      unfold os_rdy_grp_addr in Hgrpaddr;
      rewrite Hprioaddr, Hcuraddr, Hpriocuraddr, Hrdyaddr, Hgrpaddr
  end.
  all: entailer!.
  all: try (unfold task_rdy_snapshot_of_prop; repeat split;
    try assumption; reflexivity).
  all: try match goal with
  | Hrdy : osrdytbl_list_rel ?sg0 ?tsk0 ?sched0 ?l0 |-
      sched_ready_prio_snapshot_prop ?sg0 ?tsk0 ?sched0 _ ?l0 _ =>
      unfold sched_ready_prio_snapshot_prop;
      split; [reflexivity | split; [exact Hrdy | reflexivity]]
  end.
  all: try (unfold sched_tcb_cur_snapshot_prop; reflexivity).
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_which_implies_wit_2 : OSMutex_RdyAtPrio_full_which_implies_wit_2.
Proof.
  pre_process.
  all: pureIntros.
  all: match goal with
  | Hsnap : sched_ready_prio_snapshot_prop
      ?sg0 ?tsk0 ?sched0 ?grp0 ?rdyL0 ?prio0 |- _ =>
      pose proof Hsnap as HsnapFacts;
      unfold sched_ready_prio_snapshot_prop in HsnapFacts;
      destruct HsnapFacts as [_ [HrdyRel _]];
      unfold osrdytbl_list_rel in HrdyRel;
      destruct HrdyRel as [Hlen _];
      match goal with
      | Hlo : 0 <= ?idx, Hhi : ?idx < 8 |- _ =>
          assert (Hidx : osrdytbl_index_in_range idx) by
            (unfold osrdytbl_index_in_range, OS_RDY_TBL_SIZE; lia);
          pose proof
            (store_osrdytbl_split sg0 rdyL0 idx Hidx Hlen) as Hsplit
      end
  end.
  all: sep_apply_l_atomic Hsplit.
  all: unfold osrdytbl_element_store, sizeof_OS_PRIO.
  all: match goal with
  | Haddr : os_rdy_tbl_addr ?sg0 ?addr0 |- _ =>
      pose proof Haddr as HaddrEq;
      unfold os_rdy_tbl_addr in HaddrEq;
      rewrite HaddrEq
  end.
  all: rewrite PreH3.
  all: cbn [sizeof_front_end_type].
  all: entailer!.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_which_implies_wit_3 : OSMutex_RdyAtPrio_full_which_implies_wit_3.
Proof.
  pre_process.
  all: pureIntros.
  all: match goal with
  | Hsnap : sched_ready_prio_snapshot_prop
      ?sg0 ?tsk0 ?sched0 ?grp0 ?rdyL0 ?prio0 |- _ =>
      pose proof Hsnap as HsnapFacts;
      unfold sched_ready_prio_snapshot_prop in HsnapFacts;
      destruct HsnapFacts as [_ [HrdyRel _]];
      unfold osrdytbl_list_rel in HrdyRel;
      destruct HrdyRel as [Hlen _];
      match goal with
      | Heq : ?newv = Znth ?newi (replace_Znth ?oldi ?oldv ?rdyL0) 0 |- _ =>
          assert (Hnewidx : osrdytbl_index_in_range newi) by
            (unfold osrdytbl_index_in_range, OS_RDY_TBL_SIZE; lia);
          prop_apply_p
            (store_osrdytbl_missing_i_range__spatial_localization
               sg0 rdyL0 oldi);
          Intros_p Holdidx;
          match goal with
          | Haddr : os_rdy_tbl_addr sg0 ?addr0 |- _ =>
              pose proof Haddr as HaddrEq;
              unfold os_rdy_tbl_addr in HaddrEq;
              rewrite HaddrEq
          end;
          sep_apply_l_atomic
            (debug_store_osrdytbl_merge_c_cell__relocation_semantics
               sg0 rdyL0 oldi oldv Holdidx Hlen);
          assert (Hlen' :
            Zlength (replace_Znth oldi oldv rdyL0) = OS_RDY_TBL_SIZE) by
            (rewrite Zlength_replace_Znth; exact Hlen);
          sep_apply_l_atomic
            (store_osrdytbl_split sg0
               (replace_Znth oldi oldv rdyL0) newi Hnewidx Hlen')
      end
  end.
  all: unfold osrdytbl_element_store, sizeof_OS_PRIO.
  all: rewrite <- PreH3.
  all: cbn [sizeof_front_end_type].
  all: entailer!.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_full_which_implies_wit_4 : OSMutex_RdyAtPrio_full_which_implies_wit_4.
Proof.
  pre_process.
  all: pureIntros.
  all: match goal with
  | Hrel : prio_tbl_list_rel ?sg0 ?tsk0 ?prioL0 |- _ =>
      pose proof Hrel as HrelFacts;
      unfold prio_tbl_list_rel in HrelFacts;
      destruct HrelFacts as [Hlen _];
      match goal with
      | Hlo : 0 <= ?idx, Hhi : ?idx < 64 |- _ =>
          assert (Hidx : priotbl_index_in_range idx) by
            (unfold priotbl_index_in_range, OS_PRIO_TBL_SIZE; lia);
          pose proof
            (store_priotbl_list_split sg0 prioL0 idx Hidx Hlen) as Hsplit
      end
  end.
  all: sep_apply_l_atomic Hsplit.
  all: unfold priotbl_element_store, sizeof_OSTCB_ptr.
  all: match goal with
  | Haddr : os_tcb_prio_tbl_addr ?sg0 ?addr0 |- _ =>
      pose proof Haddr as HaddrEq;
      unfold os_tcb_prio_tbl_addr in HaddrEq;
      rewrite HaddrEq
  end.
  all: cbn [sizeof_front_end_type].
  all: entailer!.
Qed.
