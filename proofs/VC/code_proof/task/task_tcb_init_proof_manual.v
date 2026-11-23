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
From Ucos2Verify.VC.code.task Require Import task_tcb_init_goal.
From Ucos2Verify.VC.code.task Require Import task_tcb_init_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OS_TCBInit_safety_wit_4 : OS_TCBInit_safety_wit_4.
Proof.
  left; intros.
  pose proof (task_tcb_init_entry_priority_in_range _ _ _ _ _ PreH5) as Hrange.
  destruct PreH2 as [Hprio _]; rewrite Hprio in Hrange.
  entailer!; lia.
Qed.

Lemma proof_of_OS_TCBInit_safety_wit_5 : OS_TCBInit_safety_wit_5.
Proof.
  left; intros.
  pose proof (task_tcb_init_entry_priority_in_range _ _ _ _ _ PreH5) as Hrange.
  destruct PreH2 as [Hprio _]; rewrite Hprio in Hrange.
  rewrite task_tcb_init_priority_shift_eq.
  rewrite unsigned_last_nbits_eq by (change (0 <= prio_pre / 8 < 256); lia).
  entailer!; lia.
Qed.

Lemma proof_of_OS_TCBInit_safety_wit_6 : OS_TCBInit_safety_wit_6.
Proof.
  left; intros.
  rewrite task_tcb_init_priority_mask_eq.
  pose proof (Z.mod_pos_bound prio_pre 8 ltac:(lia)) as Hrange.
  entailer!; lia.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_1 : OS_TCBInit_entail_wit_1.
Proof.
  left; intros; Exists acquired_2.
  pose proof (task_tcb_init_acquire_entry _ _ _ _ _ _ _ PreH3 PreH1) as Hentry.
  pose proof (proj1 PreH4) as Hfree.
  rewrite task_tcb_init_raw_split_free_root, Hfree.
  entailer!.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_2 : OS_TCBInit_entail_wit_2.
Proof.
  right; intros.
  destruct (unUsedTaskStates (TskState acquired)) as [|slot rest] eqn:Hhead.
  - unfold task_tcb_init_free_root in PreH1; rewrite Hhead in PreH1;
      cbn [hd_error encode_task_link] in PreH1; contradiction.
  - pose proof (proj1 (proj2 (proj1 PreH6))) as Htasks.
    assert (Hconfiguration : sg.(osKernelConfig).(cfgEventMultiEnabled) = false /\
      sg.(osKernelConfig).(cfgTaskProfile) = false).
    { pose proof (proj1 (proj1 PreH6)) as Hprofile.
      unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto. }
    destruct Hconfiguration as [Hmulti Htaskprofile].
    pose proof (proj1 (proj2 (proj2 Htasks))) as Hlinks.
    rewrite Hhead in Hlinks; cbn [task_free_links] in Hlinks.
    destruct Hlinks as [image [Himage [Hnext Htail]]].
    assert (Hdetach : task_tcb_init_detach_observation args invocation origin
      acquired slot rest image).
    { unfold task_tcb_init_detach_observation, task_detach_guard.
      split; [exact Hhead|]. split; [exact (proj1 (proj2 (proj2 (proj2 PreH6))))|].
      split; [reflexivity|exact Himage]. }
    assert (Hroot : task_tcb_init_free_root sg acquired = tcb64_addr sg slot).
    { unfold task_tcb_init_free_root; rewrite Hhead; cbn [hd_error encode_task_link].
      apply task_slot_addr_tcb64; assumption. }
    Exists slot rest image acquired.
    unfold task_tcb_init_public_without_free_root,
      task_tcb_init_public_without_free_head,
      task_public_storage_without_free_head.
    rewrite Hhead; cbn [task_free_storage_rep].
    Intros stored.
    assert (stored = image) by congruence; subst stored.
    sep_apply_l_atomic (proj1 (task_slot_storage_tcb64 sg slot image Hmulti Htaskprofile)).
    sep_apply_l_atomic (tcb64_storage_split (tcb64_addr sg slot)
      (tcb_layout_common_image image) TCBNext).
    unfold tcb_layout_common_image.
    rewrite Hnext.
    cbn [tcb_cell tcb_field_address].
    rewrite Hroot.
    entailer!.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_3 : OS_TCBInit_entail_wit_3.
Proof.
  left; intros; Exists slot_2 rest_2 free_image_2 acquired_2.
  pose proof (tcb64_storage_merge ptcb (tcb_layout_common_image free_image_2) TCBNext) as Hmerge.
  change (tcb_layout_common_image free_image_2 TCBNext = Some next_free) in PreH7.
  cbn [tcb_cell tcb_field_address] in Hmerge.
  rewrite PreH7 in Hmerge.
  sep_apply_l_atomic Hmerge.
  pose proof (task_tcb_init_detach_merge_invariant _ _ _ _ _ _ _ _ PreH5 PreH6)
    as Hclose.
  pose proof (proj1 PreH1) as Hfree.
  rewrite Hfree, <- PreH8 in Hclose.
  sep_apply_l_atomic Hclose.
  entailer!.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_4 : OS_TCBInit_entail_wit_4.
Proof.
  left; intros; Exists slot_2 rest_2 free_image_2 acquired_2.
  sep_apply_l_atomic (task_tcb_init_storage_open_initialization ptcb (tcb_layout_common_image free_image_2)).
  unfold task_tcb_init_written_storage, tcb64_fields_rep, tcb_fields.
  cbn [filter task_tcb_init_written_field].
  repeat rewrite TaskFieldStorage.store_fields_cons by
    (repeat constructor; simpl; intuition discriminate).
  rewrite !TaskFieldStorage.store_fields_nil.
  cbn [tcb_cell tcb_field_address].
  entailer!.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_5 : OS_TCBInit_entail_wit_5.
Proof.
  right; intros.
  pose proof (task_tcb_init_entry_priority_in_range _ _ _ _ _ PreH5) as Hrange.
  destruct PreH2 as [Hprio _]; rewrite Hprio in Hrange.
  rewrite zdiv_equiv by lia.
  rewrite Z.rem_mod_nonneg by lia.
  rewrite task_tcb_init_priority_shift_eq, task_tcb_init_priority_mask_eq.
  rewrite (unsigned_last_nbits_eq (prio_pre / 8) 8) by
    (change (0 <= prio_pre / 8 < 256); lia).
  entailer!.
  all: apply unsigned_last_nbits_eq;
    apply shiftl_one_byte_in_range__private_initialization; lia.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_6 : OS_TCBInit_entail_wit_6.
Proof.
  right; intros.
  assert (i = 0) by lia; subst i.
  Exists slot_2 rest_2 free_image_2 acquired_2.
  replace (0 + 1) with 1 by lia.
  rewrite UIntArray.undef_seg_empty.
  entailer!.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_7 : OS_TCBInit_entail_wit_7.
Proof.
  left; intros.
  pose proof (task_tcb_init_entry_priority_in_range _ _ _ _ _ PreH6) as Hrange.
  pose proof (proj1 PreH3) as Hprio_range; rewrite Hprio_range in Hrange.
  rewrite zdiv_equiv by lia.
  rewrite Z.rem_mod_nonneg by lia.
  assert (i = 1) by lia; subst i.
  Exists slot_2 rest_2 free_image_2 acquired_2.
  rewrite UIntArray.undef_seg_empty.
  sep_apply_l_atomic (UIntArray.seg_to_full
    (&(ptcb # "os_tcb" ->ₛ "OSTCBRegTbl")) 0 1 (zeros 1)).
  replace ((&(ptcb # "os_tcb" ->ₛ "OSTCBRegTbl")) + 0 * sizeof(UINT))
    with (&(ptcb # "os_tcb" ->ₛ "OSTCBRegTbl")) by lia.
  cbn [zeros Z.to_nat repeat Z.sub].
  rewrite task_tcb_init_storage_split_written.
  unfold task_tcb_init_retained_storage, task_tcb_init_written_storage,
    tcb64_fields_rep, tcb_fields.
  cbn [filter task_tcb_init_written_field].
  repeat rewrite TaskFieldStorage.store_fields_cons by
    (repeat constructor; simpl; intuition discriminate).
  rewrite !TaskFieldStorage.store_fields_nil.
  cbn [task_tcb_init_raw_image tcb_cell tcb_field_address].
  destruct PreH3 as [Hprio [Htop [Hbottom [Hid [Hsize [Hext [Hopt Hname]]]]]]].
  rewrite Hprio, Htop, Hbottom, Hid, Hsize, Hext, Hopt, Hname.
  entailer!.
  unfold task_tcb_init_arguments; tauto.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_8 : OS_TCBInit_entail_wit_8.
Proof.
  unfold OS_TCBInit_entail_wit_8; left; intros.
  destruct (task_tcb_init_acquire_commit critical sg args invocation origin acquired_2
    slot_2 rest_2 free_image_2 acquired_3 PreH7 PreH8 PreH1)
    as [Hvalid [Hbinding Hactive]].
  pose proof (interrupt_saved_value_resave mask cpu_sr retval PreH6 PreH2) as Hsaved.
  pose proof (task_tcb_init_entry_priority_in_range sg args invocation origin acquired_2
    PreH7) as Hrange.
  pose proof PreH3 as Haddresses.
  destruct Haddresses as [Hfree [Hhead [Htable [Hgroup [Hrows Hcount]]]]].
  pose proof PreH4 as Harguments.
  destruct Harguments as [Hprio [Htop [Hbottom [Hid [Hsize [Hext [Hopt Hname]]]]]]].
  rewrite Hprio in Hrange; destruct Hrange as [[Hp0 Hp64] [[Hy0 Hy8] [Hx0 Hx8]]].
  rewrite Z.quot_div_nonneg by lia.
  rewrite Z.rem_mod_nonneg by lia.
  rewrite (task_tcb_init_raw_split_publication sg acquired_3).
  sep_apply_l_atomic (task_tcb_init_storage_open_links__publication_and_returns
    ptcb args (tcb_layout_common_image free_image_2)).
  Exists acquired_3 slot_2 rest_2 free_image_2 acquired_2.
  unfold task_tcb_init_written_storage, tcb64_fields_rep, tcb_fields.
  cbn [filter task_tcb_init_written_field].
  repeat rewrite TaskFieldStorage.store_fields_cons by
    (repeat constructor; simpl; intuition discriminate).
  rewrite !TaskFieldStorage.store_fields_nil.
  cbn [task_tcb_init_raw_image tcb_cell tcb_field_address].
  unfold tcb_x_of_prio, tcb_y_of_prio, tcb_bit_x_of_prio, tcb_bit_y_of_prio.
  rewrite Hhead, Htable, Hgroup, Hrows, Hcount.
  rewrite Hprio, Htop, Hbottom, Hid, Hsize, Hext, Hopt, Hname.
  entailer!.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_9 : OS_TCBInit_entail_wit_9.
Proof.
  unfold OS_TCBInit_entail_wit_9; right; intros.
  sep_apply_l_atomic (task_tcb_init_used_split_head_prev__publication_and_returns
    sg current_2 PreH18 PreH1).
  Intros previous.
  Exists previous current_2 slot_2 rest_2 free_image_2 acquired_2.
  cbn [tcb_cell tcb_field_address].
  entailer!.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_10_1 : OS_TCBInit_entail_wit_10_1.
Proof.
  unfold OS_TCBInit_entail_wit_10_1; right; intros.
  subst head ptcb.
  assert (Hconfiguration : sg.(osKernelConfig).(cfgEventMultiEnabled) = false /\
    sg.(osKernelConfig).(cfgTaskProfile) = false).
  { pose proof (proj1 PreH17) as Hprofile.
    unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto. }
  destruct Hconfiguration as [Hmulti Htaskprofile].
  pose proof (task_tcb_init_used_merge_head_prev__publication_and_returns
    sg current_2 slot_2) as Hmerge.
  rewrite task_slot_addr_tcb64 in Hmerge by assumption.
  cbn [tcb_cell tcb_field_address] in Hmerge.
  sep_apply_l_atomic Hmerge.
  Exists current_2 slot_2 rest_2 free_image_2 acquired_2.
  entailer!.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_10_2 : OS_TCBInit_entail_wit_10_2.
Proof.
  unfold OS_TCBInit_entail_wit_10_2; right; intros.
  pose proof (task_tcb_init_active_head_zero__publication_and_returns sg current_2
    PreH18 PreH1) as Hnone.
  Exists current_2 slot_2 rest_2 free_image_2 acquired_2.
  unfold task_tcb_init_used_with_head_prev, task_tcb_init_used_storage,
    task_tcb_init_head_updated_map.
  rewrite Hnone; entailer!.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_11 : OS_TCBInit_entail_wit_11.
Proof.
  unfold OS_TCBInit_entail_wit_11; right; intros.
  rewrite Z.quot_div_nonneg in * by lia.
  rewrite Z.rem_mod_nonneg in * by lia.
  pose proof PreH5 as Haddresses.
  destruct Haddresses as [Hfree [Hhead [Htable [Hgroup [Hrows Hcount]]]]].
  pose proof PreH6 as Harguments.
  destruct Harguments as [Hprio [Htop [Hbottom [Hid [Hsize [Hext [Hopt Hname]]]]]]].
  assert (Hconfiguration : sg.(osKernelConfig).(cfgEventMultiEnabled) = false /\
    sg.(osKernelConfig).(cfgTaskProfile) = false).
  { pose proof (proj1 PreH21) as Hprofile.
    unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto. }
  destruct Hconfiguration as [Hmulti Htaskprofile].
  pose proof (task_tcb_init_commit_binding_identity args invocation origin acquired_2 current_2
    slot_2 free_image_2 PreH20) as Hidentity.
  destruct (task_tcb_init_detached_flags_defined sg args invocation origin acquired_2
    slot_2 rest free_image_2 PreH9 PreH10) as [flags Hflags].
  assert (Hnot : ~ In slot_2 current_2.(SchedState).(readyList)).
  { pose proof (task_commit_identity_private _ _ _ _ Hidentity) as Hprivate.
    destruct (task_private_excludes_public sg current_2.(TskState) slot_2
      (proj1 (proj1 (proj2 PreH21))) Hprivate) as [Hnone _].
    intro Hin.
    destruct (proj1 (proj1 (proj1 (proj2 (proj2 PreH21)))) slot_2 Hin) as [t [Hget _]].
    congruence. }
  assert (Hprio_range : forall tid t, In tid current_2.(SchedState).(readyList) ->
    current_2.(TskState).(inUsedTaskStates) tid = Some t -> 0 <= t.(curPrio) < 64).
  { intros tid t Hin Hget.
    destruct (proj1 (proj1 (proj1 (proj2 (proj2 PreH21)))) tid Hin) as [other [Hother [Hp _]]].
    assert (other = t) by congruence; subst other.
    pose proof (proj1 (proj1 PreH21)) as Hsg.
    unfold valid_stable_glob_vars in Hsg.
    unfold task_priority_in_range in Hp; intuition lia. }
  pose proof (task_tcb_init_published_result critical sg args invocation origin initial acquired_2
    slot_2 rest free_image_2 current_2 PreH9 PreH7 PreH10 PreH19 PreH20 PreH21) as Hresult.
  pose proof (sched_commit_ready_encodings__publication_and_returns sg current_2.(TskState)
    current_2.(SchedState) args.(initPrio) invocation
    (task_tcb_init_commit_node args acquired_2 slot_2 free_image_2) Hnot) as [Hgrp Hrow].
  assert (Htable_eq : task_tcb_init_priority_table sg
    (task_tcb_init_published_state sg args invocation acquired_2 current_2 slot_2 free_image_2) =
      replace_Znth prio_pre ptcb (task_tcb_init_priority_table sg current_2)).
  { subst ptcb; unfold task_tcb_init_priority_table.
    rewrite <- Hprio.
    pose proof (task_commit_priority_table_replace_eq__publication_and_returns sg
      current_2.(TskState) args.(initPrio) invocation
      (task_tcb_init_commit_node args acquired_2 slot_2 free_image_2)) as Heq.
    cbn [task_tcb_init_commit_node task_tcb_init_node_from_free_image taskID] in Heq.
    rewrite task_slot_addr_tcb64 in Heq by assumption.
    apply Heq; rewrite Hprio; lia. }
  assert (Hrows_eq : task_tcb_init_ready_rows
    (task_tcb_init_published_state sg args invocation acquired_2 current_2 slot_2 free_image_2) =
    replace_Znth (prio_pre / 8)
      (Z.lor (Znth (prio_pre / 8) (task_tcb_init_ready_rows current_2) 0)
        (Z.shiftl 1 (prio_pre mod 8))) (task_tcb_init_ready_rows current_2)).
  { pose proof (sched_commit_rows_replace_eq__publication_and_returns sg current_2.(TskState)
      current_2.(SchedState) args.(initPrio) invocation
      (task_tcb_init_commit_node args acquired_2 slot_2 free_image_2) Hnot) as Heq.
    cbn [task_tcb_init_commit_node task_tcb_init_node_from_free_image curPrio] in Heq.
    rewrite Hprio in Heq; apply Heq; lia. }
  assert (Hgrp_eq : task_tcb_init_ready_group
    (task_tcb_init_published_state sg args invocation acquired_2 current_2 slot_2 free_image_2) =
    Z.lor (task_tcb_init_ready_group current_2) (Z.shiftl 1 (prio_pre / 8))).
  { rewrite <- Hprio; exact Hgrp. }
  assert (Hcount_range : 0 <= task_tcb_init_count current_2 + 1 < 256).
  { pose proof (task_count_in_pool_range sg current_2.(TskState)
      (proj1 PreH21) (proj1 (proj2 PreH21))).
    unfold task_tcb_init_count; lia. }
  rewrite (unsigned_last_nbits_eq (task_tcb_init_count current_2 + 1) 8 Hcount_range).
  assert (Hgroup_cast : unsigned_last_nbits (task_tcb_init_ready_group current_2) 8 =
    task_tcb_init_ready_group current_2).
  { apply ready_group_uchar_id__publication_and_returns; exact Hprio_range. }
  rewrite Hgroup_cast.
  rewrite !uchar_shift_mask_id__publication_and_returns by lia.
  change (Znth (prio_pre / 8) (task_tcb_init_ready_rows current_2) 0) with
    (Znth (prio_pre / 8) (Ucos2Verify.lib.sched.sched_row_values current_2.(TskState) current_2.(SchedState).(readyList)) 0).
  rewrite Ucos2Verify.lib.sched.sched_row_values_Znth by lia.
  rewrite ready_row_uchar_id__publication_and_returns.
  rewrite <- Ucos2Verify.lib.sched.sched_row_values_Znth by lia.
  change (Ucos2Verify.lib.sched.sched_row_values current_2.(TskState) current_2.(SchedState).(readyList))
    with (task_tcb_init_ready_rows current_2).
  rewrite <- Hrows_eq, <- Htable_eq, <- Hgrp_eq.
  rewrite <- Hhead, <- Htable, <- Hgroup, <- Hrows, <- Hcount.
  rewrite <- Hprio, <- Htop, <- Hbottom, <- Hid, <- Hsize, <- Hext, <- Hopt, <- Hname.
  subst ptcb.
  assert (Hstorage : task_tcb_init_retained_without_links (tcb64_addr sg slot_2) (tcb_layout_common_image free_image_2) **
    task_tcb_init_written_storage (tcb64_addr sg slot_2) (task_tcb_init_raw_image args (tcb_layout_common_image free_image_2)) **
    tcb_cell (tcb64_addr sg slot_2) TCBNext (Some (task_tcb_init_active_head sg current_2)) **
    tcb_cell (tcb64_addr sg slot_2) TCBPrev (Some 0) |--
    tcb64_storage_rep (tcb64_addr sg slot_2)
      (task_tcb_init_linked_image sg current_2.(TskState).(tcbListHead)
        (task_tcb_init_raw_image args (tcb_layout_common_image free_image_2)))).
  { unfold task_tcb_init_active_head.
    rewrite encode_task_link_tcb64 by assumption.
    unfold tcb64_storage_rep, task_tcb_init_retained_without_links,
      task_tcb_init_written_storage, tcb64_fields_rep, tcb_fields,
      task_tcb_init_linked_image.
    cbn [filter task_tcb_init_written_field].
    repeat rewrite TaskFieldStorage.store_fields_cons by
      (repeat constructor; simpl; intuition discriminate).
    rewrite !TaskFieldStorage.store_fields_nil.
    cbn [tcb_write field_update TCBField_eq_dec task_tcb_init_raw_image].
    entailer!. }
  Exists acquired_2 current_2 slot_2 free_image_2.
  entailer!.
  all: try solve [unfold task_tcb_init_arguments; intuition].
  all: try solve [unfold task_tcb_init_global_addresses; intuition].
  assert (Hnewname : sg.(osKernelConfig).(cfgTaskNames) = true ->
      exists chars, readable_name current_2.(NameState)
        (task_tcb_init_commit_node args acquired_2 slot_2 free_image_2).(tcbTaskName) chars).
  { intros Htasknames.
    pose proof (proj2 (proj2 (proj2 PreH9))) as [_ HtaskNameValid].
    destruct (HtaskNameValid Htasknames) as [chars Hread].
    pose proof (critical_region_interval_preserves_name_state critical sg invocation
      (task_tcb_init_detached_state args invocation origin acquired_2 slot_2 rest free_image_2)
      current_2 PreH19) as Hname_frame.
    exists chars; rewrite (task_tcb_init_commit_node_name args acquired_2 slot_2 free_image_2).
    rewrite <- Hname_frame; exact Hread. }
  pose proof (task_tcb_init_publication_storage_merge__publication_and_returns
    sg args invocation origin acquired_2 current_2 slot_2 free_image_2 flags PreH21 PreH20 Hflags Hnewname) as Hpublication.
  cbv zeta in Hpublication.
  rewrite task_slot_storage_tcb64 in Hpublication by assumption.
  rewrite task_slot_addr_tcb64 in Hpublication by assumption.
  assert (Himage : tcb_layout_common_image
    (task_tcb_init_linked_layout_image sg current_2.(TskState).(tcbListHead)
      (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile) args free_image_2)) =
    task_tcb_init_linked_image sg current_2.(TskState).(tcbListHead)
      (task_tcb_init_raw_image args (tcb_layout_common_image free_image_2))).
  { unfold task_tcb_init_layout_image; rewrite Hmulti, Htaskprofile.
    unfold tcb_layout_common_image, task_tcb_init_linked_layout_image,
      tcb_layout_write, task_tcb_init_linked_image.
    apply functional_extensionality; intros field; destruct field;
      cbn beta iota;
      repeat first [rewrite field_update_same | rewrite field_update_other by discriminate].
    all: try reflexivity.
    f_equal; apply encode_task_link_tcb64; assumption. }
  rewrite Himage in Hpublication.
  sep_apply_r_atomic Hpublication.
  sepcon_assoc_change.
  sep_apply_r_atomic Hstorage.
  unfold task_tcb_init_written_storage, tcb64_fields_rep, tcb_fields.
  cbn [filter task_tcb_init_written_field].
  repeat rewrite TaskFieldStorage.store_fields_cons by
    (repeat constructor; simpl; intuition discriminate).
  rewrite !TaskFieldStorage.store_fields_nil.
  cbn [task_tcb_init_raw_image tcb_cell tcb_field_address].
  unfold tcb_x_of_prio, tcb_y_of_prio, tcb_bit_x_of_prio, tcb_bit_y_of_prio.
  entailer!.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_12 : OS_TCBInit_entail_wit_12.
Proof.
  unfold OS_TCBInit_entail_wit_12; right; intros.
  assert (Hresult : task_tcb_init_result critical sg args invocation origin initial
    66 acquired_2).
  { apply TaskTCBInitNoFree; [exact PreH4| |exact (proj1 (proj2 (proj2 (proj2 PreH6))))|
      exact (proj1 PreH6)].
    apply (task_tcb_init_free_root_zero__publication_and_returns sg acquired_2
      (proj1 PreH6) PreH1). }
  pose proof PreH2 as Haddr; destruct Haddr as [Hfree Haddr].
  rewrite <- Hfree.
  sep_apply_l_atomic (proj2 (task_tcb_init_raw_split_free_root sg acquired_2)).
  Exists acquired_2.
  unfold UCOS2_inv; entailer!.
  exact (proj1 PreH6).
  rewrite Hfree; exact PreH2.
Qed.

Lemma proof_of_OS_TCBInit_return_wit_1 : OS_TCBInit_return_wit_1.
Proof.
  unfold OS_TCBInit_return_wit_1; left; intros.
  sep_apply_l_atomic (task_tcb_init_post_from_released_result platform critical sg args
    invocation origin mask initial 66 acquired cpu_sr PreH3 PreH4).
  entailer!.
Qed.

Lemma proof_of_OS_TCBInit_return_wit_2 : OS_TCBInit_return_wit_2.
Proof.
  unfold OS_TCBInit_return_wit_2; left; intros.
  sep_apply_l_atomic (task_tcb_init_post_from_released_result platform critical sg args
    invocation origin mask initial 0 _ cpu_sr PreH3 PreH5).
  entailer!.
Qed.

Lemma proof_of_OS_TCBInit_which_implies_wit_1 : OS_TCBInit_which_implies_wit_1.
Proof.
  left; intros; unfold task_tcb_init_pre; reflexivity.
Qed.
