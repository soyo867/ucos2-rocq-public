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
From Ucos2Verify.VC.code.task Require Import task_tcb_init_stack_goal.
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

Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_sched_publication_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_modular_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_timer_phase_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_name_resources_spec.
Lemma proof_of_OS_TCBInit_safety_wit_4 : OS_TCBInit_safety_wit_4.
Proof.
  left; intros.
  pose proof (task_tcb_init_entry_priority_in_range _ _ _ _ _ PreH18) as Hrange.
  destruct PreH15 as [Hprio _]; rewrite Hprio in Hrange.
  entailer!; lia.
Qed.

Lemma proof_of_OS_TCBInit_safety_wit_5 : OS_TCBInit_safety_wit_5.
Proof.
  left; intros.
  pose proof (task_tcb_init_entry_priority_in_range _ _ _ _ _ PreH18) as Hrange.
  destruct PreH15 as [Hprio _]; rewrite Hprio in Hrange.
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
  left; intros.
  assert (Hentry : task_tcb_init_entry sg_phase_call_spec args_phase_call_spec call_phase_call_spec.(os_sched_call_invocation)
    call_phase_call_spec.(os_sched_call_origin) initial_phase_call_spec).
  { rewrite PreH1, PreH2, PreH7; exact PreH3. }
  sep_apply_l_atomic (task_tcb_init_modular_save_phase_entry environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec args_phase_call_spec call_phase_call_spec
    mask_phase_call_spec retval initial_phase_call_spec Hentry).
  Intros returned acquired.
  Exists acquired returned.
  rewrite PreH1, PreH2 in *.
  pose proof (proj1 PreH5) as Hfree.
  rewrite task_tcb_init_raw_split_free_root, Hfree.
  unfold task_tcb_init_stack_same_call in *; rewrite PreH1, PreH2 in *; entailer!; tauto.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_2 : OS_TCBInit_entail_wit_2.
Proof.
  right; intros.
  destruct (unUsedTaskStates (TskState acquired)) as [|slot rest] eqn:Hhead.
  - unfold task_tcb_init_free_root in PreH1; rewrite Hhead in PreH1;
      cbn [hd_error encode_task_link] in PreH1; contradiction.
  - pose proof (proj1 (proj2 (proj1 PreH19))) as Htasks.
    assert (Hconfiguration : sg_phase_call_spec.(osKernelConfig).(cfgEventMultiEnabled) = false /\
      sg_phase_call_spec.(osKernelConfig).(cfgTaskProfile) = false).
    { pose proof (proj1 (proj1 PreH19)) as Hprofile.
      unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto. }
    destruct Hconfiguration as [Hmulti Htaskprofile].
    pose proof (proj1 (proj2 (proj2 Htasks))) as Hlinks.
    rewrite Hhead in Hlinks; cbn [task_free_links] in Hlinks.
    destruct Hlinks as [image [Himage [Hnext Htail]]].
    assert (Hdetach : task_tcb_init_detach_observation args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec
      acquired slot rest image).
    { unfold task_tcb_init_detach_observation, task_detach_guard.
      split; [exact Hhead|]. split; [exact (proj1 (proj2 (proj2 (proj2 PreH19))))|].
      split; [reflexivity|exact Himage]. }
    assert (Hroot : task_tcb_init_free_root sg_phase_call_spec acquired = tcb64_addr sg_phase_call_spec slot).
    { unfold task_tcb_init_free_root; rewrite Hhead; cbn [hd_error encode_task_link].
      apply task_slot_addr_tcb64; assumption. }
    Exists slot rest image acquired first_call_2.
    unfold task_tcb_init_public_without_free_root,
      task_tcb_init_public_without_free_head,
      task_public_storage_without_free_head.
    rewrite Hhead; cbn [task_free_storage_rep].
    Intros stored.
    assert (stored = image) by congruence; subst stored.
    sep_apply_l_atomic (proj1 (task_slot_storage_tcb64 sg_phase_call_spec slot image Hmulti Htaskprofile)).
    sep_apply_l_atomic (tcb64_storage_split (tcb64_addr sg_phase_call_spec slot)
      (tcb_layout_common_image image) TCBNext).
    unfold tcb_layout_common_image.
    rewrite Hnext.
    cbn [tcb_cell tcb_field_address].
    rewrite Hroot.
    entailer!.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_3 : OS_TCBInit_entail_wit_3.
Proof.
  left; intros; Exists slot_2 rest_2 free_image_2 acquired_2 first_call_2.
  pose proof (tcb64_storage_merge ptcb (tcb_layout_common_image free_image_2) TCBNext) as Hmerge.
  change (tcb_layout_common_image free_image_2 TCBNext = Some next_free) in PreH20.
  cbn [tcb_cell tcb_field_address] in Hmerge.
  rewrite PreH20 in Hmerge.
  sep_apply_l_atomic Hmerge.
  pose proof (task_tcb_init_continuation_detach_resources environment_phase_call_spec saved_local_phase_call_spec
    sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 PreH18 PreH19) as Hclose.
  pose proof (proj1 PreH14) as Hfree.
  rewrite Hfree, <- PreH21 in Hclose.
  cbv zeta in Hclose.
  sep_apply_l_atomic Hclose.
  entailer!.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_4 : OS_TCBInit_entail_wit_4.
Proof.
  left; intros; rewrite PreH8, PreH9, <- PreH10.
  Exists slot_2 rest_2 free_image_2 acquired_2 first_call_2.
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
  pose proof (task_tcb_init_entry_priority_in_range _ _ _ _ _ PreH21) as Hrange.
  destruct PreH18 as [Hprio _]; rewrite Hprio in Hrange.
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
  Exists slot_2 rest_2 free_image_2 acquired_2 first_call_2.
  replace (0 + 1) with 1 by lia.
  rewrite UIntArray.undef_seg_empty.
  entailer!.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_7 : OS_TCBInit_entail_wit_7.
Proof.
  left; intros.
  pose proof (task_tcb_init_entry_priority_in_range _ _ _ _ _ PreH19) as Hrange.
  pose proof (proj1 PreH16) as Hprio_range; rewrite Hprio_range in Hrange.
  rewrite zdiv_equiv by lia.
  rewrite Z.rem_mod_nonneg by lia.
  assert (i = 1) by lia; subst i.
  Exists slot_2 rest_2 free_image_2 acquired_2 first_call_2.
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
  destruct PreH16 as [Hprio [Htop [Hbottom [Hid [Hsize [Hext [Hopt Hname]]]]]]].
  rewrite Hprio, Htop, Hbottom, Hid, Hsize, Hext, Hopt, Hname.
  entailer!.
  unfold task_tcb_init_arguments; tauto.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_8 : OS_TCBInit_entail_wit_8.
Proof.
  left; intros.
  assert (Hentry : task_tcb_init_entry sg_phase_call_spec args_phase_call_spec call_phase_call_spec.(os_sched_call_invocation)
    call_phase_call_spec.(os_sched_call_origin) acquired_2) by (rewrite PreH20, PreH21; exact PreH27).
  assert (Hdetach : task_tcb_init_detach_observation args_phase_call_spec call_phase_call_spec.(os_sched_call_invocation)
    call_phase_call_spec.(os_sched_call_origin) acquired_2 slot_2 rest_2 free_image_2)
    by (rewrite PreH20, PreH21; exact PreH28).
  assert (Hprevious : task_tcb_init_call_preserved sg_phase_call_spec call_phase_call_spec.(os_sched_call_invocation)
    (task_tcb_init_detached_state args_phase_call_spec call_phase_call_spec.(os_sched_call_invocation) call_phase_call_spec.(os_sched_call_origin)
      acquired_2 slot_2 rest_2 free_image_2) checkpoint)
    by (rewrite PreH20, PreH21; exact PreH9).
  sep_apply_l_atomic (task_tcb_init_modular_save_phase_commit environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec args_phase_call_spec call_phase_call_spec checkpoint_call
    mask_phase_call_spec retval initial_phase_call_spec acquired_2 slot_2 rest_2 free_image_2 checkpoint PreH1 Hentry Hdetach Hprevious PreH3 PreH4).
  Intros returned current.
  assert (Htransport : task_tcb_init_stack_source_preserved checkpoint_call checkpoint current) by tauto.
  assert (Hpreserved : task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current).
  { intros Hbefore.
    apply (proj1 (task_tcb_init_stack_same_call_source_iff checkpoint_call call_phase_call_spec current PreH1)).
    apply Htransport.
    apply (proj2 (task_tcb_init_stack_same_call_source_iff checkpoint_call call_phase_call_spec checkpoint PreH1)).
    apply PreH2; exact Hbefore. }
  rewrite PreH20, PreH21 in *.
  pose proof (task_tcb_init_entry_priority_in_range sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 PreH27) as Hrange.
  pose proof PreH23 as Haddresses.
  destruct Haddresses as [Hfree [Hhead [Htable [Hgroup [Hrows Hcount]]]]].
  pose proof PreH24 as Harguments.
  destruct Harguments as [Hprio [Htop [Hbottom [Hid [Hsize [Hext [Hopt Hname]]]]]]].
  rewrite Hprio in Hrange; destruct Hrange as [[Hp0 Hp64] [[Hy0 Hy8] [Hx0 Hx8]]].
  rewrite Z.quot_div_nonneg by lia.
  rewrite Z.rem_mod_nonneg by lia.
  rewrite (task_tcb_init_raw_split_publication sg_phase_call_spec current).
  sep_apply_l_atomic (task_tcb_init_storage_open_links__publication_and_returns
    ptcb args_phase_call_spec (tcb_layout_common_image free_image_2)).
  Exists slot_2 rest_2 free_image_2 acquired_2 current returned.
  unfold task_tcb_init_written_storage, tcb64_fields_rep, tcb_fields.
  cbn [filter task_tcb_init_written_field].
  repeat rewrite TaskFieldStorage.store_fields_cons by
    (repeat constructor; simpl; intuition discriminate).
  rewrite !TaskFieldStorage.store_fields_nil.
  cbn [task_tcb_init_raw_image tcb_cell tcb_field_address].
  unfold tcb_x_of_prio, tcb_y_of_prio, tcb_bit_x_of_prio, tcb_bit_y_of_prio.
  rewrite Hhead, Htable, Hgroup, Hrows, Hcount.
  rewrite Hprio, Htop, Hbottom, Hid, Hsize, Hext, Hopt, Hname.
  unfold task_tcb_init_stack_same_call in *; rewrite PreH20, PreH21 in *; entailer!; tauto.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_9 : OS_TCBInit_entail_wit_9.
Proof.
  unfold OS_TCBInit_entail_wit_9; right; intros.
  sep_apply_l_atomic (task_tcb_init_used_split_head_prev__publication_and_returns
    sg_phase_call_spec current_2 PreH31 PreH1).
  Intros previous.
  Exists previous slot_2 rest_2 free_image_2 acquired_2 current_2 current_call_2.
  cbn [tcb_cell tcb_field_address].
  entailer!.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_10_1 : OS_TCBInit_entail_wit_10_1.
Proof.
  unfold OS_TCBInit_entail_wit_10_1; right; intros.
  subst head ptcb.
  assert (Hconfiguration : sg_phase_call_spec.(osKernelConfig).(cfgEventMultiEnabled) = false /\
    sg_phase_call_spec.(osKernelConfig).(cfgTaskProfile) = false).
  { pose proof (proj1 PreH30) as Hprofile.
    unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto. }
  destruct Hconfiguration as [Hmulti Htaskprofile].
  pose proof (task_tcb_init_used_merge_head_prev__publication_and_returns
    sg_phase_call_spec current_2 slot_2) as Hmerge.
  rewrite task_slot_addr_tcb64 in Hmerge by assumption.
  cbn [tcb_cell tcb_field_address] in Hmerge.
  sep_apply_l_atomic Hmerge.
  Exists slot_2 rest_2 free_image_2 acquired_2 current_2 current_call_2.
  entailer!.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_10_2 : OS_TCBInit_entail_wit_10_2.
Proof.
  unfold OS_TCBInit_entail_wit_10_2; right; intros.
  pose proof (task_tcb_init_active_head_zero__publication_and_returns sg_phase_call_spec current_2
    PreH31 PreH1) as Hnone.
  Exists slot_2 rest_2 free_image_2 acquired_2 current_2 current_call_2.
  unfold task_tcb_init_used_with_head_prev, task_tcb_init_used_storage,
    task_tcb_init_head_updated_map.
  rewrite Hnone; entailer!.
Qed.

Lemma proof_of_OS_TCBInit_entail_wit_11 : OS_TCBInit_entail_wit_11.
Proof.
  unfold OS_TCBInit_entail_wit_11; right; intros.
  rewrite Z.quot_div_nonneg in * by lia.
  rewrite Z.rem_mod_nonneg in * by lia.
  pose proof PreH18 as Haddresses.
  destruct Haddresses as [Hfree [Hhead [Htable [Hgroup [Hrows Hcount]]]]].
  pose proof PreH19 as Harguments.
  destruct Harguments as [Hprio [Htop [Hbottom [Hid [Hsize [Hext [Hopt Hname]]]]]]].
  assert (Hconfiguration : sg_phase_call_spec.(osKernelConfig).(cfgEventMultiEnabled) = false /\
    sg_phase_call_spec.(osKernelConfig).(cfgTaskProfile) = false).
  { pose proof (proj1 PreH34) as Hprofile.
    unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto. }
  destruct Hconfiguration as [Hmulti Htaskprofile].
  pose proof (task_tcb_init_commit_binding_identity args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2 current_2
    slot_2 free_image_2 PreH33) as Hidentity.
  destruct (task_tcb_init_detached_flags_defined sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired_2
    slot_2 rest free_image_2 PreH22 PreH23) as [flags Hflags].
  assert (Hnot : ~ In slot_2 current_2.(SchedState).(readyList)).
  { pose proof (task_commit_identity_private _ _ _ _ Hidentity) as Hprivate.
    destruct (task_private_excludes_public sg_phase_call_spec current_2.(TskState) slot_2
      (proj1 (proj1 (proj2 PreH34))) Hprivate) as [Hnone _].
    intro Hin.
    destruct (proj1 (proj1 (proj1 (proj2 (proj2 PreH34)))) slot_2 Hin) as [t [Hget _]].
    congruence. }
  assert (Hprio_range : forall tid t, In tid current_2.(SchedState).(readyList) ->
    current_2.(TskState).(inUsedTaskStates) tid = Some t -> 0 <= t.(curPrio) < 64).
  { intros tid t Hin Hget.
    destruct (proj1 (proj1 (proj1 (proj2 (proj2 PreH34)))) tid Hin) as [other [Hother [Hp _]]].
    assert (other = t) by congruence; subst other.
    pose proof (proj1 (proj1 PreH34)) as Hsg.
    unfold valid_stable_glob_vars in Hsg.
    unfold task_priority_in_range in Hp; intuition lia. }
  pose proof (sched_commit_ready_encodings__publication_and_returns sg_phase_call_spec current_2.(TskState)
    current_2.(SchedState) args_phase_call_spec.(initPrio) invocation_phase_call_spec
    (task_tcb_init_commit_node args_phase_call_spec acquired_2 slot_2 free_image_2) Hnot) as [Hgrp Hrow].
  assert (Htable_eq : task_tcb_init_priority_table sg_phase_call_spec
    (task_tcb_init_published_state sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec acquired_2 current_2 slot_2 free_image_2) =
      replace_Znth prio_pre ptcb (task_tcb_init_priority_table sg_phase_call_spec current_2)).
  { subst ptcb; unfold task_tcb_init_priority_table.
    rewrite <- Hprio.
    pose proof (task_commit_priority_table_replace_eq__publication_and_returns sg_phase_call_spec
      current_2.(TskState) args_phase_call_spec.(initPrio) invocation_phase_call_spec
      (task_tcb_init_commit_node args_phase_call_spec acquired_2 slot_2 free_image_2)) as Heq.
    cbn [task_tcb_init_commit_node task_tcb_init_node_from_free_image taskID] in Heq.
    rewrite task_slot_addr_tcb64 in Heq by assumption.
    apply Heq; rewrite Hprio; lia. }
  assert (Hrows_eq : task_tcb_init_ready_rows
    (task_tcb_init_published_state sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec acquired_2 current_2 slot_2 free_image_2) =
    replace_Znth (prio_pre / 8)
      (Z.lor (Znth (prio_pre / 8) (task_tcb_init_ready_rows current_2) 0)
        (Z.shiftl 1 (prio_pre mod 8))) (task_tcb_init_ready_rows current_2)).
  { pose proof (sched_commit_rows_replace_eq__publication_and_returns sg_phase_call_spec current_2.(TskState)
      current_2.(SchedState) args_phase_call_spec.(initPrio) invocation_phase_call_spec
      (task_tcb_init_commit_node args_phase_call_spec acquired_2 slot_2 free_image_2) Hnot) as Heq.
    cbn [task_tcb_init_commit_node task_tcb_init_node_from_free_image curPrio] in Heq.
    rewrite Hprio in Heq; apply Heq; lia. }
  assert (Hgrp_eq : task_tcb_init_ready_group
    (task_tcb_init_published_state sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec acquired_2 current_2 slot_2 free_image_2) =
    Z.lor (task_tcb_init_ready_group current_2) (Z.shiftl 1 (prio_pre / 8))).
  { rewrite <- Hprio; exact Hgrp. }
  assert (Hcount_range : 0 <= task_tcb_init_count current_2 + 1 < 256).
  { pose proof (task_count_in_pool_range sg_phase_call_spec current_2.(TskState)
      (proj1 PreH34) (proj1 (proj2 PreH34))).
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
  assert (Hstorage : task_tcb_init_retained_without_links (tcb64_addr sg_phase_call_spec slot_2) (tcb_layout_common_image free_image_2) **
    task_tcb_init_written_storage (tcb64_addr sg_phase_call_spec slot_2) (task_tcb_init_raw_image args_phase_call_spec (tcb_layout_common_image free_image_2)) **
    tcb_cell (tcb64_addr sg_phase_call_spec slot_2) TCBNext (Some (task_tcb_init_active_head sg_phase_call_spec current_2)) **
    tcb_cell (tcb64_addr sg_phase_call_spec slot_2) TCBPrev (Some 0) |--
    tcb64_storage_rep (tcb64_addr sg_phase_call_spec slot_2)
      (task_tcb_init_linked_image sg_phase_call_spec current_2.(TskState).(tcbListHead)
        (task_tcb_init_raw_image args_phase_call_spec (tcb_layout_common_image free_image_2)))).
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
  assert (Himage : tcb_layout_common_image
    (task_tcb_init_linked_layout_image sg_phase_call_spec current_2.(TskState).(tcbListHead)
      (task_tcb_init_layout_image sg_phase_call_spec.(osKernelConfig).(cfgEventMultiEnabled)
        sg_phase_call_spec.(osKernelConfig).(cfgTaskProfile) args_phase_call_spec free_image_2)) =
    task_tcb_init_linked_image sg_phase_call_spec current_2.(TskState).(tcbListHead)
      (task_tcb_init_raw_image args_phase_call_spec (tcb_layout_common_image free_image_2))).
  { unfold task_tcb_init_layout_image; rewrite Hmulti, Htaskprofile.
    unfold tcb_layout_common_image, task_tcb_init_linked_layout_image,
      tcb_layout_write, task_tcb_init_linked_image.
    apply functional_extensionality; intros field; destruct field;
      cbn beta iota;
      repeat first [rewrite field_update_same | rewrite field_update_other by discriminate].
    all: try reflexivity.
    f_equal; apply encode_task_link_tcb64; assumption. }
  match goal with
  | |- ?resources |-- _ =>
    assert (Hcells : resources |--
      task_create_publication_storage sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec acquired_2 current_2 slot_2 free_image_2 **
      task_stack_storage region_phase_call_spec (task_create_stack_image TaskStackNoVFP create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec) **
      task_tcb_init_continuation_capsules environment_phase_call_spec saved_local_phase_call_spec current_2 **
      critical_region_masked (task_stack_call_platform environment_phase_call_spec) critical_phase_call_spec sg_phase_call_spec invocation_phase_call_spec origin_phase_call_spec cpu_sr current_2 **
      task_tcb_init_stack_context environment_phase_call_spec current_call_2 ** GlobalStrings_missing LitMap_phase_call_spec literals_phase_call_spec)
  end.
  { unfold task_create_publication_storage; cbv zeta.
    rewrite task_slot_storage_tcb64 by assumption.
    rewrite task_slot_addr_tcb64 by assumption.
    rewrite Himage.
    sepcon_assoc_change.
    sep_apply_r_atomic Hstorage.
    unfold task_tcb_init_written_storage, tcb64_fields_rep, tcb_fields.
    cbn [filter task_tcb_init_written_field].
    repeat rewrite TaskFieldStorage.store_fields_cons by
      (repeat constructor; simpl; intuition discriminate).
    rewrite !TaskFieldStorage.store_fields_nil.
    cbn [task_tcb_init_raw_image tcb_cell tcb_field_address].
    unfold tcb_x_of_prio, tcb_y_of_prio, tcb_bit_x_of_prio, tcb_bit_y_of_prio.
    entailer!. }
  sep_apply_l_atomic Hcells.
  rewrite Hname.
  pose proof (task_tcb_init_continuation_publication_sched_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec
    lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec "?") invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec acquired_2 current_2 slot_2 rest free_image_2
    current_call_2 PreH12 PreH13 PreH17)
    as Hhandover.
  rewrite <- PreH14 in Hhandover.
  specialize (Hhandover PreH22 PreH20 PreH23 PreH32 PreH33 PreH34 PreH35).
  sepcon_assoc_change; sep_apply_l_atomic Hhandover; Intros lease.
  assert (Htransport : forall other, task_tcb_init_stack_source_preserved other current_2
    (task_create_stack_publication_state sg_phase_call_spec
      (task_tcb_init_stack_publication region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec "?")
        invocation_phase_call_spec origin_phase_call_spec acquired_2 slot_2 free_image_2 lease) current_2)) by tauto.
  pose proof (task_tcb_init_stack_source_preserved_trans call_phase_call_spec initial_phase_call_spec current_2
    _ PreH6 (Htransport call_phase_call_spec)) as Hpreserved.
  Exists acquired_2 slot_2 free_image_2 lease current_2 current_call_2.
  unfold UCOS2_inv.
  entailer!.
  all: try solve [unfold task_tcb_init_arguments; intuition].
  all: try solve [unfold task_tcb_init_global_addresses; intuition].
Qed.


Lemma proof_of_OS_TCBInit_entail_wit_12 : OS_TCBInit_entail_wit_12.
Proof.
  unfold OS_TCBInit_entail_wit_12; right; intros.
  assert (Hresult : task_tcb_init_call_result sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec
    66 acquired_2).
  { apply TaskTCBInitCallNoFree; [exact PreH17| |exact (proj1 (proj2 (proj2 (proj2 PreH19))))|
      exact (proj1 PreH19)].
    apply (task_tcb_init_free_root_zero__publication_and_returns sg_phase_call_spec acquired_2
      (proj1 PreH19) PreH1). }
  pose proof PreH15 as Haddr; destruct Haddr as [Hfree Haddr].
  rewrite <- Hfree.
  sep_apply_l_atomic (proj2 (task_tcb_init_raw_split_free_root sg_phase_call_spec acquired_2)).
  Exists acquired_2 first_call_2.
  pose proof (proj1 PreH19) as Hvalid.
  unfold UCOS2_inv; entailer!.
  rewrite Hfree; exact PreH15.
Qed.

Lemma proof_of_OS_TCBInit_return_wit_1 : OS_TCBInit_return_wit_1.
Proof.
  left; intros.
  assert (Hresult : task_tcb_init_stack_call_result critical_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec
    (LitMap_phase_call_spec "?") invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec 66 acquired).
  { constructor; rewrite <- PreH10; exact PreH17. }
  pose proof (task_tcb_init_modular_return_phase_post environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec
    create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec "?") invocation_phase_call_spec origin_phase_call_spec mask_phase_call_spec initial_phase_call_spec call_phase_call_spec 66 acquired
    first_call cpu_sr PreH5 PreH7 Hresult PreH18 PreH2 PreH3 PreH4 PreH16) as Hpost.
  unfold task_tcb_init_stack_buffer_result in Hpost.
  destruct (Z.eq_dec 66 66); [|contradiction].
  sepcon_assoc_change; sep_apply_l_atomic Hpost; entailer!.
Qed.

Lemma proof_of_OS_TCBInit_return_wit_2 : OS_TCBInit_return_wit_2.
Proof.
  left; intros.
  rewrite PreH8, PreH9.
  set (publication := task_tcb_init_stack_publication region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec "?")
    invocation_phase_call_spec origin_phase_call_spec acquired slot free_image lease).
  assert (Hbody : task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec current_call
    (task_create_stack_publication_state sg_phase_call_spec publication current)).
  { eapply task_tcb_init_runtime_history_trans; [exact PreH3|].
    apply task_tcb_init_publication_runtime_history; exact PreH21. }
  pose proof (task_tcb_init_modular_return_phase_post environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec
    create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec "?") invocation_phase_call_spec origin_phase_call_spec mask_phase_call_spec initial_phase_call_spec call_phase_call_spec 0
    (task_create_stack_publication_state sg_phase_call_spec
    (task_tcb_init_stack_publication region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec "?")
      invocation_phase_call_spec origin_phase_call_spec acquired slot free_image lease) current)
    current_call cpu_sr PreH5 PreH7 PreH18 PreH19 PreH20 Hbody PreH4 PreH16) as Hpost.
  unfold task_tcb_init_stack_buffer_result in Hpost.
  destruct (Z.eq_dec 0 66); [discriminate|].
  assert (Hconsume : task_tcb_init_modular_restore_output environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec
    current_call cpu_sr (task_create_stack_publication_state sg_phase_call_spec publication current) |--
    task_tcb_init_modular_phase_call_post environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec region_phase_call_spec create_args_phase_call_spec task_return_phase_call_spec
      lower_phase_call_spec upper_phase_call_spec (LitMap_phase_call_spec "?") invocation_phase_call_spec origin_phase_call_spec mask_phase_call_spec initial_phase_call_spec call_phase_call_spec 0).
  { sep_apply_r_atomic Hpost; entailer!. }
  sep_apply_l_atomic Hconsume; entailer!.
Qed.

Lemma proof_of_OS_TCBInit_which_implies_wit_1 : OS_TCBInit_which_implies_wit_1.
Proof.
  left; intros.
  unfold task_tcb_init_continuation_call_pre, task_tcb_init_stack_pre, task_tcb_init_pre; Intros.
  assert (Hcall : call_phase_call_spec.(os_sched_call_invocation) = invocation_phase_call_spec /\ call_phase_call_spec.(os_sched_call_origin) = origin_phase_call_spec)
    by tauto.
  assert (Hentry : task_tcb_init_entry sg_phase_call_spec (task_tcb_init_stack_call_args create_args_phase_call_spec (LitMap_phase_call_spec "?"))
    invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec) by assumption.
  unfold task_tcb_init_continuation_save_input, task_create_continuation_input,
    task_tcb_init_continuation_capsules, kernel_call_execution_owned.
  destruct Hcall as [-> ->]; entailer!; exact (proj1 Hentry).
Qed.

Lemma proof_of_OS_TCBInit_which_implies_wit_2 : OS_TCBInit_which_implies_wit_2.
Proof.
  left; intros.
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_stack_context, task_tcb_init_continuation_capsules.
  rewrite PreH1, PreH2; entailer!.
Qed.

Lemma proof_of_OS_TCBInit_which_implies_wit_3 : OS_TCBInit_which_implies_wit_3.
Proof.
  left; intros.
  pose proof (task_create_default_name_binding_detached sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec initial_phase_call_spec
    acquired slot rest free_image (LitMap_phase_call_spec "?") PreH2 PreH1 PreH3) as Hbinding.
  sep_apply_l_atomic (task_tcb_init_literal_restore_split environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec
    first_call cpu_sr (task_tcb_init_detached_state args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image)
    (LitMap_phase_call_spec "?") Hbinding); entailer!.
Qed.

Lemma proof_of_OS_TCBInit_which_implies_wit_4 : OS_TCBInit_which_implies_wit_4.
Proof.
  left; intros; apply task_tcb_init_literal_restore_merge.
Qed.

Lemma proof_of_OS_TCBInit_which_implies_wit_5 : OS_TCBInit_which_implies_wit_5.
Proof.
  left; intros.
  sep_apply_l_atomic (task_tcb_init_modular_restore_phase_observation environment_phase_call_spec critical_phase_call_spec saved_local_phase_call_spec sg_phase_call_spec
    first_call cpu_sr (task_tcb_init_detached_state args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image)).
  Intros returned current.
  assert (Hvalid : UCOS2_state_inv sg_phase_call_spec
    (task_tcb_init_detached_state args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image)).
  { eapply (task_tcb_init_detach_preserves_validity sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image); eassumption. }
  assert (Htransport : task_tcb_init_stack_source_preserved first_call
    (task_tcb_init_detached_state args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image) current) by tauto.
  assert (Hpreserved : task_tcb_init_stack_source_preserved call_phase_call_spec initial_phase_call_spec current).
  { intros Hsource.
    apply (proj1 (task_tcb_init_stack_same_call_source_iff first_call call_phase_call_spec current PreH1)).
    apply Htransport.
    apply (proj2 (task_tcb_init_stack_same_call_source_iff first_call call_phase_call_spec _ PreH1)).
    apply (task_tcb_init_detach_preserves_call_source args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image call_phase_call_spec).
    apply PreH2; exact Hsource. }
  assert (Hhistory : task_tcb_init_runtime_history sg_phase_call_spec call_phase_call_spec initial_phase_call_spec returned current).
  { eapply (task_tcb_init_runtime_history_trans sg_phase_call_spec call_phase_call_spec initial_phase_call_spec first_call acquired returned current);
      [exact PreH3|].
    eapply (task_tcb_init_runtime_history_trans sg_phase_call_spec first_call acquired first_call
      (task_tcb_init_detached_state args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image) returned current).
    - exact (task_tcb_init_detach_runtime_history sg_phase_call_spec args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image first_call).
    - split; tauto. }
  pose proof (proj1 (proj1 Hhistory)) as Hsame.
  assert (Hinterval : task_tcb_init_call_preserved sg_phase_call_spec invocation_phase_call_spec
    (task_tcb_init_detached_state args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image) current).
  { assert (Hobserved : task_tcb_init_call_preserved sg_phase_call_spec first_call.(os_sched_call_invocation)
      (task_tcb_init_detached_state args_phase_call_spec invocation_phase_call_spec origin_phase_call_spec acquired slot rest free_image) current) by tauto.
    rewrite (proj1 PreH1), PreH8 in Hobserved; exact Hobserved. }
  rewrite (proj2 PreH10).
  Exists current returned.
  unfold task_tcb_init_timer_phase_eq in *.
  rewrite task_tcb_init_detached_timer_state_eq in *.
  entailer!; intuition congruence.
Qed.

Lemma proof_of_OS_TCBInit_which_implies_wit_6 : OS_TCBInit_which_implies_wit_6.
Proof.
  left; intros.
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_stack_context, task_tcb_init_continuation_capsules.
  rewrite PreH1, PreH2; entailer!.
Qed.

Lemma proof_of_OS_TCBInit_which_implies_wit_7 : OS_TCBInit_which_implies_wit_7.
Proof.
  left; intros.
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_stack_context, task_tcb_init_continuation_capsules.
  rewrite PreH1, PreH2; entailer!.
Qed.

Lemma proof_of_OS_TCBInit_derive_name_call_spec_by_phase_call_spec :
  OS_TCBInit_derive_name_call_spec_by_phase_call_spec.
Proof.
  unfold OS_TCBInit_derive_name_call_spec_by_phase_call_spec; intros.
  Exists environment_name_call_spec critical_name_call_spec saved_local_name_call_spec
    sg_name_call_spec args_name_call_spec region_name_call_spec create_args_name_call_spec
    task_return_name_call_spec lower_name_call_spec upper_name_call_spec call_name_call_spec
    invocation_name_call_spec origin_name_call_spec mask_name_call_spec initial_name_call_spec
    LitMap_name_call_spec literals_name_call_spec.
  entailer!.
  apply_sepcon_adjoint; elim_emp.
  Intros result.
  Exists result.
  sep_apply_l_atomic (task_tcb_init_modular_phase_call_post_forget
    environment_name_call_spec critical_name_call_spec saved_local_name_call_spec
    sg_name_call_spec region_name_call_spec create_args_name_call_spec task_return_name_call_spec
    lower_name_call_spec upper_name_call_spec (LitMap_name_call_spec "?") invocation_name_call_spec
    origin_name_call_spec mask_name_call_spec initial_name_call_spec call_name_call_spec result).
  entailer!.
Qed.
