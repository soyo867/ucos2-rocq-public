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
From Ucos2Verify.VC.code.task Require Import task_stk_chk_continuation_goal.
From Ucos2Verify.VC.code.task Require Import task_stk_chk_continuation_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.task.spec.task_stk_chk_continuation_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTaskStkChk_entail_wit_1_1 : OSTaskStkChk_entail_wit_1_1.
Proof.
left; intros.
  sep_apply_l_atomic (task_stk_chk_continuation_save_open
    environment critical saved_local sg original mask retval before caller_frame ltac:(assumption)).
  Intros active entry.
  Exists active entry; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_entail_wit_1_2 : OSTaskStkChk_entail_wit_1_2.
Proof.
left; intros.
  sep_apply_l_atomic (task_stk_chk_continuation_save_open
    environment critical saved_local sg original mask retval before caller_frame ltac:(assumption)).
  Intros active entry.
  Exists active entry; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_entail_wit_2_2 : OSTaskStkChk_entail_wit_2_2.
Proof.
  left; intros.
  unfold task_stk_chk_selected.
  rewrite (proj2 (Z.eqb_neq _ _) PreH1).
  entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_entail_wit_3 : OSTaskStkChk_entail_wit_3.
Proof.
  left; intros.
  pose proof PreH2 as [_ [_ [_ Hstate]]].
  pose proof PreH10 as [Hchecks [Hlowest Hself]].
  assert (Hrange : task_priority_in_range sg prio)
    by (unfold task_priority_in_range; lia).
  pose proof (task_stk_chk_null_table_entry__lookup_and_error_paths
    sg entry prio Hstate Hrange PreH1) as Hfree.
  assert (Harguments : task_stk_chk_valid_arguments prio_pre p_stk_data_pre).
  { eapply task_stk_chk_selected_valid_arguments__lookup_and_error_paths;
      [exact PreH14|lia|exact PreH17]. }
  assert (Hcritical : task_stk_chk_critical sg entry (task_stk_chk_continuation_frame environment saved_local sg active entry caller_frame) prio_pre
    p_stk_data_pre prio (TaskStackCheckError OS_ERR_TASK_NOT_EXIST)).
  { split; [exact PreH14|].
    apply task_stack_check_critical_explicit_free; [lia|exact Hrange|exact Hfree]. }
  assert (Herror : task_stk_chk_continuation_error_facts environment critical saved_local sg original active mask before
    caller_frame prio_pre p_stk_data_pre cpu_sr entry prio 67).
  { split; [exact PreH10|]. split; [exact Harguments|].
    split; [exact PreH2|]. exists OS_ERR_TASK_NOT_EXIST; split; [reflexivity|exact Hcritical]. }
  entailer!.
  apply UCOS2_C_Rules.store_ptr_undef_store_ptr.
Qed.

Lemma proof_of_OSTaskStkChk_entail_wit_4 : OSTaskStkChk_entail_wit_4.
Proof.
  left; intros.
  pose proof PreH11 as [Hchecks [Hlowest Hself]].
  pose proof PreH8 as [_ [_ Hlayout]].
  assert (Hrange : task_priority_in_range sg prio)
    by (unfold task_priority_in_range; lia).
  apply _derivable1_andp_intros.
  - sep_apply_l_atomic (task_stk_chk_reserved_table_entry
      sg entry prio Hlayout Hrange PreH1).
    coq_prop_lift.
    apply (coq_prop_andp_left (entry.(TskState).(prioTbl) prio = PTReserved));
      intro Hreserved.
    assert (Harguments : task_stk_chk_valid_arguments prio_pre p_stk_data_pre).
    { eapply task_stk_chk_selected_valid_arguments__lookup_and_error_paths;
        [exact PreH15|lia|exact PreH18]. }
    assert (Hcritical : task_stk_chk_critical sg entry (task_stk_chk_continuation_frame environment saved_local sg active entry caller_frame) prio_pre
      p_stk_data_pre prio (TaskStackCheckError OS_ERR_TASK_NOT_EXIST)).
    { split; [exact PreH15|].
      apply task_stack_check_critical_explicit_reserved; [lia|exact Hrange|exact Hreserved]. }
    assert (Herror : task_stk_chk_continuation_error_facts environment critical saved_local sg original active mask before
      caller_frame prio_pre p_stk_data_pre cpu_sr entry prio 67).
    { split; [exact PreH11|]. split; [exact Harguments|].
      split; [exact PreH3|]. exists OS_ERR_TASK_NOT_EXIST; split; [reflexivity|exact Hcritical]. }
    entailer!.
  - entailer!.
    apply UCOS2_C_Rules.store_ptr_undef_store_ptr.
Qed.

Lemma proof_of_OSTaskStkChk_entail_wit_5 : OSTaskStkChk_entail_wit_5.
Proof.
  left; intros.
  pose proof PreH4 as [Hchecks [Hlowest Hself]].
  pose proof PreH2 as [Htable [Hnode Hpointer]].
  assert (Hrange : task_priority_in_range sg prio)
    by (unfold task_priority_in_range; lia).
  assert (Harguments : task_stk_chk_valid_arguments prio_pre p_stk_data_pre).
  { eapply task_stk_chk_selected_valid_arguments__lookup_and_error_paths;
      [exact PreH6|lia|exact PreH26]. }
  assert (Hcritical : task_stk_chk_critical sg entry (task_stk_chk_continuation_frame environment saved_local sg active entry caller_frame) prio_pre
    p_stk_data_pre prio (TaskStackCheckError OS_ERR_TASK_OPT)).
  { split; [exact PreH6|].
    eapply task_stack_check_critical_explicit_option_error;
      [lia|exact Hrange|exact Htable|exact Hnode|exact PreH3]. }
  assert (Herror : task_stk_chk_continuation_error_facts environment critical saved_local sg original active mask before
    caller_frame prio_pre p_stk_data_pre cpu_sr entry prio 69).
  { split; [exact PreH4|]. split; [exact Harguments|].
    split; [exact PreH1|]. exists OS_ERR_TASK_OPT; split; [reflexivity|exact Hcritical]. }
  entailer!.
  apply UCOS2_C_Rules.store_ptr_undef_store_ptr.
Qed.

Lemma proof_of_OSTaskStkChk_entail_wit_7 : OSTaskStkChk_entail_wit_7.
Proof.
left; intros.
  assert (Harguments : task_stk_chk_valid_arguments prio_pre p_stk_data_pre).
  { eapply task_stk_chk_selected_valid_arguments__self_and_snapshot_fields;
      [exact PreH28|lia|exact PreH48]. }
  assert (Hcritical : task_stk_chk_critical sg entry
    (task_stk_chk_continuation_frame environment saved_local sg active entry caller_frame)
    prio_pre p_stk_data_pre prio (TaskStackCheckScan (task_stk_chk_node_snapshot slot node))).
  { split; [exact PreH28|].
    pose proof PreH26 as [Hchecks [Hlowest Hself]].
    pose proof PreH2 as [Htable [Hnode Hpointer]].
    unfold task_stk_chk_node_snapshot.
    apply task_stack_check_critical_explicit_scan.
    - rewrite Hself; lia.
    - unfold task_priority_in_range; rewrite Hlowest; lia.
    - exact Htable.
    - exact Hnode.
    - exact PreH25. }
  sep_apply_l_atomic (task_stk_chk_continuation_restore_scan_open environment critical saved_local
    sg original active mask before caller_frame prio_pre p_stk_data_pre cpu_sr entry prio
    (task_stk_chk_node_snapshot slot node) PreH26 Harguments PreH43 PreH1 Hcritical).
  Intros returned current region words count stop residual.
  Exists returned current (task_stk_chk_node_snapshot slot node) region words count stop residual.
  entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_entail_wit_9 : OSTaskStkChk_entail_wit_9.
Proof.
  unfold OSTaskStkChk_entail_wit_9; left; intros.
  subst nfree; entailer!; unfold task_stk_chk_count; lia.
Qed.

Lemma proof_of_OSTaskStkChk_entail_wit_10 : OSTaskStkChk_entail_wit_10.
Proof.
  unfold OSTaskStkChk_entail_wit_10; left; intros.
  assert (Hprefix : task_stk_chk_initialized_prefix snapshot region words count stop).
  { eapply task_stk_chk_continuation_scan_facts_prefix; exact PreH2. }
  assert (Hstop : stop <> 0).
  { unfold task_stk_chk_initialized_prefix, task_stack_scan_prefix in Hprefix; tauto. }
  assert (Hindex : index < task_stk_chk_count count).
  { eapply task_stk_chk_word_zero_index_lt__scan_loop_and_result; eauto; lia. }
  pose proof (task_stk_chk_prefix_uint32_count__scan_loop_and_result
    snapshot region words count stop Hprefix) as Hcount.
  assert (Hincrement : unsigned_last_nbits (index + 1) 32 = index + 1).
  { apply unsigned_last_nbits_eq; change (0 <= index + 1 < 4294967296); lia. }
  Exists index.
  rewrite Hincrement, sizeof_uint, PreH5; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_entail_wit_11 : OSTaskStkChk_entail_wit_11.
Proof.
  unfold OSTaskStkChk_entail_wit_11; left; intros.
  subst index.
  Exists size_2 0 (task_stk_chk_cursor snapshot 0) cpu_sr_2 prio_2.
  entailer!; lia.
Qed.

Lemma proof_of_OSTaskStkChk_entail_wit_12 : OSTaskStkChk_entail_wit_12.
Proof.
  unfold OSTaskStkChk_entail_wit_12; left; intros.
  assert (Hindex : index = task_stk_chk_count count).
  { eapply task_stk_chk_word_nonzero_index_eq__scan_loop_and_result; eauto; lia. }
  subst index.
  rewrite task_stk_chk_word_at_count__scan_loop_and_result, PreH5, sizeof_uint.
  entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_return_wit_1 : OSTaskStkChk_return_wit_1.
Proof.
left; intros.
  pose proof PreH1 as [Hconfig [Harguments [Hacquire [Hcritical
    [Hrestore_observation [Hrestore [Hinv Hview]]]]]]].
  pose proof (task_stk_chk_valid_arguments_no_error__scan_loop_and_result
    sg prio_pre p_stk_data_pre Hconfig Harguments) as Hargs.
  pose proof Hacquire as [Hbefore [Hsave_observation [Hsave Hentry]]].
  assert (Hsource : task_stk_chk_continuation_program environment critical saved_local sg original
    mask caller_frame prio_pre p_stk_data_pre before
    ((0, Some (task_stack_scan_data size count)), returned) after).
  { rewrite PreH5; unfold task_stk_chk_size.
    eapply task_stk_chk_continuation_program_scan; eassumption. }
  assert (Hresult : X 0 (Some (task_stack_scan_data size count)) after).
  { eapply task_stk_chk_continuation_safe_result; [exact PreH8|exact Hsource]. }
  pose proof (proj1 Hview) as Hprefix.
  Exists 0.
  unfold task_stk_chk_continuation_post.
  Exists returned (Some (task_stack_scan_data size count)) after.
  rewrite task_stk_chk_continuation_closed_equiv.
  unfold task_stk_chk_output_post.
  rewrite (task_stk_chk_scan_data_fields__scan_loop_and_result
    snapshot region words count stop size Hprefix) in Hsource, Hresult |- *.
  unfold task_stack_check_data_rep; cbn [stackCheckFree stackCheckUsed]; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_return_wit_2 : OSTaskStkChk_return_wit_2.
Proof.
right; intros.
  eapply task_stk_chk_continuation_error_finish; eassumption.
Qed.

Lemma proof_of_OSTaskStkChk_return_wit_3 : OSTaskStkChk_return_wit_3.
Proof.
right; intros.
  eapply task_stk_chk_continuation_error_finish; eassumption.
Qed.

Lemma proof_of_OSTaskStkChk_return_wit_4 : OSTaskStkChk_return_wit_4.
Proof.
right; intros.
  eapply task_stk_chk_continuation_error_finish; eassumption.
Qed.

Lemma proof_of_OSTaskStkChk_return_wit_5 : OSTaskStkChk_return_wit_5.
Proof.
left; intros.
  assert (Herror : task_stack_check_argument_error sg prio_pre p_stk_data_pre =
    Some OS_ERR_PDATA_NULL).
  { subst p_stk_data_pre.
    destruct PreH7 as [Hchecks [Hlowest Hself]].
    apply task_stack_check_argument_error_null; [exact Hchecks|].
    right; congruence. }

  assert (Hsource : task_stk_chk_continuation_program environment critical saved_local sg original
    mask caller_frame prio_pre p_stk_data_pre before ((9, None), original) before).
  { apply task_stk_chk_continuation_program_argument_error with (error := OS_ERR_PDATA_NULL); exact Herror. }
  assert (Hresult : X 9 None before).
  { eapply task_stk_chk_continuation_safe_result; [eassumption|exact Hsource]. }
  unfold task_stk_chk_output_pre; rewrite Herror.
  Exists 9.
  unfold task_stk_chk_continuation_post; Exists original (@None TaskStackCheckData) before.
  unfold task_stk_chk_output_post; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_return_wit_6 : OSTaskStkChk_return_wit_6.
Proof.
left; intros.
  assert (Herror : task_stack_check_argument_error sg prio_pre p_stk_data_pre =
    Some OS_ERR_PDATA_NULL).
  { subst p_stk_data_pre.
    destruct PreH6 as [Hchecks [Hlowest Hself]].
    apply task_stack_check_argument_error_null; [exact Hchecks|].
    left; lia. }

  assert (Hsource : task_stk_chk_continuation_program environment critical saved_local sg original
    mask caller_frame prio_pre p_stk_data_pre before ((9, None), original) before).
  { apply task_stk_chk_continuation_program_argument_error with (error := OS_ERR_PDATA_NULL); exact Herror. }
  assert (Hresult : X 9 None before).
  { eapply task_stk_chk_continuation_safe_result; [eassumption|exact Hsource]. }
  unfold task_stk_chk_output_pre; rewrite Herror.
  Exists 9.
  unfold task_stk_chk_continuation_post; Exists original (@None TaskStackCheckData) before.
  unfold task_stk_chk_output_post; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_return_wit_7 : OSTaskStkChk_return_wit_7.
Proof.
left; intros.
  assert (Herror : task_stack_check_argument_error sg prio_pre p_stk_data_pre =
    Some OS_ERR_PRIO_INVALID).
  { destruct PreH6 as [Hchecks [Hlowest Hself]].
    apply task_stack_check_argument_error_priority; [exact Hchecks|lia|congruence]. }

  assert (Hsource : task_stk_chk_continuation_program environment critical saved_local sg original
    mask caller_frame prio_pre p_stk_data_pre before ((42, None), original) before).
  { apply task_stk_chk_continuation_program_argument_error with (error := OS_ERR_PRIO_INVALID); exact Herror. }
  assert (Hresult : X 42 None before).
  { eapply task_stk_chk_continuation_safe_result; [eassumption|exact Hsource]. }
  unfold task_stk_chk_output_pre; rewrite Herror.
  Exists 42.
  unfold task_stk_chk_continuation_post; Exists original (@None TaskStackCheckData) before.
  unfold task_stk_chk_output_post; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_partial_solve_wit_1_pure : OSTaskStkChk_partial_solve_wit_1_pure.
Proof.
  left; intros; unfold task_stk_chk_valid_arguments; entailer!; lia.
Qed.

Lemma proof_of_OSTaskStkChk_partial_solve_wit_2_pure : OSTaskStkChk_partial_solve_wit_2_pure.
Proof.
  left; intros; unfold task_stk_chk_valid_arguments; entailer!; lia.
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_1 : OSTaskStkChk_which_implies_wit_1.
Proof.
  left; intros.
  assert (Herror : task_stack_check_argument_error sg prio p_stk_data = None).
  { destruct PreH1 as [Hchecks [Hlowest Hself]].
    destruct PreH2 as [Hrange [[Hprio|Hprio] Houtput]];
      unfold task_stack_check_argument_error;
      rewrite Hchecks, Hlowest, Hself,
        (proj2 (Z.eqb_neq _ _) Houtput).
    - rewrite (proj2 (Z.ltb_ge _ _) Hprio); reflexivity.
    - rewrite Hprio; reflexivity. }
  unfold task_stk_chk_output_pre; rewrite Herror.
  unfold task_stk_chk_output_undef; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_2 : OSTaskStkChk_which_implies_wit_2.
Proof.
  left; intros.
  unfold task_stack_check_data_rep, task_stack_check_zero_data; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_3 : OSTaskStkChk_which_implies_wit_3.
Proof.
  unfold OSTaskStkChk_which_implies_wit_3; left; intros.
  assert (Harguments : task_stk_chk_valid_arguments prio_pre p_stk_data).
  { unfold task_stk_chk_valid_arguments; subst prio_pre; lia. }
  pose proof (task_stk_chk_valid_arguments_no_error__self_and_snapshot_fields
    sg prio_pre p_stk_data PreH3 Harguments) as Herror.
  pose proof PreH2 as Hacquire.
  destruct Hacquire as [Hbefore [Hsave_observation [Hsave Hentry]]].
  destruct (proj1 (PreH1 Herror active cpu_sr entry Hsave Hentry) PreH4) as
    (selected & residual & Hview).
  Exists selected residual.
  pose proof Hview as Hview_parts.
  destruct Hview_parts as [Hrange [Hsplit Hmerge]].
  pose proof PreH6 as Haddresses.
  destruct Haddresses as [Hcurrent [Htable Hlayout]].
  unfold task_stk_chk_world in Hsplit.
  rewrite Hcurrent in Hsplit.
  unfold UCOS2_inv, task_stk_chk_residual.
  Intros.
  sep_apply_l_atomic Hsplit; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_4 : OSTaskStkChk_which_implies_wit_4.
Proof.
  unfold OSTaskStkChk_which_implies_wit_4; left; intros.
  assert (Hselected : task_stk_chk_selected sg entry (task_stk_chk_continuation_frame environment saved_local sg active entry caller_frame) prio_pre
    p_stk_data selected).
  { unfold task_stk_chk_selected; rewrite PreH4; simpl.
    exists residual; exact PreH2. }
  destruct PreH2 as [[Hlow Hhigh] [Hsplit Hmerge]].
  destruct PreH3 as [Hcurrent [Htable Hlayout]].
  pose proof PreH1 as Hacquire.
  destruct Hacquire as [Hbefore [Hsave_observation [Hsave Hentry]]].
  unfold task_stk_chk_world in Hmerge.
  rewrite Hcurrent in Hmerge.
  unfold task_stk_chk_residual, UCOS2_inv.
  cbn [tcb_field_address] in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_5 : OSTaskStkChk_which_implies_wit_5.
Proof.
  left; intros.
  pose proof PreH2 as [_ [Htable _]].
  pose proof (task_stk_chk_table_split sg entry prio ltac:(lia)) as Hsplit.
  rewrite Htable in Hsplit.
  sep_apply_l_atomic Hsplit; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_6 : OSTaskStkChk_which_implies_wit_6.
Proof.
  left; intros.
  pose proof PreH1 as [_ [_ [_ Hstate]]].
  pose proof PreH2 as [_ [Htable _]].
  pose proof (task_stk_chk_table_merge sg entry prio ltac:(lia)) as Hmerge.
  rewrite Htable in Hmerge.
  rewrite <- Hmerge; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_7 : OSTaskStkChk_which_implies_wit_7.
Proof.
left; intros.
  apply (proj2 (task_stk_chk_continuation_masked_equiv
    environment critical saved_local sg active cpu_sr entry entry caller_frame)).
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_8 : OSTaskStkChk_which_implies_wit_8.
Proof.
left; intros.
  apply (proj2 (task_stk_chk_continuation_masked_equiv
    environment critical saved_local sg active cpu_sr entry entry caller_frame)).
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_9 : OSTaskStkChk_which_implies_wit_9.
Proof.
  left; intros.
  pose proof PreH1 as [Hchecks [Hlowest Hself]].
  pose proof PreH2 as [_ [_ [_ Hstate]]].
  assert (Hrange : task_priority_in_range sg prio)
    by (unfold task_priority_in_range; lia).
  destruct (entry.(TskState).(prioTbl) prio) as [| |slot] eqn:Htable.
  - unfold task_stk_chk_table_pointer in PreH6; rewrite Htable in PreH6;
      change (ptcb = 0) in PreH6; contradiction.
  - unfold task_stk_chk_table_pointer in PreH6; rewrite Htable in PreH6;
      change (ptcb = 1) in PreH6; contradiction.
  - destruct (task_stk_chk_table_task_live sg entry prio slot
      Hstate Hrange Htable) as [node Hnode].
    assert (Hpointer : ptcb = task_slot_addr sg slot).
    { unfold task_stk_chk_table_pointer in PreH6; rewrite Htable in PreH6;
        exact PreH6. }
    assert (Hselected_node : task_stk_chk_node sg entry prio ptcb slot node)
      by (repeat split; assumption).
    pose proof (task_stk_chk_field_split sg entry slot node TCBOpt Hnode) as Hsplit.
    cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell]
      in Hsplit.
    Exists slot node.
    rewrite Hpointer in Hselected_node.
    rewrite Hpointer.
    sep_apply_l_atomic Hsplit; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_10 : OSTaskStkChk_which_implies_wit_10.
Proof.
  unfold OSTaskStkChk_which_implies_wit_10; right; intros.
  destruct PreH2 as [Htable [Hnode Hpointer]]; subst ptcb.
  destruct PreH1 as [Hbefore [Hsave_observation [Hsave Hentry]]].
  pose proof (task_stk_chk_field_merge sg entry slot node TCBOpt Hnode) as Hmerge.
  cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image
    tcb_cell] in Hmerge.
  unfold task_stk_chk_node_option.
  rewrite <- Hmerge; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_11 : OSTaskStkChk_which_implies_wit_11.
Proof.
left; intros.
  apply (proj2 (task_stk_chk_continuation_masked_equiv
    environment critical saved_local sg active cpu_sr entry entry caller_frame)).
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_12 : OSTaskStkChk_which_implies_wit_12.
Proof.
  unfold OSTaskStkChk_which_implies_wit_12; right; intros.
  destruct PreH2 as [Htable [Hnode Hpointer]]; subst ptcb.
  destruct PreH1 as [Hbefore [Hsave_observation [Hsave Hentry]]].
  pose proof (task_stk_chk_field_merge sg entry slot node TCBOpt Hnode) as Hmerge.
  cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image
    tcb_cell] in Hmerge.
  unfold task_stk_chk_node_option.
  rewrite <- Hmerge; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_13 : OSTaskStkChk_which_implies_wit_13.
Proof.
  unfold OSTaskStkChk_which_implies_wit_13; right; intros.
  destruct PreH2 as [Htable [Hnode Hpointer]]; subst ptcb.
  pose proof (task_stk_chk_field_split sg entry slot node TCBStkSize Hnode) as Hsplit.
  cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image
    tcb_cell] in Hsplit.
  unfold task_stk_chk_node_size.
  sep_apply_l_atomic Hsplit; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_14 : OSTaskStkChk_which_implies_wit_14.
Proof.
  unfold OSTaskStkChk_which_implies_wit_14; left; intros.
  pose proof PreH2 as Hnode_info.
  destruct Hnode_info as [Htable [Hnode Hpointer]]; subst ptcb.
  pose proof PreH1 as Hacquire.
  destruct Hacquire as [Hbefore [Hsave_observation [Hsave Hentry]]].
  pose proof (task_stk_chk_field_merge sg entry slot node TCBStkSize Hnode) as Hmerge.
  cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image
    tcb_cell] in Hmerge.
  unfold task_stk_chk_node_size.
  rewrite <- Hmerge; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_15 : OSTaskStkChk_which_implies_wit_15.
Proof.
  unfold OSTaskStkChk_which_implies_wit_15; right; intros.
  destruct PreH2 as [Htable [Hnode Hpointer]]; subst ptcb.
  pose proof (task_stk_chk_field_split sg entry slot node TCBStkBottom Hnode) as Hsplit.
  cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image
    tcb_cell] in Hsplit.
  unfold task_stk_chk_node_bottom.
  sep_apply_l_atomic Hsplit; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_16 : OSTaskStkChk_which_implies_wit_16.
Proof.
  unfold OSTaskStkChk_which_implies_wit_16; right; intros.
  destruct PreH2 as [Htable [Hnode Hpointer]]; subst ptcb.
  destruct PreH1 as [Hbefore [Hsave_observation [Hsave Hentry]]].
  pose proof (task_stk_chk_field_merge sg entry slot node TCBStkBottom Hnode) as Hmerge.
  cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image
    tcb_cell] in Hmerge.
  unfold task_stk_chk_node_bottom.
  rewrite <- Hmerge; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_17 : OSTaskStkChk_which_implies_wit_17.
Proof.
left; intros.
  apply (proj2 (task_stk_chk_continuation_masked_equiv
    environment critical saved_local sg active cpu_sr entry entry caller_frame)).
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_18 : OSTaskStkChk_which_implies_wit_18.
Proof.
left; intros.
  pose proof PreH1 as [_ [_ [_ [_ [_ [_ [Hinv [Hprefix [Hsplit Hmerge]]]]]]]]].
  assert (Hcursor : pchk = task_stk_chk_cursor snapshot 0).
  { unfold task_stk_chk_cursor, task_stk_chk_bottom in *; lia. }
  unfold UCOS2_inv; Intros.
  unfold task_stk_chk_world in Hsplit.
  sep_apply_l_atomic Hsplit.
  unfold task_stk_chk_cursor, task_stk_chk_scan_read_frame.
  sep_apply_l_atomic (task_stk_chk_initialized_prefix_split_word
    snapshot region words count stop 0 Hprefix ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_19 : OSTaskStkChk_which_implies_wit_19.
Proof.
  unfold OSTaskStkChk_which_implies_wit_19; left; intros.
  assert (Hprefix : task_stk_chk_initialized_prefix snapshot region words count stop).
  { eapply task_stk_chk_continuation_scan_facts_prefix; exact PreH1. }
  pose proof (task_stk_chk_cursor_successor__scan_loop_and_result
    snapshot previous) as Hsuccessor.
  unfold task_stk_chk_cursor, task_stk_chk_scan_read_frame.
  sep_apply_l_atomic (task_stk_chk_initialized_prefix_merge_word
    snapshot region words count stop previous Hprefix
    ltac:(unfold task_stk_chk_count in *; lia)).
  sep_apply_l_atomic (task_stk_chk_initialized_prefix_split_word
    snapshot region words count stop (previous + 1) Hprefix
    ltac:(unfold task_stk_chk_count in *; lia)).
  Exists (previous + 1).
  entailer!; unfold task_stk_chk_cursor in *; lia.
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_20 : OSTaskStkChk_which_implies_wit_20.
Proof.
left; intros.
  pose proof PreH1 as [_ [_ [_ [_ [_ [_ [Hinv [Hprefix [Hsplit Hmerge]]]]]]]]].
  unfold task_stk_chk_cursor, task_stk_chk_count, task_stk_chk_scan_read_frame.
  sep_apply_l_atomic (task_stk_chk_initialized_prefix_merge_stop
    snapshot region words count stop Hprefix).
  unfold task_stk_chk_world in Hmerge.
  unfold UCOS2_inv; sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma proof_of_OSTaskStkChk_which_implies_wit_21 : OSTaskStkChk_which_implies_wit_21.
Proof.
  left; intros.
  unfold task_stack_check_data_rep, task_stack_check_zero_data; entailer!.
Qed.
