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
From Ucos2Verify.VC.code.task Require Import task_del_goal.
From Ucos2Verify.VC.code.task Require Import task_del_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.task.spec.task_del_api_spec Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.task Ucos2Verify.lib.task_storage Ucos2Verify.lib.task_retirement Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules ListNotations.
Local Open Scope sac.

Lemma proof_of_OSTaskDel_entail_wit_1_7 : OSTaskDel_entail_wit_1_7.
Proof.
  right; intros.
  unfold task_delete_ptr_cell; cbn [tcb_field_address].
  sep_apply_l_atomic (task_delete_focus_reassemble
    (tcb_field_address (task_slot_addr sg tid) TCBEventPtr # Ptr |->
      task_delete_event_handle sg node)
    (task_delete_ready_body environment critical saved_local sg requested call initial
      current saved acquired priority (task_slot_addr sg tid) tid node)).
  unfold task_delete_ready_body; Intros.
  assert (Hhistory : task_delete_live_history sg requested call initial current acquired
    priority (task_slot_addr sg tid) tid node) by assumption.
  destruct (task_delete_live_history_inv_and_lookup__event_and_flag_unlink
    _ _ _ _ _ _ _ _ _ _ Hhistory) as [Hvalid Hnode].
  pose proof (task_event_handle_zero_implies_none__event_and_flag_unlink
    sg acquired tid node Hvalid Hnode PreH1) as Hnull.
  unfold task_delete_event_body.
  Exists (task_delete_ready_state acquired tid) node.
  entailer!; unfold task_delete_event_unlinked; rewrite Hnull; auto.
Qed. 

Lemma proof_of_OSTaskDel_entail_wit_1_8 : OSTaskDel_entail_wit_1_8.
Proof.
  right; intros.
  unfold task_delete_ptr_cell; cbn [tcb_field_address].
  sep_apply_l_atomic (task_delete_focus_reassemble
    (tcb_field_address (task_slot_addr sg tid) TCBEventPtr # Ptr |->
      task_delete_event_handle sg node)
    (task_delete_ready_body environment critical saved_local sg requested call initial
      current saved acquired priority (task_slot_addr sg tid) tid node)).
  unfold task_delete_ready_body; Intros.
  assert (Hhistory : task_delete_live_history sg requested call initial current acquired
    priority (task_slot_addr sg tid) tid node) by assumption.
  destruct (task_delete_live_history_inv_and_lookup__event_and_flag_unlink
    _ _ _ _ _ _ _ _ _ _ Hhistory) as [Hvalid Hnode].
  pose proof (task_event_handle_zero_implies_none__event_and_flag_unlink
    sg acquired tid node Hvalid Hnode PreH1) as Hnull.
  unfold task_delete_event_body.
  Exists (task_delete_ready_state acquired tid) node.
  entailer!; unfold task_delete_event_unlinked; rewrite Hnull; auto.
Qed. 

Lemma proof_of_OSTaskDel_entail_wit_1_9 : OSTaskDel_entail_wit_1_9.
Proof.
  right; intros.
  unfold task_delete_ptr_cell; cbn [tcb_field_address].
  sep_apply_l_atomic (task_delete_focus_reassemble
    (tcb_field_address (task_slot_addr sg tid) TCBEventPtr # Ptr |->
      task_delete_event_handle sg node)
    (task_delete_ready_body environment critical saved_local sg requested call initial
      current saved acquired priority (task_slot_addr sg tid) tid node)).
  unfold task_delete_ready_body; Intros.
  assert (Hhistory : task_delete_live_history sg requested call initial current acquired
    priority (task_slot_addr sg tid) tid node) by assumption.
  destruct (task_delete_live_history_inv_and_lookup__event_and_flag_unlink
    _ _ _ _ _ _ _ _ _ _ Hhistory) as [Hvalid Hnode].
  pose proof (task_event_handle_zero_implies_none__event_and_flag_unlink
    sg acquired tid node Hvalid Hnode PreH1) as Hnull.
  unfold task_delete_event_body.
  Exists (task_delete_ready_state acquired tid) node.
  entailer!; unfold task_delete_event_unlinked; rewrite Hnull; auto.
Qed. 

Lemma proof_of_OSTaskDel_entail_wit_1_10 : OSTaskDel_entail_wit_1_10.
Proof.
  right; intros.
  unfold task_delete_ptr_cell; cbn [tcb_field_address].
  sep_apply_l_atomic (task_delete_focus_reassemble
    (tcb_field_address (task_slot_addr sg tid) TCBEventPtr # Ptr |->
      task_delete_event_handle sg node)
    (task_delete_ready_body environment critical saved_local sg requested call initial
      current saved acquired priority (task_slot_addr sg tid) tid node)).
  unfold task_delete_ready_body; Intros.
  assert (Hhistory : task_delete_live_history sg requested call initial current acquired
    priority (task_slot_addr sg tid) tid node) by assumption.
  destruct (task_delete_live_history_inv_and_lookup__event_and_flag_unlink
    _ _ _ _ _ _ _ _ _ _ Hhistory) as [Hvalid Hnode].
  pose proof (task_event_handle_zero_implies_none__event_and_flag_unlink
    sg acquired tid node Hvalid Hnode PreH1) as Hnull.
  unfold task_delete_event_body.
  Exists (task_delete_ready_state acquired tid) node.
  entailer!; unfold task_delete_event_unlinked; rewrite Hnull; auto.
Qed. 

Lemma proof_of_OSTaskDel_entail_wit_1_11 : OSTaskDel_entail_wit_1_11.
Proof.
  right; intros.
  unfold task_delete_ptr_cell; cbn [tcb_field_address].
  sep_apply_l_atomic (task_delete_focus_reassemble
    (tcb_field_address (task_slot_addr sg tid) TCBEventPtr # Ptr |->
      task_delete_event_handle sg node)
    (task_delete_ready_body environment critical saved_local sg requested call initial
      current saved acquired priority (task_slot_addr sg tid) tid node)).
  unfold task_delete_ready_body; Intros.
  assert (Hhistory : task_delete_live_history sg requested call initial current acquired
    priority (task_slot_addr sg tid) tid node) by assumption.
  destruct (task_delete_live_history_inv_and_lookup__event_and_flag_unlink
    _ _ _ _ _ _ _ _ _ _ Hhistory) as [Hvalid Hnode].
  pose proof (task_event_handle_zero_implies_none__event_and_flag_unlink
    sg acquired tid node Hvalid Hnode PreH1) as Hnull.
  unfold task_delete_event_body.
  Exists (task_delete_ready_state acquired tid) node.
  entailer!; unfold task_delete_event_unlinked; rewrite Hnull; auto.
Qed. 

Lemma proof_of_OSTaskDel_entail_wit_1_12 : OSTaskDel_entail_wit_1_12.
Proof.
  right; intros.
  unfold task_delete_ptr_cell; cbn [tcb_field_address].
  sep_apply_l_atomic (task_delete_focus_reassemble
    (tcb_field_address (task_slot_addr sg tid) TCBEventPtr # Ptr |->
      task_delete_event_handle sg node)
    (task_delete_ready_body environment critical saved_local sg requested call initial
      current saved acquired priority (task_slot_addr sg tid) tid node)).
  unfold task_delete_ready_body; Intros.
  assert (Hhistory : task_delete_live_history sg requested call initial current acquired
    priority (task_slot_addr sg tid) tid node) by assumption.
  destruct (task_delete_live_history_inv_and_lookup__event_and_flag_unlink
    _ _ _ _ _ _ _ _ _ _ Hhistory) as [Hvalid Hnode].
  pose proof (task_event_handle_zero_implies_none__event_and_flag_unlink
    sg acquired tid node Hvalid Hnode PreH1) as Hnull.
  unfold task_delete_event_body.
  Exists (task_delete_ready_state acquired tid) node.
  entailer!; unfold task_delete_event_unlinked; rewrite Hnull; auto.
Qed. 

Lemma proof_of_OSTaskDel_entail_wit_2_2 : OSTaskDel_entail_wit_2_2.
Proof.
  right; intros.
  unfold task_delete_ptr_cell; cbn [tcb_field_address].
  sep_apply_l_atomic (task_delete_focus_reassemble
    (tcb_field_address (task_slot_addr sg tid) TCBFlagNode # Ptr |->
      task_delete_flag_handle event_node)
    (task_delete_masked_raw environment critical saved_local None sg current saved acquired evented)).
  unfold task_delete_flag_body.
  Exists evented event_node evented event_node (@None FlagWaiterState).
  entailer!.
  unfold task_delete_flag_unlinked, task_delete_flag_handle in *.
  rewrite PreH1, Z.eqb_refl; auto.
Qed.

Lemma proof_of_OSTaskDel_entail_wit_3_1 : OSTaskDel_entail_wit_3_1.
Proof.
  left; intros.
  rewrite (task_delete_added_value_below_saturation flagged PreH3).
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_entail_wit_3_2 : OSTaskDel_entail_wit_3_2.
Proof.
  left; intros.
  rewrite (task_delete_added_value_at_saturation flagged ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_return_wit_7 : OSTaskDel_return_wit_7.
Proof.
  left; intros.
  unfold task_delete_uchar_cell.
  sep_apply task_delete_focus_reassemble.
  sep_apply (task_delete_final_body_api_post environment critical saved_local sg
    requested (LitMap "?") call mask initial final_call final_state
    (task_delete_cut sg prepared resumed tid priority node (LitMap "?")) loan X
    ltac:(intro Hr; apply PreH1; rewrite Hr; reflexivity) PreH19).
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_return_wit_8 : OSTaskDel_return_wit_8.
Proof.
  left; intros.
  unfold task_delete_uchar_cell.
  sep_apply task_delete_focus_reassemble.
  sep_apply (task_delete_final_body_api_post environment critical saved_local sg
    requested (LitMap "?") call mask initial final_call final_state
    (task_delete_cut sg prepared resumed tid priority node (LitMap "?")) loan X
    ltac:(intro Hr; apply PreH1; rewrite Hr; reflexivity) PreH18).
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_return_wit_9 : OSTaskDel_return_wit_9.
Proof.
  left; intros.
  unfold task_delete_uchar_cell.
  sep_apply task_delete_focus_reassemble.
  sep_apply (task_delete_final_body_api_post environment critical saved_local sg
    requested (LitMap "?") call mask initial final_call final_state
    (task_delete_cut sg prepared resumed tid priority node (LitMap "?")) loan X
    ltac:(intro Hr; apply PreH1; rewrite Hr; reflexivity) PreH19).
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_return_wit_10 : OSTaskDel_return_wit_10.
Proof.
  left; intros.
  unfold task_delete_uchar_cell.
  sep_apply task_delete_focus_reassemble.
  sep_apply (task_delete_final_body_api_post environment critical saved_local sg
    requested (LitMap "?") call mask initial final_call final_state
    (task_delete_cut sg prepared resumed tid priority node (LitMap "?")) loan X
    ltac:(intro Hr; apply PreH1; rewrite Hr; reflexivity) PreH19).
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_return_wit_11 : OSTaskDel_return_wit_11.
Proof.
  left; intros.
  unfold task_delete_uchar_cell.
  sep_apply task_delete_focus_reassemble.
  sep_apply (task_delete_final_body_api_post environment critical saved_local sg
    requested (LitMap "?") call mask initial final_call final_state
    (task_delete_cut sg prepared resumed tid priority node (LitMap "?")) loan X
    ltac:(intro Hr; apply PreH1; rewrite Hr; reflexivity) PreH18).
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_return_wit_12 : OSTaskDel_return_wit_12.
Proof.
  left; intros.
  unfold task_delete_uchar_cell.
  sep_apply task_delete_focus_reassemble.
  sep_apply (task_delete_final_body_api_post environment critical saved_local sg
    requested (LitMap "?") call mask initial final_call final_state
    (task_delete_cut sg prepared resumed tid priority node (LitMap "?")) loan X
    ltac:(intro Hr; apply PreH1; rewrite Hr; reflexivity) PreH19).
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_return_wit_13 : OSTaskDel_return_wit_13.
Proof.
  left; intros.
  pose proof (task_delete_table_reserved_lookup__prefix_and_error_returns
    sg acquired priority PreH14 PreH1) as Hlookup.
  pose proof (task_delete_lookup_error_api_post
    environment critical saved_local sg requested (LitMap "?") call mask initial
    current acquired priority error_codes.OS_ERR_TASK_DEL X PreH11 (proj1 PreH5) Hlookup
    ltac:(discriminate) PreH29) as Hpost.
  rewrite <- PreH8, (proj2 PreH12).
  sep_apply_l_atomic Hpost; entailer!.
Qed. 

Lemma proof_of_OSTaskDel_return_wit_14 : OSTaskDel_return_wit_14.
Proof.
  left; intros.
  pose proof (task_delete_table_reserved_lookup__prefix_and_error_returns
    sg acquired priority PreH11 PreH1) as Hlookup.
  pose proof (task_delete_lookup_error_api_post
    environment critical saved_local sg requested (LitMap "?") call mask initial
    current acquired priority error_codes.OS_ERR_TASK_DEL X PreH8 (proj1 PreH5) Hlookup
    ltac:(discriminate) PreH26) as Hpost.
  rewrite (proj2 PreH9).
  sep_apply_l_atomic Hpost; entailer!.
Qed. 

Lemma proof_of_OSTaskDel_return_wit_15 : OSTaskDel_return_wit_15.
Proof.
  left; intros.
  pose proof (task_delete_table_reserved_lookup__prefix_and_error_returns
    sg acquired priority PreH11 PreH1) as Hlookup.
  pose proof (task_delete_lookup_error_api_post
    environment critical saved_local sg requested (LitMap "?") call mask initial
    current acquired priority error_codes.OS_ERR_TASK_DEL X PreH8 (proj1 PreH5) Hlookup
    ltac:(discriminate) PreH25) as Hpost.
  rewrite (proj2 PreH9).
  sep_apply_l_atomic Hpost; entailer!.
Qed. 

Lemma proof_of_OSTaskDel_return_wit_16 : OSTaskDel_return_wit_16.
Proof.
  left; intros.
  assert (Hvalid : UCOS2_state_inv sg acquired).
  { unfold task_delete_lookup_history, task_delete_phase_rely,
      task_delete_phase_valid in PreH10; tauto. }
  assert (Hrange : task_priority_in_range sg priority).
  { pose proof PreH13 as [[Hstable Hprofile] Hrest].
    unfold task_priority_in_range, valid_stable_glob_vars in *; lia. }
  pose proof (task_delete_table_null_lookup__prefix_and_error_returns
    sg acquired priority PreH13 Hvalid Hrange PreH1) as Hlookup.
  pose proof (task_delete_lookup_error_api_post
    environment critical saved_local sg requested (LitMap "?") call mask initial
    current acquired priority error_codes.OS_ERR_TASK_NOT_EXIST X PreH10 (proj1 PreH4) Hlookup
    ltac:(discriminate) PreH28) as Hpost.
  rewrite <- PreH7, (proj2 PreH11).
  sep_apply_l_atomic Hpost; entailer!.
Qed. 

Lemma proof_of_OSTaskDel_return_wit_17 : OSTaskDel_return_wit_17.
Proof.
  left; intros.
  assert (Hvalid : UCOS2_state_inv sg acquired).
  { unfold task_delete_lookup_history, task_delete_phase_rely,
      task_delete_phase_valid in PreH7; tauto. }
  assert (Hrange : task_priority_in_range sg priority).
  { pose proof PreH10 as [[Hstable Hprofile] Hrest].
    unfold task_priority_in_range, valid_stable_glob_vars in *; lia. }
  pose proof (task_delete_table_null_lookup__prefix_and_error_returns
    sg acquired priority PreH10 Hvalid Hrange PreH1) as Hlookup.
  pose proof (task_delete_lookup_error_api_post
    environment critical saved_local sg requested (LitMap "?") call mask initial
    current acquired priority error_codes.OS_ERR_TASK_NOT_EXIST X PreH7 (proj1 PreH4) Hlookup
    ltac:(discriminate) PreH25) as Hpost.
  rewrite (proj2 PreH8).
  sep_apply_l_atomic Hpost; entailer!.
Qed. 

Lemma proof_of_OSTaskDel_return_wit_18 : OSTaskDel_return_wit_18.
Proof.
  left; intros.
  assert (Hvalid : UCOS2_state_inv sg acquired).
  { unfold task_delete_lookup_history, task_delete_phase_rely,
      task_delete_phase_valid in PreH7; tauto. }
  assert (Hrange : task_priority_in_range sg priority).
  { pose proof PreH10 as [[Hstable Hprofile] Hrest].
    unfold task_priority_in_range, valid_stable_glob_vars in *; lia. }
  pose proof (task_delete_table_null_lookup__prefix_and_error_returns
    sg acquired priority PreH10 Hvalid Hrange PreH1) as Hlookup.
  pose proof (task_delete_lookup_error_api_post
    environment critical saved_local sg requested (LitMap "?") call mask initial
    current acquired priority error_codes.OS_ERR_TASK_NOT_EXIST X PreH7 (proj1 PreH4) Hlookup
    ltac:(discriminate) PreH24) as Hpost.
  rewrite (proj2 PreH8).
  sep_apply_l_atomic Hpost; entailer!.
Qed. 

Lemma proof_of_OSTaskDel_return_wit_19 : OSTaskDel_return_wit_19.
Proof.
  left; intros.
  prop_apply (store_uchar_range ( &( "OSIntNesting" ) ) (task_delete_ints initial)); Intros.
  change (0 <= task_delete_ints initial <= 255) in H.
  rewrite (unsigned_last_nbits_eq (task_delete_ints initial) 32 ltac:(change (0 <= (task_delete_ints initial) < 4294967296); lia)) in PreH4.
  pose proof (task_delete_focus_reassemble
    (task_delete_uchar_cell ( &( "OSIntNesting" ) ) (task_delete_ints initial))
    (task_delete_entry environment critical saved_local completed sg requested call mask initial))
    as Hentry.
  unfold task_delete_uchar_cell in Hentry; sep_apply Hentry.
  prop_apply (task_delete_entry_profile_and_priority__prefix_and_error_returns
    environment critical saved_local completed sg requested call mask initial); Intros.
  assert (Hstatic : task_delete_static_profile sg) by tauto.
  assert (Hrequested : 0 <= requested <= 255) by tauto.
  assert (Hpriority : 0 <= prio_pre <= 255) by lia.
  rewrite (unsigned_last_nbits_eq prio_pre 32 ltac:(change (0 <= prio_pre < 4294967296); lia)) in PreH1, PreH2.
  assert (Herr : task_delete_prefix_error sg false initial.(IntrState).(intNesting)
    requested = Some error_codes.OS_ERR_PRIO_INVALID).
  { rewrite task_delete_prefix_error_selected_profile__prefix_and_error_returns by exact Hstatic.
    assert (Hzero : initial.(IntrState).(intNesting) = 0)
      by (unfold task_delete_ints in H, PreH4; lia).
    rewrite Hzero; cbn.
    rewrite (proj2 (Z.eqb_neq requested 63) ltac:(lia)),
      (proj2 (Z.leb_le 63 requested) ltac:(lia)),
      (proj2 (Z.eqb_neq requested 255) ltac:(lia)); reflexivity. }
  sep_apply_l_atomic (task_delete_prefix_error_api_post
    environment critical saved_local completed sg requested (LitMap "?") call mask initial
    error_codes.OS_ERR_PRIO_INVALID X Herr PreH10); entailer!.
Qed. 

Lemma proof_of_OSTaskDel_return_wit_20 : OSTaskDel_return_wit_20.
Proof.
  left; intros.
  prop_apply (store_uchar_range ( &( "OSIntNesting" ) ) (task_delete_ints initial)); Intros.
  change (0 <= task_delete_ints initial <= 255) in H.
  rewrite (unsigned_last_nbits_eq (task_delete_ints initial) 32 ltac:(change (0 <= (task_delete_ints initial) < 4294967296); lia)) in PreH2.
  pose proof (task_delete_focus_reassemble
    (task_delete_uchar_cell ( &( "OSIntNesting" ) ) (task_delete_ints initial))
    (task_delete_entry environment critical saved_local completed sg requested call mask initial))
    as Hentry.
  unfold task_delete_uchar_cell in Hentry; sep_apply Hentry.
  prop_apply (task_delete_entry_profile_and_priority__prefix_and_error_returns
    environment critical saved_local completed sg requested call mask initial); Intros.
  assert (Hstatic : task_delete_static_profile sg) by tauto.
  assert (Hrequested : 0 <= requested <= 255) by tauto.
  assert (Herr : task_delete_prefix_error sg false initial.(IntrState).(intNesting)
    requested = Some error_codes.OS_ERR_TASK_DEL_IDLE).
  { rewrite task_delete_prefix_error_selected_profile__prefix_and_error_returns by exact Hstatic.
    assert (Hzero : initial.(IntrState).(intNesting) = 0)
      by (unfold task_delete_ints in H, PreH2; lia).
    assert (Hidle : requested = 63) by lia.
    rewrite Hzero, Hidle; reflexivity. }
  sep_apply_l_atomic (task_delete_prefix_error_api_post
    environment critical saved_local completed sg requested (LitMap "?") call mask initial
    error_codes.OS_ERR_TASK_DEL_IDLE X Herr PreH8); entailer!.
Qed. 

Lemma proof_of_OSTaskDel_return_wit_21 : OSTaskDel_return_wit_21.
Proof.
  left; intros.
  prop_apply (store_uchar_range ( &( "OSIntNesting" ) ) (task_delete_ints initial)); Intros.
  change (0 <= task_delete_ints initial <= 255) in H.
  rewrite (unsigned_last_nbits_eq (task_delete_ints initial) 32 ltac:(change (0 <= (task_delete_ints initial) < 4294967296); lia)) in PreH1.
  pose proof (task_delete_focus_reassemble
    (task_delete_uchar_cell ( &( "OSIntNesting" ) ) (task_delete_ints initial))
    (task_delete_entry environment critical saved_local completed sg requested call mask initial))
    as Hentry.
  unfold task_delete_uchar_cell in Hentry; sep_apply Hentry.
  prop_apply (task_delete_entry_profile_and_priority__prefix_and_error_returns
    environment critical saved_local completed sg requested call mask initial); Intros.
  assert (Hstatic : task_delete_static_profile sg) by tauto.
  assert (Hrequested : 0 <= requested <= 255) by tauto.
  assert (Herr : task_delete_prefix_error sg false initial.(IntrState).(intNesting)
    requested = Some error_codes.OS_ERR_TASK_DEL_ISR).
  { rewrite task_delete_prefix_error_selected_profile__prefix_and_error_returns by exact Hstatic.
    rewrite (proj2 (Z.ltb_lt 0 initial.(IntrState).(intNesting))
      ltac:(unfold task_delete_ints in PreH1; lia)); reflexivity. }
  sep_apply_l_atomic (task_delete_prefix_error_api_post
    environment critical saved_local completed sg requested (LitMap "?") call mask initial
    error_codes.OS_ERR_TASK_DEL_ISR X Herr PreH7); entailer!.
Qed. 

Lemma proof_of_OSTaskDel_partial_solve_wit_2_pure : OSTaskDel_partial_solve_wit_2_pure.
Proof.
  left; intros.
  prop_apply (store_uchar_range ( &( "OSIntNesting" ) ) (task_delete_ints initial)); Intros.
  change (0 <= task_delete_ints initial <= 255) in H.
  rewrite (unsigned_last_nbits_eq (task_delete_ints initial) 32 ltac:(change (0 <= (task_delete_ints initial) < 4294967296); lia)) in PreH3.
  pose proof (task_delete_focus_reassemble
    (task_delete_uchar_cell ( &( "OSIntNesting" ) ) (task_delete_ints initial))
    (task_delete_entry environment critical saved_local completed sg requested call mask initial))
    as Hentry.
  unfold task_delete_uchar_cell in Hentry; sep_apply Hentry.
  prop_apply (task_delete_entry_profile_and_priority__prefix_and_error_returns
    environment critical saved_local completed sg requested call mask initial); Intros.
  assert (Hstatic : task_delete_static_profile sg) by tauto.
  assert (Hrequested : 0 <= requested <= 255) by tauto.
  assert (Hpriority : 0 <= prio_pre <= 255) by lia.
  rewrite (unsigned_last_nbits_eq prio_pre 32 ltac:(change (0 <= prio_pre < 4294967296); lia)) in PreH1.
  assert (Hprefix : task_delete_prefix_passed sg requested initial).
  { unfold task_delete_prefix_passed.
    rewrite task_delete_prefix_error_selected_profile__prefix_and_error_returns by exact Hstatic.
    assert (Hzero : initial.(IntrState).(intNesting) = 0)
      by (unfold task_delete_ints in H, PreH3; lia).
    rewrite Hzero; cbn.
    rewrite (proj2 (Z.eqb_neq requested 63) ltac:(lia)),
      (proj2 (Z.leb_gt 63 requested) ltac:(lia)); reflexivity. }
  rewrite PreH5; entailer!.
Qed. 

Lemma proof_of_OSTaskDel_partial_solve_wit_3_pure : OSTaskDel_partial_solve_wit_3_pure.
Proof.
  left; intros.
  prop_apply (store_uchar_range ( &( "OSIntNesting" ) ) (task_delete_ints initial)); Intros.
  change (0 <= task_delete_ints initial <= 255) in H.
  rewrite (unsigned_last_nbits_eq (task_delete_ints initial) 32 ltac:(change (0 <= (task_delete_ints initial) < 4294967296); lia)) in PreH4.
  pose proof (task_delete_focus_reassemble
    (task_delete_uchar_cell ( &( "OSIntNesting" ) ) (task_delete_ints initial))
    (task_delete_entry environment critical saved_local completed sg requested call mask initial))
    as Hentry.
  unfold task_delete_uchar_cell in Hentry; sep_apply Hentry.
  prop_apply (task_delete_entry_profile_and_priority__prefix_and_error_returns
    environment critical saved_local completed sg requested call mask initial); Intros.
  assert (Hstatic : task_delete_static_profile sg) by tauto.
  assert (Hrequested : 0 <= requested <= 255) by tauto.
  assert (Hpriority : 0 <= prio_pre <= 255) by lia.
  rewrite (unsigned_last_nbits_eq prio_pre 32 ltac:(change (0 <= prio_pre < 4294967296); lia)) in PreH1.
  assert (Hprefix : task_delete_prefix_passed sg requested initial).
  { unfold task_delete_prefix_passed.
    rewrite task_delete_prefix_error_selected_profile__prefix_and_error_returns by exact Hstatic.
    assert (Hzero : initial.(IntrState).(intNesting) = 0)
      by (unfold task_delete_ints in H, PreH4; lia).
    rewrite Hzero; cbn.
    assert (Hself : requested = 255) by lia.
    rewrite Hself; reflexivity. }
  rewrite PreH6; entailer!.
Qed. 

Lemma proof_of_OSTaskDel_partial_solve_wit_15_pure : OSTaskDel_partial_solve_wit_15_pure.
Proof.
  left; intros; subst priority requested.
  assert (Hself : sg.(osPrioSelf) = 255).
  { destruct PreH6 as [Hprofile _].
    unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto. }
  assert (Hselection : task_delete_selection sg prio_pre acquired.(TskState)
    acquired.(SchedState) prio_pre).
  { apply (proj2 (task_delete_selection_explicit sg prio_pre _ _ prio_pre
      ltac:(rewrite Hself; exact PreH2))); reflexivity. }
  pose proof (task_delete_lookup_selected_in_range sg prio_pre call initial current
    acquired prio_pre PreH3 Hselection) as Hrange.
  unfold task_delete_selected; entailer!.
Qed.

Lemma proof_of_OSTaskDel_partial_solve_wit_16_pure : OSTaskDel_partial_solve_wit_16_pure.
Proof.
  left; intros; subst priority requested.
  assert (Hself : sg.(osPrioSelf) = 255).
  { destruct PreH6 as [Hprofile _].
    unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto. }
  assert (Hselection : task_delete_selection sg prio_pre acquired.(TskState)
    acquired.(SchedState) prio_pre).
  { apply (proj2 (task_delete_selection_explicit sg prio_pre _ _ prio_pre
      ltac:(rewrite Hself; exact PreH2))); reflexivity. }
  pose proof (task_delete_lookup_selected_in_range sg prio_pre call initial current
    acquired prio_pre PreH3 Hselection) as Hrange.
  unfold task_delete_selected; entailer!.
Qed.

Lemma proof_of_OSTaskDel_partial_solve_wit_17_pure : OSTaskDel_partial_solve_wit_17_pure.
Proof.
  left; intros; subst priority.
  pose proof (task_delete_lookup_selected_in_range sg requested call initial current
    acquired caller_node.(curPrio) PreH6 (proj1 PreH2)) as Hrange.
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_partial_solve_wit_39_pure : OSTaskDel_partial_solve_wit_39_pure.
Proof.
  left; intros.
  unfold event_task_remove_group, event_task_remove_cleared.
  apply Z.eqb_neq in PreH1; rewrite PreH1; entailer!.
Qed. 

Lemma proof_of_OSTaskDel_partial_solve_wit_40_pure : OSTaskDel_partial_solve_wit_40_pure.
Proof.
  left; intros.
  unfold event_task_remove_group, event_task_remove_cleared.
  apply Z.eqb_neq in PreH1; rewrite PreH1; entailer!.
Qed. 

Lemma proof_of_OSTaskDel_partial_solve_wit_41_pure : OSTaskDel_partial_solve_wit_41_pure.
Proof.
  left; intros.
  unfold event_task_remove_group, event_task_remove_cleared.
  apply Z.eqb_neq in PreH1; rewrite PreH1; entailer!.
Qed. 

Lemma proof_of_OSTaskDel_partial_solve_wit_42_pure : OSTaskDel_partial_solve_wit_42_pure.
Proof.
  left; intros.
  unfold event_task_remove_group, event_task_remove_cleared.
  rewrite PreH1; entailer!.
Qed. 

Lemma proof_of_OSTaskDel_partial_solve_wit_43_pure : OSTaskDel_partial_solve_wit_43_pure.
Proof.
  left; intros.
  unfold event_task_remove_group, event_task_remove_cleared.
  rewrite PreH1; entailer!.
Qed. 

Lemma proof_of_OSTaskDel_partial_solve_wit_44_pure : OSTaskDel_partial_solve_wit_44_pure.
Proof.
  left; intros.
  unfold event_task_remove_group, event_task_remove_cleared.
  rewrite PreH1; entailer!.
Qed. 

Lemma proof_of_OSTaskDel_partial_solve_wit_74_pure : OSTaskDel_partial_solve_wit_74_pure.
Proof.
  left; intros.
  unfold task_delete_locks, task_delete_prepare_state, task_delete_lock_state.
  cbn [replace_IntrS IntrState lockNesting].
  assert (Htest : (lockNesting (IntrState flagged) <? 255)%Z = false).
  { apply Z.ltb_ge; unfold task_delete_locks in *; lia. }
  entailer!; rewrite Htest; reflexivity.
Qed.

Lemma proof_of_OSTaskDel_partial_solve_wit_75_pure : OSTaskDel_partial_solve_wit_75_pure.
Proof.
  left; intros.
  unfold task_delete_locks, task_delete_prepare_state, task_delete_lock_state.
  cbn [replace_IntrS IntrState lockNesting].
  assert (Htest : (lockNesting (IntrState flagged) <? 255)%Z = true).
  { apply Z.ltb_lt; unfold task_delete_locks in *; lia. }
  entailer!; rewrite Htest; reflexivity.
Qed.

Lemma proof_of_OSTaskDel_partial_solve_wit_84_pure : OSTaskDel_partial_solve_wit_84_pure.
Proof.
  left; intros.
  unfold task_delete_locks in *.
  unfold task_delete_released, task_delete_release_state.
  cbn [replace_IntrS IntrState lockNesting].
  rewrite (proj2 (Z.ltb_ge _ _) PreH1), Bool.andb_false_r.
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_partial_solve_wit_85_pure : OSTaskDel_partial_solve_wit_85_pure.
Proof.
  left; intros.
  unfold task_delete_added_value in PreH9, PreH1.
  destruct (task_delete_lock_added (IntrState prepared)) eqn:Hadded;
    destruct (task_delete_lock_added (IntrState flagged));
    cbn in PreH9, PreH1; try discriminate; try contradiction.
  unfold task_delete_locks, task_delete_released, task_delete_release_state.
  rewrite Hadded; cbn; entailer!.
Qed.

Lemma proof_of_OSTaskDel_partial_solve_wit_86_pure : OSTaskDel_partial_solve_wit_86_pure.
Proof.
  left; intros.
  unfold task_delete_added_value in PreH10, PreH2.
  destruct (task_delete_lock_added (IntrState prepared)) eqn:Hadded;
    destruct (task_delete_lock_added (IntrState flagged));
    cbn in PreH10, PreH2; try discriminate.
  unfold task_delete_locks in *.
  unfold task_delete_released, task_delete_release_state.
  rewrite Hadded; cbn [replace_IntrS IntrState lockNesting andb].
  rewrite (proj2 (Z.ltb_lt 0 resumed.(IntrState).(lockNesting)) ltac:(lia)); entailer!.
Qed.

Lemma proof_of_OSTaskDel_partial_solve_wit_105_pure : OSTaskDel_partial_solve_wit_105_pure.
Proof.
  left; intros.
  assert (Hcount : 0 < task_delete_count (task_delete_released prepared resumed)).
  { pose proof PreH6 as [_ [_ [Hrely _]]].
    destruct Hrely as [_ [_ [Hvalid _]]].
    destruct Hvalid as [_ [Htasks [[Hprepared _] _]]].
    destruct Hprepared as [_ [resumed_node [Hnode _]]].
    change (0 < taskCount (TskState resumed)).
    eapply task_active_count_positive__byte_and_cut_observations;
      [exact (proj1 (proj2 Htasks))|exact Hnode]. }
  assert (Hbyte : unsigned_last_nbits
    (task_delete_count (task_delete_released prepared resumed) - 1) 8 =
    Z.rem (task_delete_count (task_delete_released prepared resumed) - 1) 256).
  { unfold unsigned_last_nbits.
    rewrite Z.rem_mod_nonneg by lia; reflexivity. }
  assert (Hhead :
    task_delete_list_head sg (task_delete_released prepared resumed) =
    task_delete_list_head sg
      (task_delete_cut sg prepared resumed tid priority node (LitMap "?"))).
  { change (encode_task_link sg (tcbListHead (TskState resumed)) =
      encode_task_link sg
        (match prevTCB node with
         | None => nextTCB node | Some _ => tcbListHead (TskState resumed)
         end)).
    change (encode_task_link sg (prevTCB node) <> 0) in PreH1.
    destruct (prevTCB node); [reflexivity|contradiction]. }
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_partial_solve_wit_106_pure : OSTaskDel_partial_solve_wit_106_pure.
Proof.
  left; intros.
  assert (Hcount : 0 < task_delete_count (task_delete_released prepared resumed)).
  { pose proof PreH5 as [_ [_ [Hrely _]]].
    destruct Hrely as [_ [_ [Hvalid _]]].
    destruct Hvalid as [_ [Htasks [[Hprepared _] _]]].
    destruct Hprepared as [_ [resumed_node [Hnode _]]].
    change (0 < taskCount (TskState resumed)).
    eapply task_active_count_positive__byte_and_cut_observations;
      [exact (proj1 (proj2 Htasks))|exact Hnode]. }
  assert (Hbyte : unsigned_last_nbits
    (task_delete_count (task_delete_released prepared resumed) - 1) 8 =
    Z.rem (task_delete_count (task_delete_released prepared resumed) - 1) 256).
  { unfold unsigned_last_nbits.
    rewrite Z.rem_mod_nonneg by lia; reflexivity. }
  assert (Hhead :
    task_delete_list_head sg (task_delete_released prepared resumed) =
    task_delete_list_head sg
      (task_delete_cut sg prepared resumed tid priority node (LitMap "?"))).
  { change (encode_task_link sg (tcbListHead (TskState resumed)) =
      encode_task_link sg
        (match prevTCB node with
         | None => nextTCB node | Some _ => tcbListHead (TskState resumed)
         end)).
    change (encode_task_link sg (prevTCB node) <> 0) in PreH1.
    destruct (prevTCB node); [reflexivity|contradiction]. }
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_partial_solve_wit_107_pure : OSTaskDel_partial_solve_wit_107_pure.
Proof.
  left; intros.
  assert (Hcount : 0 < task_delete_count (task_delete_released prepared resumed)).
  { pose proof PreH6 as [_ [_ [Hrely _]]].
    destruct Hrely as [_ [_ [Hvalid _]]].
    destruct Hvalid as [_ [Htasks [[Hprepared _] _]]].
    destruct Hprepared as [_ [resumed_node [Hnode _]]].
    change (0 < taskCount (TskState resumed)).
    eapply task_active_count_positive__byte_and_cut_observations;
      [exact (proj1 (proj2 Htasks))|exact Hnode]. }
  assert (Hbyte : unsigned_last_nbits
    (task_delete_count (task_delete_released prepared resumed) - 1) 8 =
    Z.rem (task_delete_count (task_delete_released prepared resumed) - 1) 256).
  { unfold unsigned_last_nbits.
    rewrite Z.rem_mod_nonneg by lia; reflexivity. }
  assert (Hhead :
    task_delete_list_head sg (task_delete_released prepared resumed) =
    task_delete_list_head sg
      (task_delete_cut sg prepared resumed tid priority node (LitMap "?"))).
  { change (encode_task_link sg (tcbListHead (TskState resumed)) =
      encode_task_link sg
        (match prevTCB node with
         | None => nextTCB node | Some _ => tcbListHead (TskState resumed)
         end)).
    change (encode_task_link sg (prevTCB node) <> 0) in PreH1.
    destruct (prevTCB node); [reflexivity|contradiction]. }
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_partial_solve_wit_108_pure : OSTaskDel_partial_solve_wit_108_pure.
Proof.
  left; intros.
  assert (Hcount : 0 < task_delete_count (task_delete_released prepared resumed)).
  { pose proof PreH6 as [_ [_ [Hrely _]]].
    destruct Hrely as [_ [_ [Hvalid _]]].
    destruct Hvalid as [_ [Htasks [[Hprepared _] _]]].
    destruct Hprepared as [_ [resumed_node [Hnode _]]].
    change (0 < taskCount (TskState resumed)).
    eapply task_active_count_positive__byte_and_cut_observations;
      [exact (proj1 (proj2 Htasks))|exact Hnode]. }
  assert (Hbyte : unsigned_last_nbits
    (task_delete_count (task_delete_released prepared resumed) - 1) 8 =
    Z.rem (task_delete_count (task_delete_released prepared resumed) - 1) 256).
  { unfold unsigned_last_nbits.
    rewrite Z.rem_mod_nonneg by lia; reflexivity. }
  assert (Hnone : prevTCB node = None).
  { pose proof PreH10 as [[Hlookup [_ [Htable _]]] _].
    destruct Hlookup as [_ [_ [_ [_ [Hrely _]]]]].
    destruct Hrely as [_ [_ [[Hvalid _] _]]].
    destruct Hvalid as [Hprofile [Htasks _]].
    pose proof (proj2 (task_delete_table_lookup_live _ _ _ _ Htable)) as Hnode.
    eapply task_active_prev_encode_zero__byte_and_cut_observations;
      [exact Hprofile|exact Htasks|exact Hnode|].
    exact PreH1. }
  assert (Hhead :
    task_delete_next sg (task_delete_prepared_node node) =
    task_delete_list_head sg
      (task_delete_cut sg prepared resumed tid priority node (LitMap "?"))).
  { change (encode_task_link sg (nextTCB node) =
      encode_task_link sg
        (match prevTCB node with
         | None => nextTCB node | Some _ => tcbListHead (TskState resumed)
         end)).
    rewrite Hnone; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_partial_solve_wit_109_pure : OSTaskDel_partial_solve_wit_109_pure.
Proof.
  left; intros.
  assert (Hcount : 0 < task_delete_count (task_delete_released prepared resumed)).
  { pose proof PreH5 as [_ [_ [Hrely _]]].
    destruct Hrely as [_ [_ [Hvalid _]]].
    destruct Hvalid as [_ [Htasks [[Hprepared _] _]]].
    destruct Hprepared as [_ [resumed_node [Hnode _]]].
    change (0 < taskCount (TskState resumed)).
    eapply task_active_count_positive__byte_and_cut_observations;
      [exact (proj1 (proj2 Htasks))|exact Hnode]. }
  assert (Hbyte : unsigned_last_nbits
    (task_delete_count (task_delete_released prepared resumed) - 1) 8 =
    Z.rem (task_delete_count (task_delete_released prepared resumed) - 1) 256).
  { unfold unsigned_last_nbits.
    rewrite Z.rem_mod_nonneg by lia; reflexivity. }
  assert (Hnone : prevTCB node = None).
  { pose proof PreH9 as [[Hlookup [_ [Htable _]]] _].
    destruct Hlookup as [_ [_ [_ [_ [Hrely _]]]]].
    destruct Hrely as [_ [_ [[Hvalid _] _]]].
    destruct Hvalid as [Hprofile [Htasks _]].
    pose proof (proj2 (task_delete_table_lookup_live _ _ _ _ Htable)) as Hnode.
    eapply task_active_prev_encode_zero__byte_and_cut_observations;
      [exact Hprofile|exact Htasks|exact Hnode|].
    exact PreH1. }
  assert (Hhead :
    task_delete_next sg (task_delete_prepared_node node) =
    task_delete_list_head sg
      (task_delete_cut sg prepared resumed tid priority node (LitMap "?"))).
  { change (encode_task_link sg (nextTCB node) =
      encode_task_link sg
        (match prevTCB node with
         | None => nextTCB node | Some _ => tcbListHead (TskState resumed)
         end)).
    rewrite Hnone; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_partial_solve_wit_110_pure : OSTaskDel_partial_solve_wit_110_pure.
Proof.
  left; intros.
  assert (Hcount : 0 < task_delete_count (task_delete_released prepared resumed)).
  { pose proof PreH6 as [_ [_ [Hrely _]]].
    destruct Hrely as [_ [_ [Hvalid _]]].
    destruct Hvalid as [_ [Htasks [[Hprepared _] _]]].
    destruct Hprepared as [_ [resumed_node [Hnode _]]].
    change (0 < taskCount (TskState resumed)).
    eapply task_active_count_positive__byte_and_cut_observations;
      [exact (proj1 (proj2 Htasks))|exact Hnode]. }
  assert (Hbyte : unsigned_last_nbits
    (task_delete_count (task_delete_released prepared resumed) - 1) 8 =
    Z.rem (task_delete_count (task_delete_released prepared resumed) - 1) 256).
  { unfold unsigned_last_nbits.
    rewrite Z.rem_mod_nonneg by lia; reflexivity. }
  assert (Hnone : prevTCB node = None).
  { pose proof PreH10 as [[Hlookup [_ [Htable _]]] _].
    destruct Hlookup as [_ [_ [_ [_ [Hrely _]]]]].
    destruct Hrely as [_ [_ [[Hvalid _] _]]].
    destruct Hvalid as [Hprofile [Htasks _]].
    pose proof (proj2 (task_delete_table_lookup_live _ _ _ _ Htable)) as Hnode.
    eapply task_active_prev_encode_zero__byte_and_cut_observations;
      [exact Hprofile|exact Htasks|exact Hnode|].
    exact PreH1. }
  assert (Hhead :
    task_delete_next sg (task_delete_prepared_node node) =
    task_delete_list_head sg
      (task_delete_cut sg prepared resumed tid priority node (LitMap "?"))).
  { change (encode_task_link sg (nextTCB node) =
      encode_task_link sg
        (match prevTCB node with
         | None => nextTCB node | Some _ => tcbListHead (TskState resumed)
         end)).
    rewrite Hnone; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_partial_solve_wit_135_pure : OSTaskDel_partial_solve_wit_135_pure.
Proof.
  left; intros.
  unfold task_delete_running in PreH1 |- *.
  destruct (isRunning (SchedState final_state)); [entailer!|].
  vm_compute in PreH1; discriminate.
Qed.

Lemma proof_of_OSTaskDel_partial_solve_wit_136_pure : OSTaskDel_partial_solve_wit_136_pure.
Proof.
  left; intros.
  unfold task_delete_running in PreH1 |- *.
  destruct (isRunning (SchedState final_state)); [entailer!|].
  vm_compute in PreH1; discriminate.
Qed.

Lemma proof_of_OSTaskDel_partial_solve_wit_137_pure : OSTaskDel_partial_solve_wit_137_pure.
Proof.
  left; intros.
  unfold task_delete_running in PreH1 |- *.
  destruct (isRunning (SchedState final_state)); [entailer!|].
  vm_compute in PreH1; discriminate.
Qed.

Lemma proof_of_OSTaskDel_partial_solve_wit_138_pure : OSTaskDel_partial_solve_wit_138_pure.
Proof.
  left; intros.
  unfold task_delete_running in PreH1 |- *.
  destruct (isRunning (SchedState final_state)); [entailer!|].
  vm_compute in PreH1; discriminate.
Qed.

Lemma proof_of_OSTaskDel_partial_solve_wit_139_pure : OSTaskDel_partial_solve_wit_139_pure.
Proof.
  left; intros.
  unfold task_delete_running in PreH1 |- *.
  destruct (isRunning (SchedState final_state)); [entailer!|].
  vm_compute in PreH1; discriminate.
Qed.

Lemma proof_of_OSTaskDel_partial_solve_wit_140_pure : OSTaskDel_partial_solve_wit_140_pure.
Proof.
  left; intros.
  unfold task_delete_running in PreH1 |- *.
  destruct (isRunning (SchedState final_state)); [entailer!|].
  vm_compute in PreH1; discriminate.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_1 : OSTaskDel_which_implies_wit_1.
Proof.
  left; intros.
  pose proof (task_delete_entry_split_int_nesting__prefix_and_error_returns
    environment critical saved_local completed sg requested call mask initial) as Hsplit.
  rewrite (proj1 PreH1) in Hsplit.
  exact Hsplit.
Qed. 

Lemma proof_of_OSTaskDel_which_implies_wit_2 : OSTaskDel_which_implies_wit_2.
Proof.
  left; intros; unfold task_delete_uchar_cell.
  sep_apply (task_delete_focus_reassemble
    ((&("OSIntNesting")) # UChar |-> task_delete_ints initial)
    (task_delete_entry environment critical saved_local completed sg requested call mask initial)).
  unfold task_delete_entry; Intros.
  destruct H as [Hstatic [Henv [[Hlo Hhi] [Hlayout Hsuccess]]]].
  destruct (Hsuccess PreH1) as [Hdomain Hprotocol].
  unfold task_delete_call_closed,
    kernel_continuation_world_spec.kernel_continuation_call_closed,
    kernel_continuation_world_spec.kernel_continuation_inv,
    task_delete_phase_resources, task_delete_phase_valid.
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_4 : OSTaskDel_which_implies_wit_4.
Proof.
  left; intros; unfold task_delete_save_post; Intros returned acquired.
  destruct H as [Hsource [[Hsame Hstack] [Hrely [Hrun Hprotocol]]]].
  assert (Hhistory : task_delete_lookup_history sg requested call initial returned acquired).
  { unfold task_delete_lookup_history.
    split; [exact PreH1|]. split; [lia|]. split; [exact Hsame|].
    split; [exact PreH4|]. split; [exact Hrely|]. exact (Hprotocol PreH5). }
  assert (Hsaved : interrupt_saved_value mask saved).
  { unfold task_resume_spec.kernel_call_save_source in Hsource; tauto. }
  Exists returned acquired.
  unfold task_delete_acquired, task_delete_masked_raw, task_delete_call_masked,
    kernel_continuation_world_spec.kernel_continuation_call_masked,
    kernel_continuation_world_spec.kernel_continuation_inv,
    task_delete_phase_resources, task_delete_phase_valid,
    task_tcb_init_continuation_capsules.
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_5 : OSTaskDel_which_implies_wit_5.
Proof.
  left; intros; unfold task_delete_acquired at 1; Intros.
  pose proof H as [Hstatic [_ [_ [_ [Hrely Hprotocol]]]]].
  assert (Hself : sg.(osPrioSelf) = 255).
  { destruct Hstatic as [Hprofile _].
    unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto. }
  destruct Hrely as [_ [_ [[Hvalid Hdomain] _]]].
  destruct (proj1 Hdomain ltac:(congruence)) as [cid [node [Hcur Hnode]]].
  Exists cid node.
  assert (Hbinding : task_delete_self_binding sg acquired cid node) by (split; assumption).
  assert (Hcurrent : task_delete_current sg acquired = task_slot_addr sg cid).
  { unfold task_delete_current; rewrite Hcur; reflexivity. }
  destruct PreH2 as [_ [_ [Hcurrent_address _]]].
  unfold task_delete_masked_raw at 1; Intros.
  unfold UCOS2_raw_rep, task_stack.task_shared_rep, sched.sched_raw_rep,
    sched.sched_physical_rep.
  pose proof (task_public_storage_split_field sg acquired.(TskState) cid node
    (TCBCommonField TCBPrio) Hnode (tcb_configured_common_field_in _ _ TCBPrio)) as Hsplit.
  pose proof (task_public_storage_merge_field sg acquired.(TskState) cid node
    (TCBCommonField TCBPrio) Hnode (tcb_configured_common_field_in _ _ TCBPrio)) as Hmerge.
  cbn [task_layout_image tcb_layout_image task_tcb64_image tcb_layout_cell tcb_cell
    tcb_field_address] in Hsplit, Hmerge.
  sep_apply_l_atomic Hsplit.
  fold (task_delete_current sg acquired).
  rewrite Hcurrent_address; rewrite Hcurrent.
  entailer!.
  apply_sepcon_adjoint.
  unfold task_delete_self_cells; rewrite Hcurrent_address, Hcurrent.
  cbn [tcb_field_address].
  sep_apply_l_atomic Hmerge.
  unfold task_delete_acquired, task_delete_masked_raw, UCOS2_raw_rep,
    task_stack.task_shared_rep, sched.sched_raw_rep, sched.sched_physical_rep.
  rewrite Hcurrent_address.
  unfold task_delete_current in Hcurrent; rewrite <- Hcurrent.
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_6 : OSTaskDel_which_implies_wit_6.
Proof.
  left; intros.
  destruct PreH3 as [_ [_ [Hcurrent_address _]]].
  unfold task_delete_self_cells; rewrite Hcurrent_address.
  cbn [tcb_field_address].
  pose proof (task_delete_focus_reassemble
    ((&("OSTCBCur")) # Ptr |-> task_delete_current sg acquired **
      tcb_field_address (task_delete_current sg acquired) TCBPrio # UChar |-> caller_node.(curPrio))
    (task_delete_acquired environment critical saved_local sg requested call initial current saved acquired)) as Hjoin.
  cbn [tcb_field_address] in Hjoin.
  sep_apply Hjoin.
  unfold task_delete_acquired; Intros.
  pose proof H as [Hstatic _].
  assert (Hself : requested = sg.(osPrioSelf)).
  { destruct Hstatic as [Hprofile _].
    assert (Hvalue : sg.(osPrioSelf) = 255).
    { unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto. }
    congruence. }
  assert (Hselection : task_delete_selected sg requested acquired caller_node.(curPrio)
    (task_delete_table sg acquired caller_node.(curPrio))).
  { split; [|reflexivity]. rewrite Hself.
    destruct PreH2 as [Hcur Hnode].
    eapply task_delete_selection_self; eauto. }
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_8 : OSTaskDel_which_implies_wit_8.
Proof.
  left; intros; unfold task_delete_acquired at 1; Intros.
  unfold task_delete_masked_raw at 1; Intros.
  rewrite UCOS2_raw_rep_priority_table_equiv.
  pose proof (array_abstraction.store_prio_tbl_split_cell sg acquired.(TskState).(prioTbl)
    priority ltac:(lia)) as Hsplit.
  pose proof (array_abstraction.store_prio_tbl_merge_cell sg acquired.(TskState).(prioTbl)
    priority ltac:(lia)) as Hmerge.
  destruct PreH4 as [_ [_ [_ [_ [_ [_ [Htable_address _]]]]]]].
  rewrite Htable_address in Hsplit, Hmerge.
  sep_apply_l_atomic Hsplit.
  unfold task_delete_table.
  entailer!.
  apply_sepcon_adjoint; unfold task_delete_ptr_cell.
  sep_apply_l_atomic Hmerge.
  unfold task_delete_acquired, task_delete_masked_raw.
  rewrite UCOS2_raw_rep_priority_table_equiv.
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_9 : OSTaskDel_which_implies_wit_9.
Proof.
  left; intros; unfold task_delete_ptr_cell; apply task_delete_focus_reassemble.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_10 : OSTaskDel_which_implies_wit_10.
Proof.
  left; intros; unfold task_delete_acquired; Intros.
  destruct H as [_ [_ [_ [_ [Hrely _]]]]].
  destruct Hrely as [_ [_ [[Hvalid _] _]]].
  unfold task_delete_call_masked,
    kernel_continuation_world_spec.kernel_continuation_call_masked,
    kernel_continuation_world_spec.kernel_continuation_inv,
    task_delete_phase_resources, task_delete_phase_valid,
    task_delete_masked_raw, task_tcb_init_continuation_capsules.
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_11 : OSTaskDel_which_implies_wit_11.
Proof.
  left; intros; unfold task_delete_acquired; Intros.
  destruct H as [_ [_ [_ [_ [Hrely _]]]]].
  destruct Hrely as [_ [_ [[Hvalid _] _]]].
  unfold task_delete_call_masked,
    kernel_continuation_world_spec.kernel_continuation_call_masked,
    kernel_continuation_world_spec.kernel_continuation_inv,
    task_delete_phase_resources, task_delete_phase_valid,
    task_delete_masked_raw, task_tcb_init_continuation_capsules.
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_12 : OSTaskDel_which_implies_wit_12.
Proof.
  left; intros; unfold task_delete_acquired; Intros.
  pose proof H as [Hstatic [_ [_ [_ [Hrely _]]]]].
  pose proof (task_delete_lookup_selected_in_range sg requested call initial current
    acquired priority H (proj1 PreH1)) as Hrange.
  assert (Hlowest : sg.(osLowestPrio) = 63).
  { destruct Hstatic as [Hprofile _].
    unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto. }
  destruct Hrely as [_ [_ [[Hvalid _] _]]].
  destruct Hvalid as [_ [_ [_ [_ [Hcross _]]]]].
  destruct Hcross as [Htable _].
  destruct Htable as [_ [Hslots _]].
  specialize (Hslots priority ltac:(unfold task_priority_in_range; lia)).
  unfold task_delete_table in PreH2, PreH3.
  destruct (acquired.(TskState).(prioTbl) priority) as [| |tid] eqn:Hentry.
  - simpl in PreH2; contradiction.
  - simpl in PreH3; contradiction.
  - destruct Hslots as [node Hnode].
    assert (Hpointer : task_delete_table sg acquired priority = task_slot_addr sg tid).
    { unfold task_delete_table; rewrite Hentry; reflexivity. }
    assert (Hlive : task_delete_live sg acquired priority (task_slot_addr sg tid) tid node).
    { split; [|reflexivity]. unfold task_delete_table_lookup; rewrite Hentry.
      exists node; split; [exact Hnode|reflexivity]. }
    Exists node tid.
    unfold task_delete_live_body, task_delete_live_history.
    assert (Hselected : task_delete_selected sg requested acquired priority (task_slot_addr sg tid)).
    { rewrite <- Hpointer; exact PreH1. }
    rewrite Hpointer; entailer!.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_13 : OSTaskDel_which_implies_wit_13.
Proof.
  left; intros.
  unfold task_delete_live_body.
  Intros.
  match goal with
  | H : task_delete_live_history _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof H as Hhistory
  end.
  destruct Hhistory as [Hlookup [Hselected [Hlive Hpointer]]].
  destruct (task_delete_table_lookup_live _ _ _ _ Hlive) as [_ Hnode].
  pose proof Hlookup as [Hstatic [_ [_ [_ [Hrely _]]]]].
  destruct Hrely as [_ [_ [[Hvalid _] _]]].
  assert (Hsg : valid_stable_glob_vars sg).
  { unfold task_delete_static_profile, selected_kernel_profile in Hstatic; tauto. }
  assert (Hconfig : sg.(osKernelConfig) = selected_kernel_configuration).
  { unfold task_delete_static_profile in Hstatic; tauto. }
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (rewrite Hconfig; reflexivity).
  assert (Hprofile : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (rewrite Hconfig; reflexivity).
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid.
  destruct Hvalid as [_ [Htasks [[Hready _] _]]].
  assert (Hunique : task_priority_unique acquired.(TskState)).
  { unfold task_in_range in Htasks; tauto. }
  assert (Hprio : task_priority_in_range sg node.(curPrio)).
  { unfold task_in_range in Htasks.
    destruct Htasks as [_ [_ [_ [_ [_ [_ [_ [Hpriorities _]]]]]]]].
    exact (Hpriorities tid node Hnode). }
  assert (Hrow : 0 <= tcb_y_of_prio node.(curPrio) < 8).
  { unfold tcb_y_of_prio, task_priority_in_range in *.
    assert (Hlowest : sg.(osLowestPrio) < 64).
    { unfold valid_stable_glob_vars in Hsg; lia. }
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  unfold task_delete_masked_raw, UCOS2_raw_rep, task_stack.task_shared_rep.
  Intros.
  sep_apply_l_atomic (task_public_storage_split_task sg acquired.(TskState) tid node Hnode).
  sep_apply_l_atomic (used_task_rep_ready_fields_focus__ready_bitmap sg tid node Hmulti Hprofile).
  sep_apply_l_atomic (sched_raw_rep_remove_ready_focus__ready_bitmap sg acquired.(TskState)
    acquired.(SchedState) tid node Hsg Hunique Hnode Hprio
    (sched.sched_ready_in_range_implies_structure sg _ _ Hready) Hrow).
  unfold task_delete_global_addresses in PreH1.
  destruct PreH1 as [_ [_ [_ [_ [_ [_ [_ [Hgroup [Hrows _]]]]]]]]].
  cbn [task_delete_tcb_value task_tcb64_image task_delete_ready_row task_delete_ready_group].
  rewrite Hgroup, Hrows.
  replace (tcb_y_of_prio node.(curPrio) * sizeof(UCHAR))
    with (tcb_y_of_prio node.(curPrio)) by (cbn; lia).
  cbn [tcb_field_address].
  unfold task_delete_ready_row, task_delete_ready_group.
  entailer!.
  apply_sepcon_adjoint.
  unfold task_delete_ready_cells.
  rewrite Hgroup, Hrows.
  cbn [tcb_field_address].
  unfold task_delete_ready_body, task_delete_masked_raw, UCOS2_raw_rep, task_stack.task_shared_rep.
  unfold task_delete_ready_state, replace_SchedS.
  cbn [TskState SchedState IntrState EventState TickState FlagState MemoryState
    TimerState StatsState ControlState NameState].
  entailer!.
  sep_apply_r_atomic (task_public_storage_merge_task sg acquired.(TskState) tid node Hnode).
  entailer!.
  match goal with
  | |- context [?fields -* used_task_rep sg tid node] =>
      sep_apply_r_atomic (task_delete_focus_reassemble fields (used_task_rep sg tid node))
  end.
  entailer!.
  match goal with
  | |- context [?cells -* sched.sched_raw_rep sg acquired.(TskState)
      (sched.sched_remove_ready_task acquired.(SchedState) tid)] =>
      sep_apply_r_atomic (task_delete_focus_reassemble cells
        (sched.sched_raw_rep sg acquired.(TskState)
          (sched.sched_remove_ready_task acquired.(SchedState) tid)))
  end.
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_14 : OSTaskDel_which_implies_wit_14.
Proof.
  left; intros.
  unfold task_delete_global_addresses in PreH1.
  destruct PreH1 as [_ [_ [_ [_ [_ [_ [_ [Hgroup [Hrows _]]]]]]]]].
  pose proof (task_delete_focus_reassemble
    (task_delete_ready_cells sg acquired tid node true)
    (task_delete_ready_body environment critical saved_local sg requested call initial
      current saved acquired priority (task_slot_addr sg tid) tid node)) as Hmerge.
  unfold task_delete_ready_cells in Hmerge.
  rewrite Hgroup, Hrows in Hmerge.
  unfold task_delete_ready_cells.
  rewrite Hgroup, Hrows.
  cbn [task_delete_tcb_value task_tcb64_image task_delete_ready_row
    task_delete_ready_group tcb_field_address] in *.
  replace (tcb_y_of_prio (curPrio node) * sizeof(UCHAR))
    with (tcb_y_of_prio (curPrio node)) by (cbn; lia).
  sep_apply_r_atomic Hmerge; entailer!.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_15 : OSTaskDel_which_implies_wit_15.
Proof.
  left; intros.
  unfold task_delete_ready_body, task_delete_masked_raw.
  Intros.
  match goal with
  | H : task_delete_live_history _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof H as Hhistory
  end.
  destruct Hhistory as [Hlookup [Hselected [Hlive Hpointer]]].
  destruct (task_delete_table_lookup_live _ _ _ _ Hlive) as [_ Hnode].
  unfold UCOS2_raw_rep, task_stack.task_shared_rep.
  cbn [task_delete_ready_state replace_SchedS].
  match goal with |- _ |-- ?post => set (focused_post := post) end.
  sep_apply_l_atomic (task_public_storage_field_focus__ready_bitmap sg acquired.(TskState)
    tid node (TCBCommonField TCBEventPtr) Hnode
    (tcb_configured_common_field_in _ _ TCBEventPtr)).
  unfold focused_post.
  cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell].
  unfold task_delete_event_handle, task_delete_ptr_cell.
  cbn [tcb_field_address].
  entailer!; apply_sepcon_adjoint.
  entailer!.
  sep_apply_r_atomic (task_delete_focus_reassemble
    (tcb_field_address (task_slot_addr sg tid) TCBEventPtr # Ptr |->
      task.encode_event_link sg node.(eventPtr))
    (task_public_storage sg acquired.(TskState))).
  cbn [tcb_field_address].
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_16 : OSTaskDel_which_implies_wit_16.
Proof.
  left; intros.
  unfold task_delete_ptr_cell; cbn [tcb_field_address].
  sep_apply_l_atomic (task_delete_focus_reassemble
    (tcb_field_address (task_slot_addr sg tid) TCBEventPtr # Ptr |->
      task_delete_event_handle sg node)
    (task_delete_ready_body environment critical saved_local sg requested call initial
      current saved acquired priority (task_slot_addr sg tid) tid node)).
  unfold task_delete_ready_body; Intros.
  assert (Hhistory : task_delete_live_history sg requested call initial current acquired
    priority (task_slot_addr sg tid) tid node) by assumption.
  destruct (task_delete_live_history_inv_and_lookup__event_and_flag_unlink
    _ _ _ _ _ _ _ _ _ _ Hhistory) as [Hvalid Hnode].
  assert (Hstatic : task_delete_static_profile sg).
  { unfold task_delete_live_history, task_delete_lookup_history in Hhistory; tauto. }
  assert (Hconfig : sg.(osKernelConfig) = selected_kernel_configuration) by (unfold task_delete_static_profile in Hstatic; tauto).
  assert (Hsg : valid_stable_glob_vars sg).
  { unfold task_delete_static_profile, selected_kernel_profile in Hstatic; tauto. }
  destruct node.(eventPtr) as [eid|] eqn:Hptr.
  2: { unfold task_delete_event_handle, encode_event_link in PreH1; rewrite Hptr in PreH1; contradiction. }
  destruct Hvalid as [Hprofile [Htasks [Hsched [Hevents [Hcross Hrest]]]]].
  destruct (cross_module_invariants.task_event_reference_has_waiter sg acquired tid node eid
    Hcross Hnode Hptr) as [ev [He Hin]].
  assert (Heid : valid_event_id sg eid).
  { exact (proj1 (event_pool.event_pool_used_not_free sg acquired.(EventState) eid ev
      (proj1 Hevents) He)). }
  pose proof (task_delete_static_profile_event_layout sg eid Hstatic Heid) as Hlayout.
  assert (Hcanonical : event_wait.event_waitList_canonical sg acquired.(TskState) ev.(EventStateDef.waitList)).
  { destruct Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
    exact (proj1 (Hentries eid ev He)). }
  assert (Hprio : valid_task_prio sg node.(curPrio)).
  { destruct (proj2 (proj2 Hcanonical) tid Hin) as [found [Hfound Hprio]].
    assert (found = node) by congruence; subst found; exact Hprio. }
  assert (Hunique : task_priority_unique acquired.(TskState)).
  { unfold task_in_range in Htasks; tauto. }
  assert (Hrow : 0 <= node.(curPrio) / 8 < 8).
  { assert (Hlowest : sg.(osLowestPrio) = 63) by (unfold valid_stable_glob_vars in Hsg; tauto).
    unfold valid_task_prio in Hprio.
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  assert (Hhandle : task_delete_event_handle sg node = event.event_addr sg eid).
  { unfold task_delete_event_handle, encode_event_link, event.event_addr; rewrite Hptr; reflexivity. }
  rewrite Hhandle.
  set (ready := task_delete_ready_state acquired tid).
  fold ready.
  unfold task_delete_masked_raw at 1; Intros.
  assert (Hcoverage : task_stack_coverage_spec.task_stack_live_coverage ready.(TskState)
    (kernel_stack_world_spec.task_stack_call_active_key current)) by assumption.
  unfold UCOS2_raw_rep, task_stack.task_shared_rep.
  sep_apply_l_atomic (task_public_storage_split_task sg ready.(TskState) tid node Hnode).
  sep_apply_l_atomic (event.event_raw_rep_split_eid sg ready.(TskState) ready.(EventState) eid ev He).
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false) by (rewrite Hconfig; reflexivity).
  assert (Htaskprofile : sg.(osKernelConfig).(cfgTaskProfile) = false) by (rewrite Hconfig; reflexivity).
  pose proof (used_task_rep_tcb64 sg tid node Hmulti Htaskprofile) as Hused.
  rewrite <- (task_slot_addr_tcb64 sg tid Hmulti Htaskprofile) in Hused.
  sep_apply_l_atomic (proj1 Hused).
  unfold event.used_event_rep.
  sep_apply_l_atomic (tcb64_storage_split_wait_fields__event_and_flag_unlink
    (task_slot_addr sg tid) (task_tcb64_image sg node) (node.(curPrio) / 8)
    (Z.shiftl 1 (node.(curPrio) mod 8)) (Z.shiftl 1 (node.(curPrio) / 8))
    (event.event_addr sg eid) eq_refl eq_refl eq_refl
    ltac:(change (Some (task_delete_event_handle sg node) = Some (event.event_addr sg eid)); rewrite Hhandle; reflexivity)).
  sep_apply_l_atomic (event_task_remove_ecb_split sg.(osKernelConfig).(cfgEventNames)
    (event.event_addr sg eid) (event.event_image sg ready.(TskState) ev) (node.(curPrio) / 8)
    (event.encode_event_wait_tbl_at_or ev.(EventStateDef.waitList) ready.(TskState) (node.(curPrio) / 8))
    (event.encode_event_wait_grp ev.(EventStateDef.waitList) ready.(TskState)) Hrow
    (event.event_table_image_eq sg ready.(TskState) ev _ Hrow) eq_refl).
  Exists (node.(curPrio) / 8) (Z.shiftl 1 (node.(curPrio) mod 8))
    (Z.shiftl 1 (node.(curPrio) / 8))
    (event.encode_event_wait_tbl_at_or ev.(EventStateDef.waitList) ready.(TskState) (node.(curPrio) / 8))
    (event.encode_event_wait_grp ev.(EventStateDef.waitList) ready.(TskState)).
  unfold task_delete_event_remove_fields.
  destruct Hlayout as [Htype [Hgroup Htable]].
  unfold event.OSEventGrp_off, event.OSEventTbl_off in Hgroup, Htable.
  rewrite Hgroup, Htable.
  cbn [tcb_field_address].
  entailer!.
  apply_sepcon_adjoint.
  pose proof (task_delete_static_profile_event_layout sg eid Hstatic Heid) as Hlayout.
  pose proof (event_task_remove_abstract_storage_consequence sg ready.(TskState) eid ev tid node
    (task_slot_addr sg tid) Hlayout Hsg Hunique Hcanonical Hprio Hnode) as Hmerge.
  rewrite Hgroup, Htable in Hmerge; cbn [tcb_field_address] in Hmerge.
  sep_apply_l_atomic Hmerge.
  pose proof (used_task_rep_tcb64 sg tid (task_set_event_ptr node None) Hmulti Htaskprofile) as Hupdated.
  rewrite <- (task_slot_addr_tcb64 sg tid Hmulti Htaskprofile) in Hupdated.
  sep_apply_l_atomic (proj2 Hupdated).
  sep_apply_l_atomic (task_public_storage_merge_updated_task sg ready.(TskState) tid
    (task_set_event_ptr node None)).
  pose proof (event.event_raw_rep_merge_updated_eid sg ready.(TskState) ready.(EventState) eid
    (event_wait.event_set_wait_list ev (helpers.remove_Z_eqb tid ev.(EventStateDef.waitList)))) as Heventmerge.
  unfold event.used_event_rep in Heventmerge.
  sep_apply_l_atomic Heventmerge.
  sep_apply_l_atomic (task_delete_update_preserves_continuation_capsules environment saved_local
    ready tid node (task_set_event_ptr node None) Hnode eq_refl eq_refl).
  unfold task_delete_event_body.
  Exists (task_delete_event_state ready tid node eid ev) (task_set_event_ptr node None).
  assert (Hunlinked : task_delete_event_unlinked ready tid node
    (task_delete_event_state ready tid node eid ev) (task_set_event_ptr node None)).
  { unfold task_delete_event_unlinked; rewrite Hptr; exists ev; auto. }
  assert (Hcoverage' : task_stack_coverage_spec.task_stack_live_coverage
    (task_delete_event_state ready tid node eid ev).(TskState)
    (kernel_stack_world_spec.task_stack_call_active_key current)).
  { eapply task_update_generation_preserves_stack_coverage__event_and_flag_unlink;
      [exact Hnode|reflexivity|exact Hcoverage]. }
  unfold task_delete_masked_raw.
  entailer!.
  pose proof (task_and_event_raw_rep_merge_updated__event_and_flag_unlink
    sg ready tid node (task_set_event_ptr node None) eid ev Hnode eq_refl He) as Hraw.
  cbv zeta in Hraw.
  sep_apply_r_atomic Hraw.
  unfold UCOS2_raw_rep_missing_task_storage_sched_event.
  cbn [task_delete_return_loan task_delete_event_state replace_TskS replace_EventS
    TskState EventState task_tcb_init_continuation_capsules].
  entailer!.
Qed. 

Lemma proof_of_OSTaskDel_which_implies_wit_17 : OSTaskDel_which_implies_wit_17.
Proof. left; intros; apply task_delete_focus_reassemble. Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_18 : OSTaskDel_which_implies_wit_18.
Proof.
  left; intros.
  unfold task_delete_event_body; Intros evented event_node.
  assert (Hhistory : task_delete_live_history sg requested call initial current acquired
    priority (task_slot_addr sg tid) tid node) by tauto.
  assert (Hunlinked : task_delete_event_unlinked (task_delete_ready_state acquired tid)
    tid node evented event_node) by tauto.
  destruct (task_delete_live_history_inv_and_lookup__event_and_flag_unlink
    _ _ _ _ _ _ _ _ _ _ Hhistory) as [Hvalid Hnode].
  assert (Hevent_node : evented.(TskState).(inUsedTaskStates) tid = Some event_node).
  { exact (task_delete_event_unlinked_lookup__event_and_flag_unlink
      (task_delete_ready_state acquired tid) tid node evented event_node Hnode Hunlinked). }
  Exists evented event_node.
  entailer!.
  unfold task_delete_masked_raw at 1; Intros.
  unfold UCOS2_raw_rep at 1; unfold task_stack.task_shared_rep at 1.
  pose proof (task_public_storage_split_field sg evented.(TskState) tid event_node
    (TCBCommonField TCBFlagNode) Hevent_node
    (tcb_configured_common_field_in _ _ TCBFlagNode)) as Hsplit.
  cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell
    tcb_field_address] in Hsplit.
  sep_apply_l_atomic Hsplit.
  unfold task_delete_flag_handle.
  cancel (tcb_field_address (task_slot_addr sg tid) TCBFlagNode # Ptr |-> tcbFlagNode event_node).
  apply_sepcon_adjoint.
  pose proof (task_public_storage_merge_field sg evented.(TskState) tid event_node
    (TCBCommonField TCBFlagNode) Hevent_node
    (tcb_configured_common_field_in _ _ TCBFlagNode)) as Hmerge.
  cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell
    tcb_field_address] in Hmerge.
  unfold task_delete_ptr_cell; cbn [tcb_field_address].
  sep_apply_l_atomic Hmerge.
  unfold task_delete_masked_raw, UCOS2_raw_rep, task_stack.task_shared_rep.
  entailer!.
Qed. 

Lemma proof_of_OSTaskDel_which_implies_wit_19 : OSTaskDel_which_implies_wit_19.
Proof.
  left; intros.
  pose proof (task_delete_event_unlinked_flag_node_eq__event_and_flag_unlink
    _ _ _ _ _ PreH4) as Hflageq.
  assert (Hnonzero : node.(tcbFlagNode) <> 0).
  { unfold task_delete_flag_handle in PreH2; congruence. }
  destruct (task_delete_live_history_inv_and_lookup__event_and_flag_unlink
    _ _ _ _ _ _ _ _ _ _ PreH3) as [Hvalid Hnode].
  assert (Hconfig : sg.(osKernelConfig) = selected_kernel_configuration).
  { unfold task_delete_live_history, task_delete_lookup_history, task_delete_static_profile
      in PreH3; tauto. }
  destruct (task_live_flag_waiter_domain__event_and_flag_unlink
    sg acquired tid node Hconfig Hvalid Hnode Hnonzero) as [waiter [Htid [Hnull Hdomain]]].
  unfold task_delete_event_unlinked in PreH4; rewrite Hnull in PreH4.
  destruct PreH4 as [Hevented Heventnode]; subst evented event_node.
  set (ready := task_delete_ready_state acquired tid).
  fold ready.
  unfold task_delete_ptr_cell; cbn [tcb_field_address].
  sep_apply_l_atomic (task_delete_focus_reassemble
    (tcb_field_address (task_slot_addr sg tid) TCBFlagNode # Ptr |->
      task_delete_flag_handle node)
    (task_delete_masked_raw environment critical saved_local None sg current saved acquired ready)).
  unfold task_delete_masked_raw at 1; Intros.
  assert (Hcoverage : task_stack_coverage_spec.task_stack_live_coverage ready.(TskState)
    (kernel_stack_world_spec.task_stack_call_active_key current)) by assumption.
  unfold UCOS2_raw_rep, task_stack.task_shared_rep.
  sep_apply_l_atomic (task_public_storage_split_task sg ready.(TskState) tid node Hnode).
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false) by (rewrite Hconfig; reflexivity).
  assert (Hprofile : sg.(osKernelConfig).(cfgTaskProfile) = false) by (rewrite Hconfig; reflexivity).
  assert (Hflag : sg.(osKernelConfig).(cfgFlagEnabled) = true) by (rewrite Hconfig; reflexivity).
  pose proof (used_task_rep_tcb64 sg tid node Hmulti Hprofile) as Hused.
  rewrite <- (task_slot_addr_tcb64 sg tid Hmulti Hprofile) in Hused.
  sep_apply_l_atomic (proj1 Hused).
  unfold flag.flag_configured_rep; rewrite Hflag.
  Exists waiter.
  unfold flag_unlink_pre, flag_unlink_task_rep; rewrite Htid.
  entailer!.
  apply_sepcon_adjoint.
  unfold flag_unlink_post; Intros flags.
  assert (Hstep : flag.flag_unlink_node ready.(FlagState) node.(tcbFlagNode) = Some (waiter, flags)) by tauto.
  unfold flag_unlink_task_rep; rewrite Htid.
  pose proof (used_task_rep_tcb64 sg tid (task_set_flag_node node 0) Hmulti Hprofile) as Hupdated.
  rewrite <- (task_slot_addr_tcb64 sg tid Hmulti Hprofile) in Hupdated.
  sep_apply_l_atomic (proj2 Hupdated).
  sep_apply_l_atomic (task_public_storage_merge_updated_task sg ready.(TskState) tid
    (task_set_flag_node node 0)).
  sep_apply_l_atomic (task_delete_update_preserves_continuation_capsules
    environment saved_local ready tid node (task_set_flag_node node 0) Hnode eq_refl eq_refl).
  unfold task_delete_flag_body.
  Exists ready node (task_delete_flag_state ready tid node flags)
    (task_set_flag_node node 0) (Some waiter).
  assert (Hevent : task_delete_event_unlinked ready tid node ready node).
  { unfold task_delete_event_unlinked; rewrite Hnull; auto. }
  assert (Hflagged : task_delete_flag_unlinked ready tid node
    (task_delete_flag_state ready tid node flags) (task_set_flag_node node 0) (Some waiter)).
  { unfold task_delete_flag_unlinked.
    rewrite (proj2 (Z.eqb_neq _ _) Hnonzero).
    exists waiter, flags; auto. }
  assert (Hcoverage' : task_stack_coverage_spec.task_stack_live_coverage
    (task_delete_flag_state ready tid node flags).(TskState)
    (kernel_stack_world_spec.task_stack_call_active_key current)).
  { eapply task_update_generation_preserves_stack_coverage__event_and_flag_unlink;
      [exact Hnode|reflexivity|exact Hcoverage]. }
  unfold task_delete_masked_raw.
  entailer!.
  sep_apply_r_atomic (task_and_flag_raw_rep_merge_updated__event_and_flag_unlink
    sg ready tid node (task_set_flag_node node 0) flags Hnode eq_refl).
  unfold UCOS2_raw_rep_missing_task_storage_sched_flag, flag.flag_configured_rep.
  rewrite Hflag.
  cbn [task_delete_return_loan task_delete_flag_state replace_TskS replace_FlagS
    TskState FlagState task_tcb_init_continuation_capsules].
  entailer!.
Qed. 

Lemma proof_of_OSTaskDel_which_implies_wit_20 : OSTaskDel_which_implies_wit_20.
Proof. left; intros; apply task_delete_focus_reassemble. Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_21 : OSTaskDel_which_implies_wit_21.
Proof.
  left; intros.
  unfold task_delete_flag_body.
  Intros evented event_node flagged flag_node loan.
  Intros.
  destruct H as [Hlive [Hevent Hflag]].
  pose proof Hlive as [Hlookup [Hselected [Htable Hpointer]]].
  destruct (task_delete_table_lookup_live _ _ _ _ Htable) as [_ Hnode].
  pose proof Hlookup as [Hstatic [_ [_ [_ [Hrely Hsuccess]]]]].
  destruct Hrely as [_ [_ [[Hvalid [_ Hdomain]] _]]].
  destruct (Hdomain priority tid node (proj1 Hselected) Htable) as [Hid [Hnonidle Hrest]].
  pose proof (Hsuccess priority tid node (proj1 Hselected) Htable) as Hrun.
  pose proof (task_delete_unlinked_prepare_eq__prepare_and_completed_window
    _ _ _ _ _ _ _ _ Hevent Hflag) as Hprepare.
  pose proof (task_delete_unlinked_lookup__prepare_and_completed_window
    _ _ _ _ _ _ _ _ Hnode Hevent Hflag) as Hflagged.
  set (prepared := replace_TskS (glob_task_set_usedtask flagged.(TskState) tid
    (task_prepare_delete flag_node)) flagged) in *.
  destruct (task_delete_prepare_single_wait_establishes_shared_validity
    sg acquired tid node Hvalid Hnode) as [prepared0 [loan0 [Hprepare0 Hvalid0]]].
  rewrite Hprepare in Hprepare0; injection Hprepare0 as Hprepared Hloan; subst prepared0 loan0.
  pose proof (task_delete_preparation_preserves_running_protocol__prepare_and_completed_window
    _ _ _ _ _ _ _ Hnode Hnonidle Hprepare Hrun) as Hrun_after.
  unfold task_delete_masked_raw.
  Intros.
  match goal with
  | Hc : task_stack_coverage_spec.task_stack_live_coverage _ _ |- _ =>
      pose proof Hc as Hcoverage
  end.
  assert (Hcoverage_after : task_stack_coverage_spec.task_stack_live_coverage prepared.(TskState)
    (task_stack_call_active_key current)).
  { eapply task_stack_coverage_spec.task_stack_live_coverage_used_map_frame
      with (before := flagged.(TskState));
      [|reflexivity|exact Hcoverage].
    intros slot stored Hstored.
    cbn [prepared replace_TskS TskState glob_task_set_usedtask inUsedTaskStates] in Hstored.
    destruct ((slot =? tid)%Z) eqn:Hsame.
    - apply Z.eqb_eq in Hsame; subst slot; injection Hstored as Hstored; subst stored.
      exists flag_node; split; [exact Hflagged|reflexivity].
    - exists stored; auto. }
  sep_apply_l_atomic (task_delete_update_preserves_continuation_capsules
    environment saved_local flagged tid flag_node (task_prepare_delete flag_node)
    Hflagged eq_refl eq_refl).
  pose proof (task_delete_prepare_raw_focus__prepare_and_completed_window sg flagged tid flag_node Hflagged) as Hfocus.
  destruct PreH1 as [_ [Hlock _]].
  unfold task_delete_prepare_cells in Hfocus.
  rewrite Hlock in Hfocus.
  cbn [tcb_field_address] in Hfocus.
  sep_apply_l_atomic Hfocus.
  Exists flag_node flagged.
  unfold task_delete_tcb_value.
  cbn [task_tcb64_image encode_task_status].
  unfold task.encode_task_status, task_status.encode_task_status.
  Intros.
  unfold task_delete_locks.
  entailer!.
  match goal with |- ?L |-- _ =>
    change (L |-- task_delete_prepare_cells sg flagged tid flag_node true -*
      task_delete_prepared_body environment critical saved_local sg requested call initial
        current saved acquired priority (task_slot_addr sg tid) tid node
        (task_delete_added_value flagged))
  end.
  apply_sepcon_adjoint.
  unfold task_delete_prepare_cells; rewrite Hlock; cbn [tcb_field_address].
  unfold task_delete_prepared_body.
  Exists prepared loan.
  unfold task_delete_call_masked,
    kernel_continuation_world_spec.kernel_continuation_call_masked,
    kernel_continuation_world_spec.kernel_continuation_inv,
    task_delete_phase_resources, task_delete_phase_valid,
    task_tcb_init_continuation_call_spec.task_tcb_init_continuation_capsules.
  entailer!.
  match goal with |- ?L |-- _ =>
    change (L |-- UCOS2_raw_rep sg (task_delete_prepare_state flagged tid flag_node) **
      task_tcb_init_continuation_capsules environment saved_local prepared)
  end.
  fold prepared.
  fold (task_tcb_init_continuation_capsules environment saved_local prepared).
  entailer!.
  match goal with
  | |- _ |-- ?Q => match goal with
    | |- context [?P -* Q] =>
        sep_apply_r_atomic (task_delete_focus_reassemble P Q); entailer!
    end
  end.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_22 : OSTaskDel_which_implies_wit_22.
Proof.
  left; intros.
  destruct PreH3 as [_ [Hlock _]].
  unfold task_delete_prepare_cells.
  cbn [tcb_field_address].
  rewrite Hlock.
  unfold task_delete_locks, task_delete_prepare_state.
  cbn [replace_IntrS IntrState].
  entailer!.
  match goal with
  | |- _ |-- ?Q => match goal with
    | |- context [wand ?P Q] =>
        sep_apply_r_atomic (task_delete_focus_reassemble P Q); entailer!
    end
  end.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_23 : OSTaskDel_which_implies_wit_23.
Proof.
  left; intros.
  unfold task_delete_prepared_body, task_delete_preparation_history,
    task_delete_added_value, task_delete_locked.
  Intros prepared loan.
  Exists prepared loan.
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_24 : OSTaskDel_which_implies_wit_24.
Proof.
  left; intros.
  unfold task_delete_restore_post, task_delete_restore_history.
  Intros middle between.
  Exists middle between.
  unfold interrupt_saved_value in PreH1.
  destruct PreH1 as [_ Hmask].
  rewrite Hmask.
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_26 : OSTaskDel_which_implies_wit_26.
Proof.
  left; intros.
  unfold task_delete_save_post.
  Intros resumed_call resumed.
  Exists resumed_call resumed.
  Intros.
  destruct H as [Hsource [Hsame [Hrely Hprotocol]]].
  destruct PreH2 as [Htrace [Hsame0 [Hrely0 Hprotocol0]]].
  pose proof (task_delete_same_return_trans _ _ _ _ _ _ Hsame0 Hsame) as Hsame1.
  pose proof (task_delete_phase_rely_trans _ _ _ _ _ _ Hrely0 Hrely) as Hrely1.
  assert (Hrun : task_delete_running_protocol sg resumed_call resumed).
  { apply (proj1 Hprotocol). apply (proj1 Hprotocol0). exact (proj2 (proj2 PreH1)). }
  assert (Hcall : task_tcb_init_stack_same_call resumed_call call).
  { destruct Hsame1 as [Hs _].
    pose proof PreH1 as [[Hlookup _] _].
    destruct Hlookup as [_ [_ [Horiginal _]]].
    unfold task_tcb_init_stack_same_call in *; intuition congruence. }
  assert (Hmask : interrupt_saved_value mask saved_again).
  { unfold task_resume_spec.kernel_call_save_source in Hsource; tauto. }
  entailer!.
  unfold task_delete_window_history; auto.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_27 : OSTaskDel_which_implies_wit_27.
Proof.
  left; intros.
  destruct PreH1 as [_ [Hlock _]].
  unfold task_delete_call_masked,
    kernel_continuation_world_spec.kernel_continuation_call_masked,
    kernel_continuation_world_spec.kernel_continuation_inv,
    task_delete_phase_resources, task_delete_phase_valid.
  unfold UCOS2_raw_rep, interrupt_inv, store_int_state.
  Intros.
  prop_apply_p (store_uchar_range sg.(g_OSLockNesting) resumed.(IntrState).(lockNesting)).
  Intros.
  unfold task_delete_locks; unfold interrupt_in_range in *.
  try rewrite Hlock.
  entailer!.
  apply_sepcon_adjoint.
  unfold task_delete_uchar_cell, task_delete_released_body, task_delete_masked_raw,
    task_delete_released, UCOS2_raw_rep, interrupt_inv, store_int_state,
    task_tcb_init_continuation_capsules.
  cbn [replace_IntrS TskState IntrState SchedState EventState TickState FlagState
    MemoryState TimerState StatsState ControlState NameState].
  try rewrite Hlock.
  entailer!.
  unfold interrupt_in_range, task_delete_release_state in *; cbn in *.
  destruct (task_delete_lock_added (IntrState prepared) &&
    (Z.ltb 0 (lockNesting (IntrState resumed))))%bool eqn:Hrelease; cbn; try lia.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_28 : OSTaskDel_which_implies_wit_28.
Proof. left; intros; apply task_delete_focus_reassemble. Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_29 : OSTaskDel_which_implies_wit_29.
Proof.
  left; intros.
  unfold task_delete_released_body; Intros.
  match goal with
  | H : task_delete_window_history _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hhistory
  end.
  pose proof Hhistory as [Hpreparation [Hsame [Hrely Hprotocol]]].
  destruct Hpreparation as [[Hlookup [[Hselection Hpointer] [Hlive Hbase]]]
    [Hprepare Hprepared_protocol]].
  pose proof Hlookup as [Hstatic [Hrequested [Hfirst_same [Hprefix [Hlookup_rely Hsuccess_protocol]]]]].
  pose proof Hstatic as [Hprofile [Hconfig Hlayout]].
  destruct Hlookup_rely as [Hinitial_intr [Hinitial_running [[Hvalid Hdomain] Hdomain_copy]]].
  destruct (task_delete_table_lookup_live _ _ _ _ Hlive) as [Htable_acquired Hnode_acquired].
  destruct (proj2 Hdomain priority tid node Hselection Hlive)
    as [Hid [Hnonidle [Hstopped Howner]]].
  pose proof (task_delete_success_domain_successor sg requested acquired priority tid node
    Hvalid Hdomain Hselection Hlive) as Hnext.
  pose proof (task_delete_lookup_selected_in_range sg requested call initial current acquired
    priority Hlookup Hselection) as Hpriority.
  destruct (task_delete_preparation_task_projections__release_and_recycle_resources
    acquired tid node prepared loan Hprepare) as [Hprepared_table Hprepared_node].
  pose proof (task_delete_preparation_preserves_mutex_owner_exclusion__release_and_recycle_resources
    acquired tid node prepared loan Hprepare Howner) as Hprepared_owner.
  destruct Hrely as [Hresumed_intr [Hresumed_running [Hshared [Htable_frame [Hnode_frame Howner_frame]]]]].
  assert (Hnode_resumed : resumed.(TskState).(inUsedTaskStates) tid =
    Some (task_delete_prepared_node node)).
  { apply Hnode_frame; exact Hprepared_node. }
  assert (Htable_resumed : resumed.(TskState).(prioTbl) priority = PTTask tid).
  { rewrite Htable_frame; change (prepared.(TskState).(prioTbl) priority = PTTask tid).
    rewrite Hprepared_table; exact Htable_acquired. }
  assert (Howner_resumed : task_delete_mutex_owner_exclusion resumed tid).
  { apply Howner_frame; exact Hprepared_owner. }
  pose proof (proj1 (proj2 Hshared)) as Htasks.
  pose proof (task_count_in_pool_range sg resumed.(TskState) Hprofile Htasks) as Hcount.
  assert (Hpriority_domain : task_priority_in_range sg priority).
  { pose proof (proj1 Hprofile) as Hstable.
    unfold valid_stable_glob_vars in Hstable.
    unfold task_priority_in_range; lia. }
  assert (Hvalid_cut : UCOS2_state_inv sg
    (task_delete_cut sg prepared resumed tid priority node (LitMap "?"))).
  { apply (task_delete_recycle_restores_global_validity sg
      (task_delete_released prepared resumed) tid node.(taskGeneration) priority
      (task_delete_prepared_node node) (LitMap "?"));
      try assumption; try exact Hshared; try exact Hnode_resumed;
      try exact Htable_resumed; try exact Howner_resumed; try exact Hnonidle.
    all: cbn [task_delete_released replace_IntrS TskState]; lia. }
  assert (Hprotocol_cut : task_delete_running_protocol sg resumed_call
    (task_delete_cut sg prepared resumed tid priority node (LitMap "?"))).
  { apply (task_recycle_preserves_running_protocol__release_and_recycle_resources sg
      (task_delete_released prepared resumed) resumed_call tid priority
      (task_delete_prepared_node node) (LitMap "?")); assumption. }
  assert (Heffect : task_delete_effect sg requested (LitMap "?") initial 0
    (task_delete_cut sg prepared resumed tid priority node (LitMap "?"))).
  { apply (TaskDeleteSuccess sg requested (LitMap "?") initial acquired priority tid node prepared loan resumed);
      try assumption.
    split; [exact Hinitial_intr|]; split; [exact Hinitial_running|];
      split; [split; assumption|exact Hdomain_copy].
    split; [exact Hresumed_intr|]; split; [exact Hresumed_running|];
      split; [exact Hshared|]; split; [exact Htable_frame|]; split; assumption. }
  unfold task_delete_masked_raw; Intros.
  match goal with
  | H : task_stack_coverage_spec.task_stack_live_coverage _ _ |- _ =>
    pose proof H as Hcoverage
  end.
  pose proof (task_recycle_preserves_live_coverage__release_and_recycle_resources sg
    resumed.(TskState) (task_stack_call_active_key resumed_call) tid priority
    (task_delete_prepared_node node) (LitMap "?") Hcoverage) as Hcoverage_cut.
  pose proof (task_recycle_sched_rep_eq__release_and_recycle_resources sg
    (task_delete_released prepared resumed) tid node.(taskGeneration) priority
    (task_delete_prepared_node node) (LitMap "?")
    (proj1 (proj1 (proj2 (proj2 Hshared)))) Hnode_resumed) as Hsched.
  pose proof (task_delete_recycle_event_rep_eq sg (task_delete_released prepared resumed)
    tid node.(taskGeneration) priority (task_delete_prepared_node node) (LitMap "?")
    (proj1 (proj1 (proj2 (proj2 Hshared))))
    (proj1 (proj2 (proj2 (proj2 (proj2 Hshared))))) Hnode_resumed) as Hevent.
  pose proof (task_public_storage_recycle_focus__release_and_recycle_resources sg
    (task_delete_released prepared resumed) tid priority (task_delete_prepared_node node)
    (LitMap "?") Hconfig Htasks Hnode_resumed Htable_resumed ltac:(lia) Hnext) as Hfocus.
  unfold task_delete_recycle_cells at 1 in Hfocus; cbn zeta in Hfocus.
  destruct PreH1 as [_ [_ [_ [Hfree [Hlist [Hctr [Htable _]]]]]]].
  rewrite Hfree, Hlist, Hctr, Htable in Hfocus.
  unfold UCOS2_raw_rep, task_stack.task_shared_rep.
  sep_apply_l_atomic Hfocus.
  unfold task_delete_count, task_delete_free_head, task_delete_list_head,
    task_delete_next, task_delete_prev.
  cbn [tcb_field_address].
  change (sizeof(PTR)) with 4.
  sepcon_assoc_change; cancel; apply_sepcon_adjoint.
  match goal with
  | |- ?P |-- _ => match P with context [wand ?part ?whole] =>
      sep_apply (task_delete_focus_reassemble part whole) end
  end.
  sep_apply_l_atomic (task_delete_recycle_preserves_continuation_capsules environment saved_local sg
    (task_delete_released prepared resumed) tid priority (task_delete_prepared_node node) (LitMap "?")).
  rewrite Hsched, Hevent.
  unfold task_delete_recycled_body, task_delete_call_masked,
    kernel_continuation_world_spec.kernel_continuation_call_masked,
    kernel_continuation_world_spec.kernel_continuation_inv,
    task_delete_phase_resources, task_delete_phase_valid,
    UCOS2_raw_rep, task_stack.task_shared_rep, task_tcb_init_continuation_capsules.
  entailer!.
  unfold task_delete_cut, task_delete_recycled, task_delete_released.
  cbn [replace_TskS replace_IntrS TskState SchedState IntrState EventState TickState
    FlagState MemoryState TimerState StatsState ControlState NameState task_recycle parkedTaskStacks].
  entailer!.
Qed. 

Lemma proof_of_OSTaskDel_which_implies_wit_30 : OSTaskDel_which_implies_wit_30.
Proof.
  left; intros.
  destruct PreH1 as [[[Hlookup [Hselected [Hlive Hpointer]]] Hpreparation] Hwindow].
  destruct Hlookup as [Hstatic [Hrequested [Hsame [Hprefix [Hrely Hprotocol]]]]].
  destruct Hrely as [_ [_ [[Hvalid Hdomain] Hdomain']]].
  destruct (task_delete_table_lookup_live _ _ _ _ Hlive) as [Htable Hnode].
  assert (Hprev : node.(prevTCB) = None).
  { apply (proj1 (task_prev_encoded_zero_iff__release_and_recycle_resources
      sg acquired.(TskState) tid node Hstatic (proj1 (proj2 Hvalid)) Hnode)).
    exact PreH2. }
  unfold task_delete_neighbor_cells, task_delete_next.
  change (node.(prevTCB) = None) in Hprev.
  cbn [task_delete_prepared_node task_prepare_delete task_set_flag_node task_set_event_ptr prevTCB].
  rewrite Hprev; cbn [tcb_field_address]; entailer!.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_31 : OSTaskDel_which_implies_wit_31.
Proof.
  left; intros.
  destruct PreH1 as [[[Hlookup [Hselected [Hlive Hpointer]]] Hpreparation] Hwindow].
  destruct Hlookup as [Hstatic [Hrequested [Hsame [Hprefix [Hrely Hprotocol]]]]].
  destruct Hrely as [_ [_ [[Hvalid Hdomain] Hdomain']]].
  destruct (task_delete_table_lookup_live _ _ _ _ Hlive) as [Htable Hnode].
  assert (Hprev : node.(prevTCB) = None).
  { apply (proj1 (task_prev_encoded_zero_iff__release_and_recycle_resources
      sg acquired.(TskState) tid node Hstatic (proj1 (proj2 Hvalid)) Hnode)).
    exact PreH2. }
  unfold task_delete_neighbor_cells, task_delete_next.
  cbn [task_delete_prepared_node task_prepare_delete task_set_flag_node task_set_event_ptr prevTCB].
  rewrite Hprev; cbn [encode_task_link tcb_field_address]; entailer!.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_32 : OSTaskDel_which_implies_wit_32.
Proof.
  left; intros.
  unfold task_delete_neighbor_cells, task_delete_prev, task_delete_next in *.
  destruct (prevTCB (task_delete_prepared_node node));
    cbn [encode_task_link tcb_field_address] in *; [entailer!|contradiction].
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_33 : OSTaskDel_which_implies_wit_33.
Proof.
  left; intros.
  unfold task_delete_neighbor_cells, task_delete_prev, task_delete_next in *.
  destruct (prevTCB (task_delete_prepared_node node));
    cbn [encode_task_link tcb_field_address] in *; [entailer!|contradiction].
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_34 : OSTaskDel_which_implies_wit_34.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range (&("OSTaskCtr"))
    (Z.rem (task_delete_count (task_delete_released prepared resumed) - 1) 256)).
  Intros.
  change Byte.max_unsigned with 255 in *.
  assert (Hremainder : Z.rem (task_delete_count (task_delete_released prepared resumed) - 1) 256 =
    (task_delete_count (task_delete_released prepared resumed) - 1) mod 256).
  { apply Z.mod_unique_pos with (q := Z.quot (task_delete_count (task_delete_released prepared resumed) - 1) 256);
      [lia|apply Z.quot_rem; lia]. }
  rewrite Hremainder.
  destruct PreH1 as [_ [_ [_ [Hfree [Hlist [Hcount [Htable _]]]]]]].
  sep_apply_r_atomic (task_delete_focus_reassemble
    (task_delete_recycle_cells sg (task_delete_released prepared resumed) tid priority
      (task_delete_prepared_node node) (LitMap "?") true)
    (task_delete_recycled_body environment critical saved_local sg requested call initial
      resumed_call saved_again resumed
      (task_delete_cut sg prepared resumed tid priority node (LitMap "?")) loan (LitMap "?"))).
  cancel.
  unfold task_delete_recycle_cells, task_delete_count, task_delete_free_head, task_delete_prev,
    task_delete_list_head, task_delete_cut, task_delete_recycled, task_delete_released.
  cbn [replace_TskS replace_IntrS TskState tcbListHead task_recycle tcb_field_address].
  rewrite Hfree, Hlist, Hcount, Htable.
  change (sizeof(PTR)) with 4.
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_35 : OSTaskDel_which_implies_wit_35.
Proof.
  left; intros; unfold task_delete_recycled_body, task_delete_result_history;
    entailer!.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_36 : OSTaskDel_which_implies_wit_36.
Proof.
  left; intros.
  destruct PreH1 as [_ Hmask]; rewrite Hmask.
  apply task_delete_final_restore_body; assumption.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_37 : OSTaskDel_which_implies_wit_37.
Proof.
  left; intros.
  assert (Haddress : g_OSRunning sg = &("OSRunning"))
    by (unfold task_delete_global_addresses in PreH1; tauto).
  unfold task_delete_final_body, task_delete_call_closed,
    kernel_continuation_world_spec.kernel_continuation_call_closed,
    kernel_continuation_world_spec.kernel_continuation_inv,
    task_delete_phase_resources.
  rewrite UCOS2_raw_rep_split_running.
  unfold task_delete_uchar_cell, task_delete_running.
  rewrite Haddress; Intros.
  cancel (&("OSRunning") # UChar |->
    (if isRunning (SchedState final_state) then 1 else 0)).
  apply_sepcon_adjoint; entailer!.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_38 : OSTaskDel_which_implies_wit_38.
Proof.
  left; intros.
  unfold task_delete_uchar_cell.
  sep_apply task_delete_focus_reassemble.
  unfold task_delete_final_body; Intros.
  assert (Hrunning : isRunning (SchedState final_state) = true).
  { unfold task_delete_running in PreH1.
    destruct (isRunning (SchedState final_state)); congruence. }
  assert (Hhistory : exists cut_call,
    task_delete_result_history sg requested (LitMap "?") call initial cut_call
      (task_delete_cut sg prepared resumed tid priority node (LitMap "?")) /\
    task_delete_restore_history environment critical requested TaskDeleteStable sg cut_call
      (task_delete_cut sg prepared resumed tid priority node (LitMap "?")) final_call final_state)
    by tauto.
  destruct Hhistory as [cut_call [Hresult Hrestore]].
  pose proof (task_delete_final_body_sched_safe environment critical sg requested
    (LitMap "?") call mask initial cut_call
    (task_delete_cut sg prepared resumed tid priority node (LitMap "?"))
    final_call final_state X Hresult Hrestore Hrunning PreH2) as Hschedule.
  assert (Hcut : os_sched_call_cut sg final_call final_state).
  { apply task_delete_running_protocol_sched_cut; tauto. }
  rewrite task_delete_call_closed_stable_split_loan.
  unfold os_sched_continuation_call_pre.
  entailer!.
  apply_sepcon_adjoint.
  sep_apply (task_delete_scheduled_api_post environment critical saved_local sg
    requested (LitMap "?") call mask initial cut_call
    (task_delete_cut sg prepared resumed tid priority node (LitMap "?"))
    final_call final_state loan X Hresult Hrestore Hrunning Hschedule).
  entailer!.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_39 : OSTaskDel_which_implies_wit_39.
Proof.
  left; intros; unfold task_delete_sched_history_return_with_loan; reflexivity.
Qed.

Lemma proof_of_OSTaskDel_which_implies_wit_40 : OSTaskDel_which_implies_wit_40.
Proof.
  left; intros; apply task_delete_focus_reassemble.
Qed.

