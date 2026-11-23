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
From Ucos2Verify.VC.code.queue Require Import q_create_goal.
From Ucos2Verify.VC.code.queue Require Import q_create_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_spec.
Local Open Scope sac.

Lemma proof_of_OSQCreate_return_wit_1 : OSQCreate_return_wit_1.
Proof.
  left. intros.
  destruct PreH12 as [Hentry Hsr].
  unfold crit_rel_no_os_state_change in Hentry. subst critical_entry.
  destruct PreH5 as [Hentry Hsr2].
  unfold crit_rel_no_os_state_change in Hentry. subst critical_entry_2.
  prop_apply (verification_slice_q_create_event_residual_valid__return_paths sg lvs event_rest).
  pureIntros. rename H into Hevent.
  prop_apply (store_uchar_range (&("OSIntNesting")) (q_create_int_nesting lvs)).
  pureIntros. rename H into Hrange.
  rewrite unsigned_last_nbits_eq in PreH14 by
    (change (0 <= q_create_int_nesting lvs < 4294967296); change (0 <= q_create_int_nesting lvs <= 255) in Hrange; lia).
  assert (Hworld_cons : verification_slice_q_create_world_pure sg start_pre size_pre buffer lvs (qid :: queue_rest)).
  { rewrite <- PreH1. exact PreH16. }
  pose proof (verification_slice_q_create_world_pure_after__return_paths sg start_pre size_pre buffer
    lvs eid event_rest qid queue_rest PreH8 Hevent Hworld_cons) as Hnewworld.
  assert (Hnewvalid : verification_slice_event_in_range sg (TskState lvs)
    (verification_slice_q_create_event_state (EventState lvs) eid event_rest qid start_pre size_pre buffer)).
  { eapply verification_slice_q_create_event_valid_after__return_paths with (queue_rest := queue_rest).
    - exact PreH2.
    - unfold verification_slice_q_create_world_pure in PreH16. tauto.
    - unfold verification_slice_q_create_world_pure in PreH16. tauto.
    - exact PreH8.
    - exact Hevent.
    - unfold verification_slice_q_create_world_pure in PreH16. rewrite PreH1 in PreH16. tauto. }
  pose proof (q_create_old_event_none__return_paths sg (TskState lvs) (EventState lvs)
    eid event_rest PreH8 Hevent) as Hnone.
  assert (Hsem : verification_slice_OSQCreate_sem sg start_pre size_pre queue_free_ids buffer lvs
    (QCreateSuccess eid qid queue_rest)
    (verification_slice_q_create_success_state lvs eid event_rest qid start_pre size_pre buffer)).
  { unfold verification_slice_OSQCreate_sem.
    assert (Hgt : Z.gtb (intNesting (IntrState lvs)) 0 = false).
    { destruct (Z.gtb (intNesting (IntrState lvs)) 0) eqn:Htest; [|reflexivity].
      apply Z.gtb_lt in Htest. unfold q_create_int_nesting in PreH14. lia. }
    rewrite Hgt. change (unUsedEventStates (EventState lvs) = eid :: event_rest) in PreH8.
    rewrite PreH8, PreH1. auto. }
  pose proof (q_create_atomic_safe_return__return_paths QCreateOutcome
    (verification_slice_OSQCreate_sem sg start_pre size_pre queue_free_ids buffer)
    lvs (verification_slice_q_create_success_state lvs eid event_rest qid start_pre size_pre buffer)
    (QCreateSuccess eid qid queue_rest) X Hsem PreH18) as Hsafe.
  destruct PreH15 as [Hint [Hev [Hq [Htable [Hqtable Hprofile]]]]].
  unfold os_int_nesting_addr in Hint.
  unfold os_event_free_list_addr in Hev.
  unfold os_q_free_list_addr in Hq.
  pose proof (event_table_layout_select sg eid Htable PreH9) as Hefields.
  destruct Hefields as [[Ht [Hp Hc]] [Hg Hb]].
  pose proof (queue_table_layout_select sg (g_OSQTbl sg) qid Hqtable PreH2) as Hqfields.
  destruct Hprofile as [_ Hsize].
  cbn [sizeof_front_end_type sizeof_front_end_type_of_ptr_size] in Hqfields.
  rewrite Hsize in Hqfields. fold (qcb_addr sg qid) in Hqfields.
  destruct Hqfields as [Hqp [Hqs [Hqe [Hqi [Hqo [Hqz Hqn]]]]]].
  rewrite PreH3, PreH10, Hint, Hev, Hq, Ht, Hp, Hc, Hg, Hb,
    Hqp, Hqs, Hqe, Hqi, Hqo, Hqz, Hqn.
  cbn [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
  rewrite !Z.mul_1_r.
  sep_apply_l_atomic (verification_slice_q_create_initialized_event__return_paths
    sg (TskState lvs) eid qid start_pre size_pre).
  unfold verification_slice_q_create_event_residual, q_create_interrupt_residual, q_create_int_nesting.
  sep_apply_l_atomic (verification_slice_q_create_event_inv_after__return_paths sg (TskState lvs) (EventState lvs)
    eid event_rest qid start_pre size_pre buffer Hnone Hnewvalid).
  sep_apply_l_atomic (q_create_interrupt_rebuild__return_paths sg (IntrState lvs)).
  sep_apply_l_atomic (verification_slice_q_create_outside_after__return_paths sg lvs eid event_rest qid start_pre size_pre buffer).
  Exists (verification_slice_q_create_success_state lvs eid event_rest qid start_pre size_pre buffer)
    (QCreateSuccess eid qid queue_rest).
  unfold verification_slice_q_create_post_world, verification_slice_q_create_success_world, q_create_return_ptr, q_create_safe_post.
  apply _derivable1_andp_intros.
  - apply _derivable1_andp_intros.
    + apply derivable1s_coq_prop_r. reflexivity.
    + apply derivable1s_coq_prop_r. exact Hsafe.
  - apply _derivable1_andp_intros.
    + apply derivable1s_coq_prop_r. split; [exact Hnewworld|].
      split; [apply verification_slice_q_create_event_lookup_after__return_paths|apply verification_slice_q_create_published_buffer_lookup].
    + unfold q_create_outside, q_create_queue_free_nodes, q_create_buffer,
          store_free_queue_list, used_queue_control_block, q_create_queue_fields,
          queue_end_addr, queue_in_addr, queue_out_addr, queue_entries, sizeof_ptr.
      cbn [verification_slice_q_create_success_state replace_EventS EventState TskState IntrState qID qStart qSize qInIndex qOutIndex qMessages Arch32.ptr_size_Z].
      rewrite !Z.add_0_r.
      entailer!.
      change Arch32.ptr_size_Z with 4.
      rewrite Zlength_nil. cancel.
      apply store_ptr_undef_store_ptr.
Qed.

Lemma proof_of_OSQCreate_return_wit_2 : OSQCreate_return_wit_2.
Proof.
  left. intros.
  destruct PreH9 as [Hentry Hsr].
  unfold crit_rel_no_os_state_change in Hentry. subst critical_entry.
  destruct PreH2 as [Hentry Hsr2].
  unfold crit_rel_no_os_state_change in Hentry. subst critical_entry_2.
  assert (Hempty : queue_free_ids = nil).
  { eapply q_create_free_queue_head_zero_empty__return_paths; eauto.
    - exact (proj1 PreH13).
    - unfold verification_slice_q_create_world_pure in PreH13. tauto. }
  subst queue_free_ids.
  assert (Hsem : verification_slice_OSQCreate_sem sg start_pre size_pre nil buffer lvs
    (QCreateFailure nil) lvs).
  { unfold verification_slice_OSQCreate_sem.
    destruct (Z.gtb (intNesting (IntrState lvs)) 0); [auto|].
    change (unUsedEventStates (EventState lvs) = eid :: event_rest) in PreH5.
    rewrite PreH5. auto. }
  pose proof (q_create_atomic_safe_return__return_paths QCreateOutcome
    (verification_slice_OSQCreate_sem sg start_pre size_pre nil buffer)
    lvs lvs (QCreateFailure nil) X Hsem PreH15) as Hsafe.
  destruct PreH12 as [Hint [Hev [Hq [Htable Hqlayout]]]].
  unfold os_int_nesting_addr in Hint.
  unfold os_event_free_list_addr in Hev.
  unfold os_q_free_list_addr in Hq.
  pose proof (event_table_layout_select sg eid Htable PreH6) as Hfields.
  destruct Hfields as [[Ht [Hp Hc]] [Hg Hb]].
  rewrite PreH7, Hint, Hev, Hq, Ht, Hp, Hc, Hg, Hb.
  cbn [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
  rewrite !Z.mul_1_r.
  unfold verification_slice_q_create_event_residual, q_create_interrupt_residual, q_create_int_nesting.
  sep_apply_l_atomic (q_create_event_rollback_rebuild__return_paths
    sg (TskState lvs) (EventState lvs) eid event_rest PreH5).
  sep_apply_l_atomic (q_create_interrupt_rebuild__return_paths sg (IntrState lvs)).
  Exists lvs (QCreateFailure nil).
  unfold verification_slice_q_create_post_world, verification_slice_q_create_world, q_create_return_ptr,
    q_create_safe_post, q_create_outside, q_create_queue_free_nodes,
    q_create_buffer, store_free_queue_list.
  entailer!.
Qed.

Lemma proof_of_OSQCreate_return_wit_3 : OSQCreate_return_wit_3.
Proof.
  left. intros.
  destruct PreH3 as [Hentry Hsr].
  unfold crit_rel_no_os_state_change in Hentry. subst critical_entry.
  unfold verification_slice_q_create_event_no_free_head, verification_slice_event_inv_no_free_head.
  pureIntros.
  assert (Hfree : unUsedEventStates (EventState lvs) = nil).
  { eapply q_create_free_event_head_zero_empty__return_paths; eauto.
    exact (proj1 PreH7). }
  assert (Hsem : verification_slice_OSQCreate_sem sg start_pre size_pre queue_free_ids buffer lvs
    (QCreateFailure queue_free_ids) lvs).
  { unfold verification_slice_OSQCreate_sem. rewrite Hfree.
    destruct (Z.gtb (intNesting (IntrState lvs)) 0); auto. }
  pose proof (q_create_atomic_safe_return__return_paths QCreateOutcome
    (verification_slice_OSQCreate_sem sg start_pre size_pre queue_free_ids buffer)
    lvs lvs (QCreateFailure queue_free_ids) X Hsem PreH9) as Hsafe.
  destruct PreH6 as [Hint [Hev [Hq Hlayouts]]].
  unfold os_int_nesting_addr in Hint.
  unfold os_event_free_list_addr in Hev.
  unfold os_q_free_list_addr in Hq.
  rewrite Hint, Hev, Hq.
  Exists lvs (QCreateFailure queue_free_ids).
  unfold verification_slice_q_create_post_world, verification_slice_q_create_world, q_create_return_ptr,
    q_create_safe_post, q_create_outside, q_create_int_nesting,
    q_create_interrupt_residual, q_create_unused_events,
    q_create_queue_free_nodes, q_create_buffer,
    interrupt_inv, interrupt_inv_no_int_nesting, store_int_state,
    verification_slice_event_inv, store_free_event_list, store_free_queue_list.
  entailer!.
Qed.

Lemma proof_of_OSQCreate_return_wit_4 : OSQCreate_return_wit_4.
Proof.
  left. intros.
  prop_apply (store_uchar_range (&("OSIntNesting")) (q_create_int_nesting lvs)).
  pureIntros.
  rewrite unsigned_last_nbits_eq in PreH1 by
    (change (0 <= q_create_int_nesting lvs < 4294967296); change (0 <= q_create_int_nesting lvs <= 255) in H; lia).
  assert (Hsem : verification_slice_OSQCreate_sem sg start_pre size_pre queue_free_ids buffer lvs
    (QCreateFailure queue_free_ids) lvs).
  { unfold verification_slice_OSQCreate_sem.
    assert (Hgt : Z.gtb (intNesting (IntrState lvs)) 0 = true).
    { apply Z.gtb_lt. unfold q_create_int_nesting in PreH1. lia. }
    rewrite Hgt. auto. }
  pose proof (q_create_atomic_safe_return__return_paths QCreateOutcome
    (verification_slice_OSQCreate_sem sg start_pre size_pre queue_free_ids buffer)
    lvs lvs (QCreateFailure queue_free_ids) X Hsem PreH5) as Hsafe.
  destruct PreH2 as [Hint [Hev [Hq Hlayouts]]].
  unfold os_int_nesting_addr in Hint.
  unfold os_event_free_list_addr in Hev.
  unfold os_q_free_list_addr in Hq.
  rewrite Hint, Hev, Hq.
  Exists lvs (QCreateFailure queue_free_ids).
  unfold verification_slice_q_create_post_world, verification_slice_q_create_world, q_create_return_ptr,
    q_create_safe_post, q_create_outside, q_create_int_nesting,
    q_create_interrupt_residual, q_create_unused_events,
    verification_slice_q_create_event_no_free_head, q_create_queue_free_nodes, q_create_buffer,
    interrupt_inv, interrupt_inv_no_int_nesting, store_int_state,
    verification_slice_event_inv, verification_slice_event_inv_no_free_head, store_free_event_list,
    store_free_queue_list.
  entailer!.
Qed.

Lemma proof_of_OSQCreate_partial_solve_wit_7_pure : OSQCreate_partial_solve_wit_7_pure.
Proof.
  left. intros.
  entailer!.
  unfold verification_slice_q_create_world_pure in PreH13. tauto.
Qed.

Lemma proof_of_OSQCreate_which_implies_wit_1 : OSQCreate_which_implies_wit_1.
Proof.
  left. intros.
  destruct PreH1 as [Hint [Hev [Hq Hlayouts]]].
  unfold os_int_nesting_addr in Hint.
  unfold os_event_free_list_addr in Hev.
  unfold os_q_free_list_addr in Hq.
  unfold verification_slice_q_create_world, q_create_outside, q_create_int_nesting,
    q_create_interrupt_residual, q_create_unused_events,
    verification_slice_q_create_event_no_free_head, q_create_queue_free_nodes, q_create_buffer,
    interrupt_inv, interrupt_inv_no_int_nesting, store_int_state,
    verification_slice_event_inv, verification_slice_event_inv_no_free_head, store_free_event_list,
    store_free_queue_list.
  rewrite Hint, Hev, Hq.
  entailer!.
  unfold q_create_global_layout_prop, os_int_nesting_addr,
    os_event_free_list_addr, os_q_free_list_addr. tauto.
Qed.

Lemma proof_of_OSQCreate_which_implies_wit_2 : OSQCreate_which_implies_wit_2.
Proof.
  left. intros lvs sg pevent Hnz Hhead Hlayout.
  unfold q_create_unused_events in *.
  destruct (unUsedEventStates (EventState lvs)) as [|eid rest] eqn:Hfree.
  - cbn [free_event_head] in Hhead. subst pevent. contradiction.
  - cbn [free_event_head] in Hhead. subst pevent.
    unfold verification_slice_q_create_event_no_free_head, verification_slice_event_inv_no_free_head.
    pureIntros.
    assert (Hid : valid_event_id sg eid).
    { unfold verification_slice_event_in_range in H.
      destruct H as [_ [_ [Hids _]]]. rewrite Hfree in Hids.
      inversion Hids; subst. assumption. }
    destruct Hlayout as [_ [_ [_ [Htable _]]]].
    pose proof (event_table_layout_select sg eid Htable Hid) as Hfields.
    destruct Hfields as [[Ht [Hp Hc]] [Hg Hb]].
    rewrite Ht, Hp, Hc, Hg, Hb.
    cbn [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
    Exists eid rest.
    unfold verification_slice_q_create_event_residual, verification_slice_event_inv_free_head_rest.
    rewrite Hfree. cbn [store_free_event_nodes encode_event_type].
    rewrite Z.add_0_r.
    entailer!.
    rewrite !Z.add_0_r, !Z.mul_1_r. cancel.
Qed.

Lemma proof_of_OSQCreate_which_implies_wit_3 : OSQCreate_which_implies_wit_3.
Proof.
  left. intros ids sg pq Hnz Hhead Hvalid Hlayout.
  destruct ids as [|qid rest].
  - cbn [queue_free_head] in Hhead. subst pq. contradiction.
  - cbn [queue_free_head] in Hhead. subst pq.
    assert (Hid : valid_queue_id sg qid).
    { destruct Hvalid as [_ Hids]. inversion Hids; subst. assumption. }
    destruct Hlayout as [_ [_ [_ [_ [Htable Hprofile]]]]].
    pose proof (queue_table_layout_select sg (g_OSQTbl sg) qid Htable Hid) as Hfields.
    destruct Hprofile as [_ Hsize].
    cbn [sizeof_front_end_type sizeof_front_end_type_of_ptr_size] in Hfields. rewrite Hsize in Hfields.
    fold (qcb_addr sg qid) in Hfields.
    destruct Hfields as [Hp [Hs [He [Hi [Ho [Hz Hn]]]]]].
    rewrite Hp, Hs, He, Hi, Ho, Hz, Hn.
    Exists qid rest.
    unfold q_create_queue_free_nodes. cbn [store_free_queue_nodes].
    unfold free_queue_node.
    entailer!.
Qed.
