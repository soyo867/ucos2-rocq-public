Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String.
Require Import Coq.micromega.Lia.
From AUXLib Require Import int_auto ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.VC.code.queue.q_create_current_goal.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_proof_helpers.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_call_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wait_list_init_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

Lemma proof_of_OSQCreate_entail_wit_1 : OSQCreate_entail_wit_1.
Proof.
  left; intros.
  assert (Hbinding : sem_create_source_binding sg)
    by (unfold q_create_input_facts, q_create_source_binding in *; tauto).
  sep_apply_l_atomic (q_create_save_output_observation environment critical QCreateNoPrivate
    (q_create_buffer start_pre size_pre slots) sg call mask retval initial).
  Intros returned current.
  rewrite q_create_restore_input_open.
  rewrite (sem_create_pool_split_head sg current Hbinding).
  unfold q_create_owned, q_create_masked_control, q_create_first_facts.
  Exists returned current; unfold kernel_call_normal_return in *; entailer!.
Qed.

Lemma proof_of_OSQCreate_entail_wit_2 : OSQCreate_entail_wit_2.
Proof.
  left; intros.
  assert (Hbinding : sem_create_source_binding sg)
    by (unfold q_create_input_facts, q_create_source_binding in *; tauto).
  assert (Hvalid : UCOS2_state_inv sg entry)
    by (unfold q_create_first_facts in *; tauto).
  destruct entry.(EventState).(unUsedEventStates) as [|eid rest] eqn:Hhead.
  - apply (proj2 (sem_create_pool_head_null_iff sg entry Hbinding Hvalid)) in Hhead;
      contradiction.
  - destruct (sem_create_pool_nonempty_facts sg entry eid rest Hvalid Hhead)
      as [Hrange [image [Himage Hlink]]].
    assert (Hptr : sem_create_pool_head sg entry = event_pool_addr sg eid)
      by (unfold sem_create_pool_head; rewrite Hhead; reflexivity).
    sep_apply_l_atomic (sem_create_pool_split_node sg entry eid rest image Hbinding Hvalid Hhead Himage).
    Exists eid rest image first_call_2 entry.
    unfold sem_create_head_facts, sem_create_link_addr; rewrite Hptr; entailer!.
Qed.

Lemma proof_of_OSQCreate_entail_wit_3_1 : OSQCreate_entail_wit_3_1.
Proof.
  right; intros.
  assert (Hbinding : sem_create_source_binding sg)
    by (unfold q_create_input_facts, q_create_source_binding in *; tauto).
  assert (Hvalid : UCOS2_state_inv sg entry)
    by (unfold q_create_first_facts in *; tauto).
  destruct PreH3 as [Hhead Himage]; subst pevent.
  set (allocated := replace_EventS (event_detach_head entry.(EventState) eid rest image) entry).
  assert (Hstep : event_create_allocate_critical entry (Some (eid, image)) allocated).
  { unfold event_create_allocate_critical; rewrite Hhead; exists image;
      split; [exact Himage|]; split; reflexivity. }
  pose proof (proj2 (event_create_allocate_critical_private_result _ _ _ _ Hstep)) as Hprivate.
  assert (Hnames : cfgEventNames (osKernelConfig sg) = false)
    by (destruct Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto).
  fold (sem_create_link_addr (event_pool_addr sg eid)).
  pose proof (sem_create_pool_merge_detached_node sg entry eid rest image
    Hbinding Hvalid Hhead Himage) as Hmerge.
  lazymatch goal with |- _ |-- ?Post =>
    assert (Hcut : (event_storage_rep false (event_pool_addr sg eid) image ** UCOS2_inv sg allocated) **
      (q_create_masked_control environment critical sg first_call cpu_sr entry entry **
       q_create_buffer start_pre size_pre slots) |-- Post)
  end.
  {
  unfold q_create_allocation_cut; Exists first_call entry (Some (eid, image)) allocated.
  rewrite q_create_restore_input_open.
  unfold q_create_allocated_owner, q_create_owned, event_private_storage_rep;
    rewrite Hnames.
  unfold q_create_masked_control; Intros.
  cbn [sem_create_allocation_identity eventPrivateStorage event_create_return_ptr].
  change (TskState allocated) with (TskState entry).
  entailer!.
  }
  sep_apply_r_atomic Hcut; sep_apply_r_atomic Hmerge; entailer!.
Qed.

Lemma proof_of_OSQCreate_entail_wit_3_2 : OSQCreate_entail_wit_3_2.
Proof.
  right; intros.
  assert (Hbinding : sem_create_source_binding sg)
    by (unfold q_create_input_facts, q_create_source_binding in *; tauto).
  assert (Hvalid : UCOS2_state_inv sg entry)
    by (unfold q_create_first_facts in *; tauto).
  assert (Hempty : entry.(EventState).(unUsedEventStates) = [])
    by (apply (proj1 (sem_create_pool_head_null_iff sg entry Hbinding Hvalid)); assumption).
  assert (Hstep : event_create_allocate_critical entry None entry).
  { unfold event_create_allocate_critical; rewrite Hempty; split; reflexivity. }
  unfold q_create_allocation_cut; Exists first_call entry (@None (EventID * EventStorage)) entry.
  rewrite q_create_restore_input_open, (sem_create_pool_split_head sg entry Hbinding).
  unfold q_create_masked_control, q_create_allocated_owner, q_create_owned;
    cbn [event_create_return_ptr]; entailer!.
Qed.

Lemma proof_of_OSQCreate_entail_wit_4 : OSQCreate_entail_wit_4.
Proof.
  left; intros.
  pose proof PreH1 as [Hnest [Henter [Hfirst_same [Hsaved Hentry_valid]]]].
  assert (Hbinding : sem_create_source_binding sg)
    by (unfold q_create_input_facts, q_create_source_binding in PreH4; tauto).
  sep_apply_l_atomic (q_create_restore_output_observation environment critical
    (q_create_allocated_owner entry allocation_result) (q_create_buffer start_pre size_pre slots)
    sg first_call cpu_sr allocated).
  Intros returned current.
  assert (Hrestore : critical_region_interval critical sg first_call.(os_sched_call_invocation)
    allocated current) by tauto.
  assert (Hnormal : kernel_call_normal_return first_call allocated returned current) by tauto.
  assert (Hsame : task_tcb_init_stack_same_call returned call).
  { destruct Hnormal as [Hreturn_same _]; unfold task_tcb_init_stack_same_call in *;
      intuition congruence. }
  rewrite (proj1 Hfirst_same) in Hrestore.
  rewrite (proj2 Hsaved).
  destruct allocation_result as [[eid image]|].
  - cbn [event_create_return_ptr] in PreH3; subst pevent.
    assert (Hrange : 0 <= eid < sg.(osMaxEvents)).
    { pose proof PreH2 as Hallocate; unfold event_create_allocate_critical in Hallocate.
      destruct entry.(EventState).(unUsedEventStates) as [|head rest] eqn:Hfree.
      - destruct Hallocate as [Hbad _]; discriminate.
      - destruct Hallocate as [bytes [Hbytes [Hresult Hstate]]].
        assert (head = eid) by congruence; subst head.
        exact (proj1 (sem_create_pool_nonempty_facts sg entry eid rest Hentry_valid Hfree)). }
    assert (Hpositive : 0 < event_pool_addr sg eid).
    { destruct Hbinding as [_ [_ [_ Hlayout]]]; exact (proj1 (proj1 (Hlayout eid Hrange))). }
    pose proof (proj2 (event_create_allocate_critical_private_result entry eid image allocated PreH2))
      as Hallocated_get.
    change (allocated.(EventState).(eventLifecycle).(eventPrivate) eid =
      Some (sem_create_allocation_identity entry image)) in Hallocated_get.
    rewrite q_create_save_input_open; cbn [q_create_allocated_owner q_create_owned]; Intros.
    assert (Hcurrent_get : current.(EventState).(eventLifecycle).(eventPrivate) eid =
      Some (sem_create_allocation_identity entry image)) by tauto.
    assert (Hhistory : q_create_event_history critical sg call.(os_sched_call_invocation)
      initial eid (sem_create_allocation_identity entry image) current).
    { split; [exact Hnest|]; exists entry, image, allocated.
      split; [exact Hentry_valid|]. split; [exact Henter|]. split; [exact PreH2|].
      split; [reflexivity|]. split; [exact Hrestore|].
      exists (sem_create_allocation_identity entry image); split; assumption. }
    unfold q_create_allocation_return; Exists returned current.
    destruct (Z.eq_dec (event_pool_addr sg eid) 0); [lia|].
    Exists eid (sem_create_allocation_identity entry image).
    rewrite q_create_save_input_open; cbn [q_create_owned]; entailer!.
  - cbn [event_create_return_ptr] in PreH3; subst pevent.
    assert (Hhistory : q_create_error_history critical sg call.(os_sched_call_invocation) initial current).
    { split; [exact Hnest|]; exists entry, None, allocated.
      split; [exact Henter|]. split; [exact PreH2|]. exact Hrestore. }
    unfold q_create_allocation_return; Exists returned current.
    destruct (Z.eq_dec 0 0); [|contradiction].
    cbn [q_create_allocated_owner]; entailer!.
Qed.

Lemma proof_of_OSQCreate_entail_wit_5 : OSQCreate_entail_wit_5.
Proof.
  left; intros.
  assert (Hroot : &("OSQFreeList") = sg.(g_OSQFreeList))
    by (unfold q_create_input_facts, q_create_source_binding in PreH5; tauto).
  pose proof (q_create_event_history_private_facts critical sg call.(os_sched_call_invocation)
    initial eid_2 allocation_2 resumed PreH3) as [_ [_ [_ Hresumed_get]]].
  sep_apply_l_atomic (q_create_save_output_observation environment critical
    (QCreatePrivateEvent eid_2 allocation_2) (q_create_buffer start_pre size_pre slots)
    sg resumed_call mask retval resumed).
  Intros returned current.
  rewrite q_create_restore_input_open; unfold q_create_owned; Intros.
  assert (Hinterval : critical_region_interval critical sg resumed_call.(os_sched_call_invocation)
    resumed current) by tauto.
  assert (Hnormal : kernel_call_normal_return resumed_call resumed returned current) by tauto.
  assert (Hcurrent_get : current.(EventState).(eventLifecycle).(eventPrivate) eid_2 =
    Some allocation_2) by tauto.
  assert (Hsame : task_tcb_init_stack_same_call returned call).
  { destruct Hnormal as [Hsecond _]; unfold task_tcb_init_stack_same_call in *; intuition congruence. }
  assert (Hhistory : q_create_event_history critical sg call.(os_sched_call_invocation)
    initial eid_2 allocation_2 current).
  { destruct PreH3 as [Hnest [entry [image [detached [Hvalid [Henter [Hallocate [Hidentity Hprivate]]]]]]]].
    split; [exact Hnest|]; exists entry, image, detached.
    split; [exact Hvalid|]. split; [exact Henter|]. split; [exact Hallocate|]. split; [exact Hidentity|].
    eapply q_create_private_interval_trans; [exact Hprivate|].
    split.
    - destruct PreH1 as [Hinv _]; rewrite <- Hinv; exact Hinterval.
    - exists allocation_2; split; assumption. }
  rewrite UCOS2_inv_split_event_queue.
  unfold queue_storage_rep, store_free_queue_list; Intros free.
  unfold q_create_queue_pool_frame, q_create_masked_control, q_create_private_lookup.
  rewrite Hroot; Exists free allocation_2 current eid_2 returned; entailer!.
Qed.

Lemma proof_of_OSQCreate_entail_wit_6 : OSQCreate_entail_wit_6.
Proof.
  left; intros.
  destruct free as [|qid rest]; [simpl in PreH1; contradiction|].
  assert (Hqid : valid_queue_id sg qid).
  { pose proof (proj2 (proj1 PreH8)) as Hall; inversion Hall; assumption. }
  assert (Hbinding : q_create_source_binding sg)
    by (unfold q_create_input_facts in PreH2; tauto).
  pose proof (proj1 (q_create_qcb_layout sg qid Hbinding Hqid)) as Hptr.
  rewrite store_free_queue_nodes_cons, <- (qcb_free_image_rep sg qid (queue_free_head sg rest)).
  sep_apply_l_atomic (qcb_storage_split_field sg qid (qcb_free_image (queue_free_head sg rest)) QCBPtr).
  Exists rest allocation_2 entry_2 qid eid_2 second_call_2.
  cbn [queue_free_head qcb_cell qcb_free_image qcb_field_offset].
  unfold q_create_free_qcb_without_link; rewrite Hptr; entailer!.
Qed.

Lemma proof_of_OSQCreate_entail_wit_7 : OSQCreate_entail_wit_7.
Proof.
  right; intros.
  pose proof (q_create_event_history_private_facts _ _ _ _ _ _ _ PreH6)
    as [Hnone [Hnopcp [Htype Hget]]].
  assert (Hbinding : q_create_source_binding sg)
    by (unfold q_create_input_facts in PreH1; tauto).
  assert (Hqid : valid_queue_id sg qid).
  { pose proof (proj2 (proj1 PreH8)) as Hall; inversion Hall; assumption. }
  pose proof (proj1 (q_create_qcb_layout sg qid Hbinding Hqid)) as Hptr.
  assert (Hroot : &("OSQFreeList") = sg.(g_OSQFreeList)) by (unfold q_create_source_binding in Hbinding; tauto).
  set (reserved := replace_EventS (queue_reserve_control_block entry.(EventState) eid allocation qid) entry).
  assert (Hreserve : q_create_reserve_critical sg eid (qid :: rest) entry (Some qid) reserved).
  { exists allocation; split; [exact Hget|]; split; reflexivity. }
  assert (Hsuccess : q_create_success_history critical sg call.(os_sched_call_invocation) initial
    eid (queue_allocation_with_qcb allocation qid) qid reserved).
  { exists entry, allocation, (qid :: rest); split; [exact PreH6|].
    split; [exact PreH8|]; split; [exact Hreserve|reflexivity]. }
  pose proof (q_create_reserve_critical_private_result _ _ _ _ _ _ _ Hget Hreserve) as Hreserved_get.
  assert (Hlink_merge : (&((pq) # "os_q" ->ₛ "OSQPtr")) # Ptr |-> queue_free_head sg rest **
    q_create_free_qcb_without_link sg qid (queue_free_head sg rest) |--
    free_queue_node sg qid (queue_free_head sg rest)).
  { rewrite PreH5, Hptr; unfold q_create_free_qcb_without_link.
    sep_apply_r_atomic (proj1 (qcb_free_image_rep sg qid (queue_free_head sg rest))).
    exact (qcb_storage_merge_field sg qid (qcb_free_image (queue_free_head sg rest)) QCBPtr). }
  unfold q_create_queue_pool_frame; Intros.
  assert (Hpublished : queue_published_storage_binding entry.(EventState)) by assumption.
  pose proof (q_create_reserve_merge sg entry eid allocation qid rest
    PreH7 Hpublished PreH8 Hget Hnone Hnopcp) as Hmerge.
  lazymatch goal with |- _ |-- ?Post =>
    assert (Hcut : (free_queue_node sg qid (queue_free_head sg rest) ** UCOS2_inv sg reserved) **
      (q_create_masked_control environment critical sg second_call cpu_sr entry entry **
       event_private_storage_rep sg eid allocation ** q_create_buffer start_pre size_pre slots) |-- Post)
  end.
  {
  unfold q_create_reservation_cut.
  Exists second_call entry reserved eid (queue_allocation_with_qcb allocation qid) qid
    (qcb_free_image (queue_free_head sg rest)).
  rewrite q_create_restore_input_open; cbn [q_create_owned].
  rewrite qcb_free_image_rep.
  unfold q_create_masked_control, event_private_storage_rep; Intros.
  cbn [queue_allocation_with_qcb eventPrivateStorage eventPrivateQueue].
  change (TskState reserved) with (TskState entry); entailer!.
  }
  sep_apply_r_atomic Hcut; sep_apply_r_atomic Hmerge.
  sepcon_assoc_change; sep_apply_r_atomic Hlink_merge; rewrite Hroot; entailer!.
Qed.

Lemma proof_of_OSQCreate_entail_wit_8 : OSQCreate_entail_wit_8.
Proof.
  left; intros; subst pevent pq.
  pose proof (q_create_success_history_properties _ _ _ _ _ _ _ _ PreH5)
    as [Hreserved [Hqid [Hreserved_get Hqueue]]].
  assert (Hbinding : q_create_source_binding sg)
    by (unfold q_create_input_facts in PreH6; tauto).
  assert (Hbounds : q_create_buffer_bounds start_pre size_pre).
  { assert (Hcontract : q_create_buffer_contract critical sg call.(os_sched_call_invocation)
      initial start_pre size_pre) by (unfold q_create_input_facts in PreH6; tauto).
    apply (Hcontract eid_2 qid_2 reserved_2); apply q_create_success_history_prefix with allocation_2;
      exact PreH5. }
  assert (Hlength : Zlength slots = size_pre) by (unfold q_create_input_facts in PreH6; tauto).
  sep_apply_l_atomic (q_create_restore_output_observation environment critical
    (QCreatePrivateQueue eid_2 allocation_2 qid_2 image_2) (q_create_buffer start_pre size_pre slots)
    sg second_call cpu_sr reserved_2).
  Intros returned current.
  assert (Hinterval : critical_region_interval critical sg call.(os_sched_call_invocation) reserved_2 current).
  { destruct PreH1 as [Hi _]; rewrite <- Hi; tauto. }
  assert (Hsame : task_tcb_init_stack_same_call returned call).
  { unfold kernel_call_normal_return, task_tcb_init_stack_same_call in *; intuition congruence. }
  pose proof (proj1 (critical_region_interval_transports_resources _ _ _ _ _ Hinterval Hreserved))
    as Hcurrent.
  assert (Hnames : cfgEventNames (osKernelConfig sg) = false)
    by (pose proof (proj1 Hcurrent) as Hprofile; unfold selected_kernel_profile in Hprofile; tauto).
  pose proof Hcurrent as [_ [_ [_ [[Hpart _] _]]]].
  rewrite q_create_save_input_open; cbn [q_create_owned]; Intros.
  assert (Hget : current.(EventState).(eventLifecycle).(eventPrivate) eid_2 = Some allocation_2) by tauto.
  assert (Hprivate : q_create_private_interval critical sg call.(os_sched_call_invocation) eid_2 reserved_2 current).
  { split; [exact Hinterval|]; exists allocation_2; split; assumption. }
  pose proof (proj1 (event_pool_private_not_free sg current.(EventState) eid_2 allocation_2 Hpart Hget)) as Heid.
  assert (Htable : event_table_layout_prop sg) by (unfold q_create_source_binding in Hbinding; tauto).
  pose proof (Htable eid_2 Heid) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]].
  pose proof (q_create_qcb_layout sg qid_2 Hbinding Hqid)
    as [HQptr [HQstart [HQend [HQin [HQout [HQsize HQentries]]]]]].
  unfold event_private_storage_rep; rewrite Hnames.
  sep_apply_l_atomic (sem_create_initialization_split (event_pool_addr sg eid_2)
    allocation_2.(eventPrivateStorage)).
  sep_apply_l_atomic (q_create_qcb_initialization_split sg qid_2 image_2).
  Exists image_2 allocation_2 reserved_2 qid_2 eid_2.
  unfold q_create_initialization_context; Exists returned current.
  unfold q_create_current_control, q_create_qcb_initialization_pre, sem_create_initialization_pre.
  unfold event_addr, OSEventType_off, OSEventPtr_off, OSEventCnt_off, OSEventGrp_off, OSEventTbl_off
    in Htype, Hptr, Hcnt, Hgrp, Htbl.
  rewrite Htype, Hptr, Hcnt, Hgrp, Htbl, HQstart, HQend, HQin, HQout, HQsize, HQentries.
  replace (event_pool_addr sg eid_2 + 0) with (event_pool_addr sg eid_2) by lia.
  rewrite (proj2 PreH2); entailer!.
Qed.

Lemma proof_of_OSQCreate_entail_wit_9 : OSQCreate_entail_wit_9.
Proof.
  right; intros; subst pevent pq.
  assert (Hbinding : q_create_source_binding sg)
    by (unfold q_create_input_facts in PreH4; tauto).
  unfold q_create_initialization_context; Intros returned current.
  assert (Hsuccess : q_create_success_history critical sg call.(os_sched_call_invocation)
    initial eid allocation qid reserved) by tauto.
  assert (Hprivate : q_create_private_interval critical sg call.(os_sched_call_invocation) eid reserved current) by tauto.
  assert (Hget : current.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation) by tauto.
  assert (Hlength : Zlength slots = size_pre) by tauto.
  pose proof (q_create_success_history_properties _ _ _ _ _ _ _ _ Hsuccess)
    as [Hreserved [Hqid [Hreserved_get Hqueue]]].
  pose proof (proj1 (critical_region_interval_transports_resources _ _ _ _ _ (proj1 Hprivate) Hreserved))
    as Hcurrent.
  assert (Hnames : cfgEventNames (osKernelConfig sg) = false)
    by (pose proof (proj1 Hcurrent) as Hprofile; unfold selected_kernel_profile in Hprofile; tauto).
  pose proof Hcurrent as [_ [_ [_ [[Hpart _] _]]]].
  pose proof (proj1 (event_pool_private_not_free sg current.(EventState) eid allocation Hpart Hget)) as Heid.
  assert (Htable : event_table_layout_prop sg) by (unfold q_create_source_binding in Hbinding; tauto).
  pose proof (Htable eid Heid) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]].
  pose proof (q_create_qcb_layout sg qid Hbinding Hqid)
    as [HQptr [HQstart [HQend [HQin [HQout [HQsize HQentries]]]]]].
  unfold event_addr, OSEventType_off, OSEventPtr_off, OSEventCnt_off, OSEventGrp_off, OSEventTbl_off
    in Htype, Hptr, Hcnt, Hgrp, Htbl.
  rewrite Htype, Hptr, Hcnt, Hgrp, Htbl, HQstart, HQend, HQin, HQout, HQsize, HQentries.
  replace (event_pool_addr sg eid + 0) with (event_pool_addr sg eid) by lia.
  change (sizeof(PTR)) with 4.
  pose proof (q_create_event_initialization_merge (event_pool_addr sg eid)
    allocation.(eventPrivateStorage) (qcb_addr sg qid)) as Hevent_merge.
  unfold q_create_event_initialization_post in Hevent_merge.
  sep_apply_l_atomic Hevent_merge.
  pose proof (q_create_qcb_initialization_merge sg qid image start_pre size_pre) as Hqueue_merge.
  unfold q_create_qcb_initialization_post in Hqueue_merge.
  sep_apply_l_atomic Hqueue_merge.
  set (writes := event_create_initialization_fields false 2 0 (qcb_addr sg qid) 0).
  destruct (event_create_private_stores_exists eid writes current allocation Hget) as [initialized Hstores].
  destruct (event_create_private_stores_post_allocation eid writes current tt initialized allocation Hget Hstores)
    as [final [Hfinal [Hinv [Hgen [Hfinal_queue Himage]]]]].
  unfold writes in Himage; rewrite event_create_stores_image_initialization_eq in Himage.
  assert (Hinterleaved : q_create_private_stores_interleaved critical sg call.(os_sched_call_invocation)
    eid (event_create_initialization_fields sg.(osKernelConfig).(cfgEventNames) 2 0 (qcb_addr sg qid) 0)
    reserved tt initialized).
  { rewrite Hnames; eapply q_create_private_stores_interval_prefix; [exact Hprivate|].
    eapply q_create_private_stores_without_interference; eassumption. }
  assert (Hstorage : event_storage_rep false (event_pool_addr sg eid)
    (event_create_image false 2 0 (qcb_addr sg qid) 0 allocation.(eventPrivateStorage)) |--
    event_private_storage_rep sg eid final).
  { unfold event_private_storage_rep; rewrite Hnames, Himage; reflexivity. }
  sep_apply_l_atomic Hstorage.
  sep_apply_l_atomic (sem_create_private_stores_global_frame sg eid writes current tt initialized Hstores).
  pose proof (event_create_private_stores_published_frame eid writes current tt initialized Hstores)
    as [_ [_ [Htasks _]]].
  assert (Hcontrol : q_create_current_control environment sg returned mask current =
    q_create_current_control environment sg returned mask initialized).
  { unfold q_create_current_control; rewrite Htasks; reflexivity. }
  rewrite Hcontrol, UCOS2_inv_split_event_queue; unfold queue_storage_rep; Intros free.
  assert (Hpublication : queue_pool_partition sg initialized.(EventState) free) by assumption.
  assert (Hpublished : queue_published_storage_binding initialized.(EventState)) by assumption.
  assert (Hname : event_name_valid sg initialized.(NameState)
    (q_create_initialized_event final qid start_pre size_pre 0))
    by (apply event_name_valid_disabled; exact Hnames).
  set (published := replace_EventS (queue_publish initialized.(EventState) eid
    (q_create_initialized_event final qid start_pre size_pre 0) qid slots) initialized).
  assert (Hprogram : q_create_program critical sg call.(os_sched_call_invocation)
    start_pre size_pre slots initial (event_pool_addr sg eid) published).
  { destruct Hsuccess as [resumed [original [old_free [Hhistory [Hpool [Hreserve Hidentity]]]]]].
    destruct Hhistory as [Hnest [entry [old_image [detached [Hvalid [Henter [Hallocate [Horig Hinterval]]]]]]]].
    eapply q_create_program_published_return; eassumption. }
  assert (Hreturn : q_create_return_safe published (event_pool_addr sg eid) X).
  { eapply (q_create_api_safe_return critical sg call.(os_sched_call_invocation)
      start_pre size_pre slots initial published (event_pool_addr sg eid) X); [exact Hprogram|].
    unfold q_create_input_facts in PreH4; tauto. }
  assert (Hstart : 0 < start_pre) by (unfold q_create_buffer_bounds in PreH1; tauto).
  assert (Hsize : 0 <= size_pre <= 65535) by (unfold q_create_buffer_bounds in PreH1; tauto).
  pose proof (q_create_interleaved_publish_merge critical sg call.(os_sched_call_invocation)
    reserved initialized free eid allocation final qid image start_pre size_pre slots 0
    Hreserved Hreserved_get Hqueue Hinterleaved Hfinal Hpublished Hpublication Hstart Hsize Hlength Hname) as Hmerge.
  lazymatch goal with |- _ |-- ?Post =>
    assert (Hcut : UCOS2_inv sg published ** q_create_current_control environment sg returned mask initialized |-- Post)
  end.
  {
  assert (Hpositive : 0 < event_pool_addr sg eid).
  { destruct Hbinding as [[_ [_ [_ Hlayout]]] _]; exact (proj1 (proj1 (Hlayout eid Heid))). }
  unfold q_create_call_post; Exists returned published.
  unfold q_create_result_buffer; destruct (Z.eq_dec (event_pool_addr sg eid) 0); [lia|].
  rewrite q_create_save_input_open.
  unfold q_create_current_control, q_create_owned; Intros.
  change (TskState published) with (TskState initialized); entailer!.
  }
  sep_apply_r_atomic Hcut; sep_apply_r_atomic Hmerge; unfold q_create_buffer; entailer!.
Qed.

Lemma proof_of_OSQCreate_entail_wit_10 : OSQCreate_entail_wit_10.
Proof.
  left; intros.
  pose proof (proj1 (q_create_queue_head_null_iff sg entry_2 free PreH7 PreH8) PreH1) as Hempty.
  subst free pevent.
  assert (Hbinding : sem_create_source_binding sg)
    by (unfold q_create_input_facts, q_create_source_binding in PreH2; tauto).
  pose proof PreH7 as [_ [_ [_ [[Hpart _] _]]]].
  pose proof (proj1 (event_pool_private_not_free sg entry_2.(EventState) eid_2 allocation_2 Hpart PreH9)) as Hrange.
  pose proof (proj2 (proj2 (proj2 Hbinding)) eid_2 Hrange) as [_ Hptr].
  pose proof (proj1 (proj2 Hbinding)) as Hroot.
  assert (HQroot : &("OSQFreeList") = sg.(g_OSQFreeList))
    by (unfold q_create_input_facts, q_create_source_binding in PreH2; tauto).
  unfold q_create_queue_pool_frame, event_private_storage_rep; Intros.
  sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
    (event_pool_addr sg eid_2) allocation_2.(eventPrivateStorage) EventPtrField
    ltac:(unfold event_fields; simpl; tauto)).
  Exists allocation_2 entry_2 eid_2 second_call_2.
  unfold q_create_rollback_frame, queue_storage_rep, store_free_queue_list; Exists (@nil QueueID).
  unfold event_raw_rep, event_free_root_rep, sem_create_pool_head, event_cell, event_field_offset.
  unfold sem_create_link_addr in Hptr; rewrite Hptr, Hroot, HQroot.
  destruct (eventPrivateStorage allocation_2 EventPtrField) as [ptr|].
  - sep_apply_l_atomic (store_ptr_undef_store_ptr (event_pool_addr sg eid_2 + 4) ptr); entailer!.
  - entailer!.
Qed.

Lemma proof_of_OSQCreate_entail_wit_11 : OSQCreate_entail_wit_11.
Proof.
  right; intros; subst pevent.
  pose proof (q_create_event_history_private_facts _ _ _ _ _ _ _ PreH6)
    as [Hnone [Hnopcp [Htype Hget]]].
  assert (Hbinding : sem_create_source_binding sg)
    by (unfold q_create_input_facts, q_create_source_binding in PreH1; tauto).
  pose proof PreH7 as [_ [_ [_ [[Hpart _] _]]]].
  pose proof (proj1 (event_pool_private_not_free sg entry.(EventState) eid allocation Hpart Hget)) as Hrange.
  pose proof (proj2 (proj2 (proj2 Hbinding)) eid Hrange) as [_ Hptr].
  pose proof (proj1 (proj2 Hbinding)) as Hroot.
  set (rolled_back := replace_EventS (event_rollback sg entry.(EventState) eid allocation) entry).
  assert (Hreserve : q_create_reserve_critical sg eid [] entry None rolled_back).
  { exists allocation; split; [exact Hget|]; split; reflexivity. }
  assert (Hhistory : q_create_error_history critical sg call.(os_sched_call_invocation) initial rolled_back).
  { destruct PreH6 as [Hnest [first [image [detached [Hvalid [Henter [Hallocate [Hidentity Hprivate]]]]]]]].
    split; [exact Hnest|]; exists first, (Some (eid, image)), detached.
    split; [exact Henter|]; split; [exact Hallocate|].
    exists entry, [], rolled_back; split; [exact Hprivate|].
    split; [exact PreH8|]. split; [exact Hreserve|constructor]. }
  pose proof (q_create_rollback_merge sg entry eid allocation PreH7 Hget Hnone Htype Hnopcp) as Hmerge.
  unfold q_create_rollback_frame, sem_create_pool_head.
  unfold sem_create_link_addr in Hptr; rewrite Hptr, Hroot.
  lazymatch goal with |- _ |-- ?Post =>
    assert (Hcut : UCOS2_inv sg rolled_back **
      (q_create_masked_control environment critical sg second_call cpu_sr entry entry **
       q_create_buffer start_pre size_pre slots) |-- Post)
  end.
  {
  unfold q_create_rollback_cut; Exists second_call entry rolled_back.
  rewrite q_create_restore_input_open.
  unfold q_create_masked_control, q_create_owned; Intros.
  change (TskState rolled_back) with (TskState entry); entailer!.
  }
  sep_apply_r_atomic Hcut; sep_apply_r_atomic Hmerge; unfold event_cell, event_field_offset; entailer!.
Qed.

Lemma proof_of_OSQCreate_entail_wit_12 : OSQCreate_entail_wit_12.
Proof.
  right; intros.
  sep_apply_l_atomic (q_create_restore_output_observation environment critical QCreateNoPrivate
    (q_create_buffer start_pre size_pre slots) sg second_call cpu_sr rolled_back).
  Intros returned current.
  assert (Hinterval : critical_region_interval critical sg call.(os_sched_call_invocation)
    rolled_back current).
  { destruct PreH1 as [Hi _]; rewrite <- Hi; tauto. }
  assert (Hhistory : q_create_error_history critical sg call.(os_sched_call_invocation) initial current)
    by (eapply q_create_error_history_extend; eassumption).
  assert (Hreturn : q_create_return_safe current 0 X).
  { eapply (q_create_api_safe_return critical sg call.(os_sched_call_invocation)
      start_pre size_pre slots initial current 0 X).
    - eapply q_create_error_history_program; exact Hhistory.
    - unfold q_create_input_facts in PreH4; tauto. }
  assert (Hsame : task_tcb_init_stack_same_call returned call).
  { unfold kernel_call_normal_return, task_tcb_init_stack_same_call in *; intuition congruence. }
  unfold q_create_call_post; Exists returned current.
  unfold q_create_result_buffer; destruct (Z.eq_dec 0 0); [|contradiction].
  rewrite (proj2 PreH2); entailer!.
Qed.

Lemma proof_of_OSQCreate_entail_wit_13_3 : OSQCreate_entail_wit_13_3.
Proof.
  right; intros; subst pevent.
  unfold q_create_allocation_return; Intros returned current.
  destruct (Z.eq_dec 0 0); [|contradiction]; Intros.
  assert (Hreturn : q_create_return_safe current 0 X).
  { eapply (q_create_api_safe_return critical sg call.(os_sched_call_invocation)
      start_pre size_pre slots initial current 0 X).
    - eapply q_create_error_history_program; eassumption.
    - unfold q_create_input_facts in PreH2; tauto. }
  unfold q_create_call_post; Exists returned current.
  unfold q_create_result_buffer; destruct (Z.eq_dec 0 0); [|contradiction]; entailer!.
Qed.

Lemma proof_of_OSQCreate_return_wit_2 : OSQCreate_return_wit_2.
Proof.
  left; intros; apply q_create_isr_return; lia.
Qed.

Lemma proof_of_OSQCreate_which_implies_wit_1 : OSQCreate_which_implies_wit_1.
Proof.
  left; intros; unfold q_create_call_pre; Intros.
  assert (Hbinding : q_create_source_binding sg)
    by (unfold q_create_input_facts in *; tauto).
  rewrite (q_create_save_input_split_nesting _ _ _ _ _ _ _ _ Hbinding).
  prop_apply_p (store_uchar_range (&("OSIntNesting")) initial.(IntrState).(intNesting)).
  entailer!.
Qed.

Lemma proof_of_OSQCreate_which_implies_wit_2 : OSQCreate_which_implies_wit_2.
Proof.
  left; intros.
  assert (Hbinding : q_create_source_binding sg)
    by (unfold q_create_input_facts in *; tauto).
  unfold q_create_call_pre.
  rewrite (q_create_save_input_split_nesting _ _ _ _ _ _ _ _ Hbinding).
  entailer!.
Qed.

Lemma proof_of_OSQCreate_which_implies_wit_3 : OSQCreate_which_implies_wit_3.
Proof.
  left; intros.
  assert (Hbinding : q_create_source_binding sg)
    by (unfold q_create_input_facts in *; tauto).
  rewrite (q_create_save_input_split_nesting _ _ _ _ _ _ _ _ Hbinding).
  entailer!.
Qed.

Lemma proof_of_OSQCreate_which_implies_wit_4 : OSQCreate_which_implies_wit_4.
Proof.
  left; intros; unfold q_create_allocation_cut; Intros returned entry result allocated.
  Exists result allocated returned entry; entailer!.
Qed.

Lemma proof_of_OSQCreate_which_implies_wit_5 : OSQCreate_which_implies_wit_5.
Proof.
  left; intros; unfold q_create_allocation_return; Intros returned current.
  destruct (Z.eq_dec pevent 0); [contradiction|].
  Intros eid allocation; Exists allocation current eid returned; entailer!.
Qed.

Lemma proof_of_OSQCreate_which_implies_wit_6 : OSQCreate_which_implies_wit_6.
Proof.
  left; intros; unfold q_create_reservation_cut.
  Intros returned acquired reserved eid allocation qid image.
  Exists image acquired allocation reserved qid eid returned; entailer!.
Qed.

Lemma proof_of_OSQCreate_which_implies_wit_7 : OSQCreate_which_implies_wit_7.
Proof.
  left; intros; unfold q_create_buffer_bounds in *; entailer!;
    simpl; change Arch32.ptr_size_Z with 4; lia.
Qed.

Lemma proof_of_OSQCreate_which_implies_wit_8 : OSQCreate_which_implies_wit_8.
Proof.
  left; intros; unfold q_create_rollback_cut; Intros returned acquired rolled_back.
  Exists acquired rolled_back returned; entailer!.
Qed.
