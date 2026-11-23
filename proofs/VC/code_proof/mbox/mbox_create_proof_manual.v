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
From Ucos2Verify.VC.code.mbox Require Import mbox_create_goal.
From Ucos2Verify.VC.code.mbox Require Import mbox_create_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_create_api_spec.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.event_pool Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSMboxCreate_entail_wit_1 : OSMboxCreate_entail_wit_1.
Proof.
  left; intros.
  assert (Hbinding : sem_create_source_binding sg)
    by (unfold mbox_create_input_facts, mbox_create_source_binding in *; tauto).
  sep_apply_l_atomic (q_create_save_output_observation environment critical
    QCreateNoPrivate mbox_create_call_frame sg call mask retval initial).
  Intros returned current.
  rewrite q_create_restore_input_open.
  unfold q_create_owned, mbox_create_call_frame.
  rewrite (sem_create_pool_split_head sg current Hbinding).
  Intros.
  Exists returned current.
  unfold q_create_first_facts, q_create_masked_control.
  unfold kernel_call_normal_return in *.
  entailer!.
Qed.

Lemma proof_of_OSMboxCreate_entail_wit_2 : OSMboxCreate_entail_wit_2.
Proof.
  left; intros.
  assert (Hbinding : sem_create_source_binding sg)
    by (unfold mbox_create_input_facts, mbox_create_source_binding in *; tauto).
  assert (Hvalid : UCOS2_state_inv sg entry)
    by (unfold q_create_first_facts in *; tauto).
  destruct (unUsedEventStates (EventState entry)) as [|eid rest] eqn:Hhead.
  - exfalso; apply PreH1; unfold sem_create_pool_head; rewrite Hhead; reflexivity.
  - destruct (sem_create_pool_nonempty_facts sg entry eid rest Hvalid Hhead)
      as [Hrange [image [Himage Hnext]]].
    sep_apply_l_atomic (sem_create_pool_split_node sg entry eid rest image
      Hbinding Hvalid Hhead Himage).
    assert (Hpointer : sem_create_pool_head sg entry = event_pool_addr sg eid)
      by (unfold sem_create_pool_head; rewrite Hhead; reflexivity).
    Exists eid rest image first_call_2 entry.
    unfold sem_create_head_facts, sem_create_link_addr.
    rewrite Hpointer; entailer!.
Qed.

Lemma proof_of_OSMboxCreate_entail_wit_3_1 : OSMboxCreate_entail_wit_3_1.
Proof.
  left; intros.
  assert (Hbinding : sem_create_source_binding sg)
    by (unfold mbox_create_input_facts, mbox_create_source_binding in *; tauto).
  assert (Hvalid : UCOS2_state_inv sg entry)
    by (unfold q_create_first_facts in *; tauto).
  destruct PreH3 as [Hhead Himage].
  assert (Hallocate : event_create_allocate_critical entry (Some (eid, image))
    (replace_EventS (event_detach_head (EventState entry) eid rest image) entry)).
  { unfold event_create_allocate_critical; rewrite Hhead.
    exists image; repeat split; assumption || reflexivity. }
  pose proof (sem_create_allocation_facts_private sg entry _ eid image
    (conj Hvalid Hallocate)) as [Hallocated Hprivate].
  assert (Hnames : cfgEventNames (osKernelConfig sg) = false).
  { destruct Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
  subst pevent.
  pose proof (sem_create_pool_merge_detached_node sg entry eid rest image
    Hbinding Hvalid Hhead Himage) as Hmerge.
  unfold sem_create_link_addr in Hmerge.
  assert (Hmerge_grouped :
    ((&("OSEventFreeList") # Ptr |-> event_encode_pool_link sg (hd_error rest)) **
     (sem_create_link_addr (event_pool_addr sg eid) # Ptr |->
       event_encode_pool_link sg (hd_error rest))) **
    sem_create_node_frame sg entry eid image |--
    event_storage_rep false (event_pool_addr sg eid) image **
    UCOS2_inv sg (replace_EventS (event_detach_head (EventState entry) eid rest image) entry)).
  { sepcon_assoc_change; exact Hmerge. }
  unfold sem_create_link_addr in Hmerge_grouped.
  sep_apply_l_atomic Hmerge_grouped.
  unfold mbox_create_allocation_cut.
  Exists first_call entry (Some (eid, image))
    (replace_EventS (event_detach_head (EventState entry) eid rest image) entry).
  rewrite q_create_restore_input_open.
  unfold q_create_allocated_owner, q_create_owned, event_private_storage_rep.
  rewrite Hnames.
  unfold q_create_masked_control; Intros.
  cbn [replace_EventS sem_create_allocation_identity eventPrivateStorage TskState].
  entailer!.
Qed.

Lemma proof_of_OSMboxCreate_entail_wit_3_2 : OSMboxCreate_entail_wit_3_2.
Proof.
  left; intros.
  assert (Hbinding : sem_create_source_binding sg)
    by (unfold mbox_create_input_facts, mbox_create_source_binding in *; tauto).
  assert (Hvalid : UCOS2_state_inv sg entry)
    by (unfold q_create_first_facts in *; tauto).
  pose proof (proj1 (sem_create_pool_head_null_iff sg entry Hbinding Hvalid) PreH1)
    as Hempty.
  assert (Hallocate : event_create_allocate_critical entry None entry).
  { unfold event_create_allocate_critical; rewrite Hempty; split; reflexivity. }
  unfold mbox_create_allocation_cut.
  Exists first_call entry (@None (Z * EventStorage)) entry.
  rewrite q_create_restore_input_open, (sem_create_pool_split_head sg entry Hbinding).
  unfold q_create_allocated_owner, q_create_owned, q_create_masked_control.
  Intros; entailer!.
Qed.

Lemma proof_of_OSMboxCreate_entail_wit_4 : OSMboxCreate_entail_wit_4.
Proof.
  left; intros.
  assert (Hsource : mbox_create_source_binding sg) by exact (proj1 PreH4).
  assert (Hsaved : interrupt_saved_value mask cpu_sr).
  { unfold q_create_first_facts in PreH1; tauto. }
  sep_apply_l_atomic (mbox_create_allocation_restore environment critical sg call initial
    mask cpu_sr first_call entry allocated allocation_result pevent
    Hsource PreH1 PreH2 PreH3).
  entailer!.
Qed.

Lemma proof_of_OSMboxCreate_entail_wit_5 : OSMboxCreate_entail_wit_5.
Proof.
  left; intros; subst pevent.
  unfold mbox_create_initialization_context at 1; Intros returned.
  assert (Hhistory : q_create_event_history critical sg call.(os_sched_call_invocation)
    initial eid allocation current) by tauto.
  assert (Hrange : valid_event_id sg eid).
  { destruct Hhistory as [_ [entry [image [detached
      [Hvalid [Henter [Hpop Htail]]]]]]].
    apply (sem_create_allocated_id_valid sg entry detached eid image); split; assumption. }
  assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false).
  { destruct Hhistory as [_ [entry [image [detached [[Hprofile Hvalid] Htail]]]]].
    unfold selected_kernel_profile in Hprofile; tauto. }
  assert (Hlayout : event_object_layout_prop sg eid).
  { apply event_table_layout_select; [exact (proj2 (proj1 PreH2))|exact Hrange]. }
  pose proof (mbox_create_storage_merge_initialization_layout sg eid
    allocation.(eventPrivateStorage) pmsg_pre Hnames Hlayout) as Hmerge.
  rewrite Hnames in Hmerge.
  unfold event_addr in Hmerge.
  sep_apply_l_atomic Hmerge.
  sep_apply_r_atomic (mbox_create_initialized_return environment critical sg call initial
    mask eid allocation current pmsg_pre X PreH2).
  unfold mbox_create_initialization_context; Exists returned.
  sep_apply store_uint_undef_store_uint.
  entailer!.
Qed.

Lemma proof_of_OSMboxCreate_entail_wit_6_2 : OSMboxCreate_entail_wit_6_2.
Proof.
  left; intros; subst pevent.
  sep_apply_l_atomic (mbox_create_exhausted_return environment critical sg call initial
    mask pmsg_pre X PreH2).
  sep_apply store_uint_undef_store_uint.
  entailer!.
Qed.

Lemma proof_of_OSMboxCreate_return_wit_2 : OSMboxCreate_return_wit_2.
Proof.
  left; intros.
  apply mbox_create_isr_return; lia.
Qed.

Lemma proof_of_OSMboxCreate_which_implies_wit_1 : OSMboxCreate_which_implies_wit_1.
Proof.
  left; intros.
  unfold mbox_create_call_pre; Intros.
  assert (Hbinding : mbox_create_source_binding sg)
    by (unfold mbox_create_input_facts in *; tauto).
  rewrite (mbox_create_save_input_split_nesting environment critical
    QCreateNoPrivate emp sg call mask initial Hbinding).
  unfold mbox_create_call_frame.
  prop_apply (store_uchar_range (&("OSIntNesting")) (intNesting (IntrState initial))).
  Intros; entailer!; simpl in *; lia.
Qed.

Lemma proof_of_OSMboxCreate_which_implies_wit_2 : OSMboxCreate_which_implies_wit_2.
Proof.
  left; intros.
  assert (Hbinding : mbox_create_source_binding sg)
    by (unfold mbox_create_input_facts in *; tauto).
  unfold mbox_create_call_pre, mbox_create_call_frame.
  rewrite (mbox_create_save_input_split_nesting environment critical
    QCreateNoPrivate emp sg call mask initial Hbinding).
  entailer!.
Qed.

Lemma proof_of_OSMboxCreate_which_implies_wit_3 : OSMboxCreate_which_implies_wit_3.
Proof.
  left; intros.
  assert (Hbinding : mbox_create_source_binding sg)
    by (unfold mbox_create_input_facts in *; tauto).
  rewrite (mbox_create_save_input_split_nesting environment critical
    QCreateNoPrivate mbox_create_call_frame sg call mask initial Hbinding).
  entailer!.
Qed.

Lemma proof_of_OSMboxCreate_which_implies_wit_4 : OSMboxCreate_which_implies_wit_4.
Proof.
  left; intros.
  unfold mbox_create_allocation_cut; Intros first_call entry result allocated.
  Exists result allocated first_call entry.
  unfold mbox_create_call_frame; entailer!.
Qed.

Lemma proof_of_OSMboxCreate_which_implies_wit_5 : OSMboxCreate_which_implies_wit_5.
Proof.
  left; intros.
  sep_apply_l_atomic (mbox_create_nonnull_initialization environment critical sg call initial
    mask pevent (proj1 PreH1) PreH2).
  Intros eid allocation current.
  Exists allocation current eid.
  entailer!.
Qed.

