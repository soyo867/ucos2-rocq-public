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
From Ucos2Verify.VC.code.sem Require Import create_goal.
From Ucos2Verify.VC.code.sem Require Import create_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_api_spec.
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

Lemma proof_of_OSSemCreate_entail_wit_1 : OSSemCreate_entail_wit_1.
Proof.
  unfold OSSemCreate_entail_wit_1; left.
  intros cnt X initial mask call sg critical environment saved Hinput Hnest Hinput' Hlower Hupper.
  assert (Hsource : sem_create_source_binding sg)
    by (unfold sem_create_api_input_facts, mbox_create_source_binding in Hinput; tauto).
  sep_apply_l_atomic (q_create_save_output_observation environment critical
    QCreateNoPrivate mbox_create_call_frame sg call mask saved initial).
  Intros first entry.
  rewrite q_create_restore_input_open.
  unfold q_create_owned, mbox_create_call_frame.
  rewrite (sem_create_pool_split_head sg entry Hsource).
  Intros.
  assert (Hfirst : q_create_first_facts critical sg call initial mask saved first entry).
  { unfold q_create_first_facts, kernel_call_normal_return in *; tauto. }
  Exists first entry.
  unfold q_create_masked_control; entailer!.
Qed.

Lemma proof_of_OSSemCreate_entail_wit_2 : OSSemCreate_entail_wit_2.
Proof.
  unfold OSSemCreate_entail_wit_2; left.
  intros cnt X initial mask call sg critical environment first entry saved Hnonnull Hinput Hfirst.
  assert (Hsource : sem_create_source_binding sg)
    by (unfold sem_create_api_input_facts, mbox_create_source_binding in Hinput; tauto).
  assert (Hvalid : UCOS2_state_inv sg entry)
    by (unfold q_create_first_facts in Hfirst; tauto).
  destruct entry.(EventState).(unUsedEventStates) as [|eid rest] eqn:Hhead.
  - exfalso; apply Hnonnull; unfold sem_create_pool_head; rewrite Hhead; reflexivity.
  - destruct (sem_create_pool_nonempty_facts sg entry eid rest Hvalid Hhead)
      as [Hrange [image [Himage Hlink]]].
    assert (Hpointer : sem_create_pool_head sg entry = event_pool_addr sg eid)
      by (unfold sem_create_pool_head; rewrite Hhead; reflexivity).
    Exists eid rest image first entry.
    rewrite Hpointer.
    sep_apply_l_atomic (sem_create_pool_split_node sg entry eid rest image
      Hsource Hvalid Hhead Himage).
    unfold sem_create_link_addr, sem_create_head_facts; entailer!.
Qed.

Lemma proof_of_OSSemCreate_entail_wit_3_1 : OSSemCreate_entail_wit_3_1.
Proof.
  unfold OSSemCreate_entail_wit_3_1; left.
  intros cnt X initial mask call sg critical environment first entry eid rest image saved pointer
    Hinput Hfirst [Hhead Himage] Hpointer; subst pointer.
  assert (Hsource : sem_create_source_binding sg)
    by (unfold sem_create_api_input_facts, mbox_create_source_binding in Hinput; tauto).
  assert (Hvalid : UCOS2_state_inv sg entry)
    by (unfold q_create_first_facts in Hfirst; tauto).
  set (detached := replace_EventS (event_detach_head entry.(EventState) eid rest image) entry).
  assert (Hstep : event_create_allocate_critical entry (Some (eid, image)) detached).
  { unfold event_create_allocate_critical; rewrite Hhead.
    exists image; repeat split; assumption || reflexivity. }
  pose proof (event_create_allocate_critical_task_frame entry _ detached Hstep) as Htasks.
  pose proof (proj2 (event_create_allocate_critical_private_result entry eid image detached Hstep))
    as Hprivate.
  assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false).
  { destruct Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
  pose proof (sem_create_pool_merge_detached_node sg entry eid rest image
    Hsource Hvalid Hhead Himage) as Hmerge.
  unfold sem_create_link_addr in Hmerge.
  sepcon_assoc_change.
  rewrite Hmerge.
  fold detached.
  unfold mbox_create_allocation_cut.
  Exists first entry (Some (eid, image)) detached.
  rewrite q_create_restore_input_open.
  cbn [q_create_allocated_owner].
  unfold q_create_owned, q_create_masked_control, event_private_storage_rep,
    sem_create_allocation_identity.
  rewrite Hnames, Htasks.
  cbn [eventPrivateStorage].
  entailer!.
Qed.

Lemma proof_of_OSSemCreate_entail_wit_3_2 : OSSemCreate_entail_wit_3_2.
Proof.
  unfold OSSemCreate_entail_wit_3_2; left.
  intros cnt X initial mask call sg critical environment first entry saved Hnull Hinput Hfirst.
  assert (Hsource : sem_create_source_binding sg)
    by (unfold sem_create_api_input_facts, mbox_create_source_binding in Hinput; tauto).
  assert (Hvalid : UCOS2_state_inv sg entry)
    by (unfold q_create_first_facts in Hfirst; tauto).
  pose proof (proj1 (sem_create_pool_head_null_iff sg entry Hsource Hvalid) Hnull) as Hempty.
  assert (Hstep : event_create_allocate_critical entry None entry).
  { unfold event_create_allocate_critical; rewrite Hempty; split; reflexivity. }
  unfold mbox_create_allocation_cut.
  Exists first entry (@None (EventID * EventStorage)) entry.
  rewrite q_create_restore_input_open, (sem_create_pool_split_head sg entry Hsource).
  unfold q_create_allocated_owner, q_create_owned, q_create_masked_control.
  cbn [event_create_return_ptr].
  entailer!.
Qed.

Lemma proof_of_OSSemCreate_entail_wit_4 : OSSemCreate_entail_wit_4.
Proof.
  unfold OSSemCreate_entail_wit_4; left.
  intros cnt X initial mask call sg critical environment pointer saved result allocated first entry
    Hfirst Hstep Hpointer Hinput.
  assert (Hsource : mbox_create_source_binding sg)
    by (unfold sem_create_api_input_facts in Hinput; tauto).
  assert (Hsaved : interrupt_saved_value mask saved)
    by (unfold q_create_first_facts in Hfirst; tauto).
  unfold mbox_create_call_frame.
  sep_apply_l_atomic (mbox_create_allocation_restore environment critical sg call initial
    mask saved first entry allocated result pointer Hsource Hfirst Hstep Hpointer).
  entailer!.
Qed.

Lemma proof_of_OSSemCreate_entail_wit_5 : OSSemCreate_entail_wit_5.
Proof.
  left; intros cnt_pre X initial mask call sg critical environment cpu_sr
    pevent allocation current eid Hpointer Hinput Hnonnull Hinput' Hsaved.
  subst pevent.
  sep_apply_r_atomic (sem_create_api_initialized_return environment critical sg
    call initial mask eid allocation current cnt_pre X Hinput).
  unfold mbox_create_initialization_context at 1; Intros returned.
  assert (Hhistory : q_create_event_history critical sg call.(os_sched_call_invocation)
    initial eid allocation current) by tauto.
  assert (Hrange : valid_event_id sg eid).
  { destruct Hhistory as [_ [entry [image [detached
      [Hvalid [Henter [Hpop Htail]]]]]]].
    apply (sem_create_allocated_id_valid sg entry detached eid image).
    split; assumption. }
  assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false).
  { destruct Hhistory as [_ [entry [image [detached [[Hprofile Hvalid] Htail]]]]].
    unfold selected_kernel_profile in Hprofile; tauto. }
  assert (Htable : event_table_layout_prop sg)
    by (unfold sem_create_api_input_facts, mbox_create_source_binding in Hinput; tauto).
  pose proof (sem_create_api_storage_merge_initialization_layout sg eid
    allocation.(eventPrivateStorage) cnt_pre Hnames
    (event_table_layout_select sg eid Htable Hrange)) as Hmerge.
  rewrite Hnames in Hmerge.
  unfold event_addr in Hmerge.
  sep_apply Hmerge.
  unfold mbox_create_initialization_context; Exists returned.
  sep_apply store_uint_undef_store_uint.
  entailer!.
Qed.

Lemma proof_of_OSSemCreate_entail_wit_6_2 : OSSemCreate_entail_wit_6_2.
Proof.
  left; intros cnt_pre X initial mask call sg critical environment cpu_sr pevent
    Hpointer Hinput Hsaved; subst pevent.
  sep_apply_l_atomic (sem_create_api_exhausted_return environment critical sg
    call initial mask cnt_pre X Hinput).
  sep_apply store_uint_undef_store_uint; entailer!.
Qed.

Lemma proof_of_OSSemCreate_return_wit_2 : OSSemCreate_return_wit_2.
Proof.
  left; intros.
  apply sem_create_api_isr_return; lia.
Qed.

Lemma proof_of_OSSemCreate_which_implies_wit_1 : OSSemCreate_which_implies_wit_1.
Proof.
  left; intros cnt_pre X initial mask call sg critical environment.
  unfold sem_create_api_call_pre; Intros.
  assert (Hsource : mbox_create_source_binding sg)
    by (unfold sem_create_api_input_facts in *; tauto).
  rewrite (mbox_create_save_input_split_nesting environment critical
    QCreateNoPrivate emp sg call mask initial Hsource).
  prop_apply store_uchar_range; Intros.
  unfold mbox_create_call_frame; entailer!.
Qed.

Lemma proof_of_OSSemCreate_which_implies_wit_2 : OSSemCreate_which_implies_wit_2.
Proof.
  left; intros cnt_pre X initial mask call sg critical environment Hinput.
  unfold sem_create_api_call_pre.
  rewrite (mbox_create_save_input_split_nesting environment critical
    QCreateNoPrivate emp sg call mask initial (proj1 Hinput)).
  unfold mbox_create_call_frame; entailer!.
Qed.

Lemma proof_of_OSSemCreate_which_implies_wit_3 : OSSemCreate_which_implies_wit_3.
Proof.
  left; intros cnt_pre X initial mask call sg critical environment Hinput.
  rewrite (mbox_create_save_input_split_nesting environment critical
    QCreateNoPrivate mbox_create_call_frame sg call mask initial (proj1 Hinput)).
  entailer!.
Qed.

Lemma proof_of_OSSemCreate_which_implies_wit_4 : OSSemCreate_which_implies_wit_4.
Proof.
  unfold OSSemCreate_which_implies_wit_4; left; intros.
  unfold mbox_create_allocation_cut; Intros first entry result allocated.
  Exists result allocated first entry.
  unfold mbox_create_call_frame; entailer!.
Qed.

Lemma proof_of_OSSemCreate_which_implies_wit_5 : OSSemCreate_which_implies_wit_5.
Proof.
  left; intros cnt_pre X initial mask call sg critical environment pevent Hinput Hnonnull.
  sep_apply_l_atomic (mbox_create_nonnull_initialization environment critical sg
    call initial mask pevent (proj1 Hinput) Hnonnull).
  Intros eid allocation current.
  Exists allocation current eid; entailer!.
Qed.

