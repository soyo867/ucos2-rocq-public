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
From Ucos2Verify.VC.code.queue Require Import q_del_goal.
From Ucos2Verify.VC.code.queue Require Import q_del_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.queue.spec.q_del_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSQDel_entail_wit_1 : OSQDel_entail_wit_1.
Proof.
  left; intros; poly_store_unfold.
  unfold UCOS2_C_Rules.store_uchar, UCOS2_Base_Rules.store_uchar; Intros; entailer!.
Qed.

Lemma proof_of_OSQDel_entail_wit_2 : OSQDel_entail_wit_2.
Proof.
  left; intros; poly_store_unfold.
  unfold UCOS2_C_Rules.store_uchar, UCOS2_Base_Rules.store_uchar; Intros; entailer!.
Qed.

Lemma proof_of_OSQDel_entail_wit_3_1 : OSQDel_entail_wit_3_1.
Proof.
  left; intros; poly_store_unfold.
  subst pe opt_pre.
  assert (Hgroup : q_post_group acquired_2 initial_2 <> 0).
  { intro Hzero; rewrite Hzero in PreH1; vm_compute in PreH1; contradiction. }
  assert (Hwaiting : q_del_waiting acquired_2 initial_2 = 1).
  { unfold q_del_waiting; rewrite (proj2 (Z.eqb_neq _ _) Hgroup); reflexivity. }
  Exists active_2 acquired_2 initial_2; entailer!.
Qed.

Lemma proof_of_OSQDel_entail_wit_3_2 : OSQDel_entail_wit_3_2.
Proof.
  left; intros; poly_store_unfold.
  subst pe opt_pre.
  sep_apply_l_atomic (q_del_uchar_range__entry_and_early_returns
    (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")) (q_post_group acquired_2 initial_2)).
  Intros.
  rewrite (unsigned_last_nbits_eq (q_post_group acquired_2 initial_2) 32 ltac:(lia)) in PreH1.
  assert (Hwaiting : q_del_waiting acquired_2 initial_2 = 0).
  { unfold q_del_waiting; rewrite PreH1; reflexivity. }
  Exists active_2 acquired_2 initial_2; entailer!.
Qed.

Lemma proof_of_OSQDel_entail_wit_7_1 : OSQDel_entail_wit_7_1.
Proof.
  right; intros.
  unfold q_del_after_schedule_context; Left; entailer!.
Qed.

Lemma proof_of_OSQDel_entail_wit_7_2 : OSQDel_entail_wit_7_2.
Proof.
  right; intros.
  assert (Hwaiting : tasks_waiting <> 1).
  { intros ->; apply PreH1; reflexivity. }
  subst pe choice.
  unfold q_del_after_schedule_context; Right; Exists buffer; entailer!.
Qed.

Lemma proof_of_OSQDel_return_wit_1 : OSQDel_return_wit_1.
Proof.
  left; intros.
  unfold q_pend_abort_output_address in PreH1; subst perr.
  apply q_del_finish_return; exact PreH2.
Qed.

Lemma proof_of_OSQDel_return_wit_2 : OSQDel_return_wit_2.
Proof.
  left; intros; poly_store_unfold.
  pose proof (proj1 PreH11) as Hints.
  rewrite Hints.
  sep_apply_l_atomic (q_del_interrupt_merge environment critical saved_local sg caller mask before PreH8).
  assert (Hresult : q_del_caller_result environment critical sg caller mask pe eid choice before
    pe 15 caller before QDelNoBuffer).
  { exists caller, before, false; split; [|auto].
    unfold q_del_prefix_program.
    rewrite (proj2 (Z.eqb_neq _ _) PreH5), PreH10,
      (proj2 (Z.ltb_lt 0 (q_del_int_nesting before)) ltac:(lia)); cbn; auto. }
  unfold q_pend_abort_output_address in PreH25; rewrite PreH25.
  pose proof (q_del_closed_return environment critical saved_local sg caller caller mask pe eid choice
    before before error_addr pe 15 QDelNoBuffer X Hresult PreH31) as Hreturn.
  cbn [q_del_buffer_rep] in Hreturn; sep_apply_r_atomic Hreturn; entailer!.
Qed.

Lemma proof_of_OSQDel_return_wit_3 : OSQDel_return_wit_3.
Proof.
  left; intros; poly_store_unfold.
  rewrite PreH6.
  sep_apply_l_atomic (q_del_type_merge_closed__entry_and_early_returns
    environment critical saved_local sg caller mask before eid PreH9 PreH8 PreH10).
  assert (Hresult : q_del_caller_result environment critical sg caller mask (event_addr sg eid) eid choice before
    (event_addr sg eid) 1 caller before QDelNoBuffer).
  { exists caller, before, false; split; [|auto].
    unfold q_del_prefix_program.
    rewrite (proj2 (Z.eqb_neq (event_addr sg eid) 0) ltac:(congruence)),
      (proj2 (Z.eqb_neq _ _) PreH1); cbn; auto. }
  unfold q_pend_abort_output_address in PreH14; rewrite PreH14.
  pose proof (q_del_closed_return environment critical saved_local sg caller caller mask (event_addr sg eid) eid choice
    before before error_addr (event_addr sg eid) 1 QDelNoBuffer X Hresult ltac:(rewrite <- PreH6; exact PreH20)) as Hreturn.
  cbn [q_del_buffer_rep] in Hreturn; sep_apply_r_atomic Hreturn; entailer!.
Qed.

Lemma proof_of_OSQDel_return_wit_4 : OSQDel_return_wit_4.
Proof.
  left; intros; poly_store_unfold.
  subst pevent_pre; subst pe.
  assert (Hresult : q_del_caller_result environment critical sg caller mask 0 eid choice before
    0 4 caller before QDelNoBuffer).
  { exists caller, before, false; split; [unfold q_del_prefix_program; cbn; auto|auto]. }
  unfold q_pend_abort_output_address in PreH3; rewrite PreH3.
  pose proof (q_del_closed_return environment critical saved_local sg caller caller mask 0 eid choice
    before before error_addr 0 4 QDelNoBuffer X Hresult PreH9) as Hreturn.
  cbn [q_del_buffer_rep] in Hreturn; sep_apply_r_atomic Hreturn; entailer!.
Qed.

Lemma proof_of_OSQDel_partial_solve_wit_7_pure : OSQDel_partial_solve_wit_7_pure.
Proof.
  unfold OSQDel_partial_solve_wit_7_pure; left; intros.
  unfold q_del_waiting in *.
  destruct (Z.eqb (q_post_group acquired initial) 0); cbn in PreH1;
    try discriminate; entailer!; lia.
Qed.

Lemma proof_of_OSQDel_partial_solve_wit_8_pure : OSQDel_partial_solve_wit_8_pure.
Proof. left; intros; unfold q_pend_abort_output_address; entailer!. Qed.

Lemma proof_of_OSQDel_partial_solve_wit_12_pure : OSQDel_partial_solve_wit_12_pure.
Proof.
  unfold OSQDel_partial_solve_wit_12_pure; left; intros.
  assert (Hwaiting : q_del_waiting acquired initial <> 0).
  { intro Hzero; rewrite Hzero in PreH1; apply PreH1; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSQDel_partial_solve_wit_15_pure : OSQDel_partial_solve_wit_15_pure.
Proof.
  unfold OSQDel_partial_solve_wit_15_pure; left; intros.
  assert (Hgroup : q_post_group state node <> 0).
  { intro Hzero; rewrite Hzero in PreH1; apply PreH1; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSQDel_partial_solve_wit_16_pure : OSQDel_partial_solve_wit_16_pure.
Proof.
  unfold OSQDel_partial_solve_wit_16_pure; left; intros.
  unfold os_sched_global_addresses, sched_new_global_addresses in PreH9.
  entailer!; tauto.
Qed.

Lemma proof_of_OSQDel_partial_solve_wit_18_pure : OSQDel_partial_solve_wit_18_pure.
Proof.
  unfold OSQDel_partial_solve_wit_18_pure; left; intros.
  sep_apply (store_uchar_range (&(pe # "os_event" ->ₛ "OSEventGrp")) (q_post_group state node)).
  Intros.
  assert (Hrange : 0 <= q_post_group state node <= 255).
  { change (0 <= q_post_group state node <= Byte.max_unsigned); tauto. }
  rewrite unsigned_last_nbits_eq in PreH1 by (change (0 <= q_post_group state node < 4294967296); lia).
  entailer!.
Qed.

Lemma proof_of_OSQDel_partial_solve_wit_19_pure : OSQDel_partial_solve_wit_19_pure.
Proof. left; intros; unfold q_pend_abort_output_address; entailer!. Qed.

Lemma proof_of_OSQDel_partial_solve_wit_22_pure : OSQDel_partial_solve_wit_22_pure.
Proof.
  left; intros.
  unfold q_del_restore_post; Intros returned current.
  destruct H as [[request [Hrequest Hprefix]] Hvalid].
  destruct request; cbn in Hrequest; subst tasks_waiting.
  - entailer!.
  - discriminate PreH1.
Qed.

Lemma proof_of_OSQDel_partial_solve_wit_28_pure : OSQDel_partial_solve_wit_28_pure.
Proof.
  unfold OSQDel_partial_solve_wit_28_pure; left; intros.
  sep_apply (store_uchar_range (&( "opt" )) choice).
  Intros.
  assert (Hrange : 0 <= choice <= 255).
  { change (0 <= choice <= Byte.max_unsigned); tauto. }
  entailer!; lia.
Qed.

Lemma proof_of_OSQDel_which_implies_wit_1 : OSQDel_which_implies_wit_1.
Proof.
  left; intros; poly_store_unfold.
  pose proof PreH4 as Hinput.
  destruct Hinput as [Hzero|[_ [Hpe [Hid [Hslot Hprotocol]]]]]; [contradiction|].
  pose proof PreH2 as [_ [Hlayout _]].
  pose proof (proj1 (proj1 (Hlayout eid Hid))) as Htype.
  rewrite Hpe, Htype, (q_post_closed_equiv _ _ _ _ _ _ _ PreH3).
  sep_apply_l_atomic (sem_query_type_split_full sg before eid observed Hslot).
  unfold q_post_type_context; entailer!.
  rewrite <- Hpe; exact PreH4.
Qed.

Lemma proof_of_OSQDel_which_implies_wit_2 : OSQDel_which_implies_wit_2.
Proof.
  left; intros; poly_store_unfold.
  pose proof (proj1 PreH8) as Hints.
  rewrite PreH1.
  sep_apply_l_atomic (q_del_type_merge_closed__entry_and_early_returns
    environment critical saved_local sg caller mask before eid PreH4 PreH3 PreH5).
  sep_apply_l_atomic (q_del_interrupt_split environment critical saved_local sg caller mask before PreH5).
  rewrite <- Hints; entailer!.
  rewrite <- PreH1; exact PreH6.
Qed.

Lemma proof_of_OSQDel_which_implies_wit_3 : OSQDel_which_implies_wit_3.
Proof.
  left; intros; poly_store_unfold.
  pose proof (proj1 PreH9) as Hints.
  rewrite Hints.
  sep_apply_l_atomic (q_del_interrupt_merge environment critical saved_local sg caller mask before PreH5).
  unfold q_post_save_pre; entailer!.
  rewrite <- Hints; exact PreH9.
Qed.

Lemma proof_of_OSQDel_which_implies_wit_4 : OSQDel_which_implies_wit_4.
Proof.
  left; intros; poly_store_unfold.
  unfold q_post_save_result; Intros active acquired initial.
  pose proof H as [_ [_ [_ [Hlookup _]]]].
  pose proof PreH3 as [_ [Hlayout _]].
  pose proof (proj1 (proj2 (Hlayout eid PreH2))) as Hgroup.
  rewrite q_post_masked_equiv.
  sep_apply_l_atomic (q_post_group_cell_split sg acquired eid initial Hlookup).
  Exists active acquired initial.
  rewrite PreH1, Hgroup; unfold q_post_group_context; entailer!.
Qed.

Lemma proof_of_OSQDel_which_implies_wit_5 : OSQDel_which_implies_wit_5.
Proof.
  left; intros; poly_store_unfold.
  unfold q_post_group_context; Intros.
  pose proof H as [Hacquire [Hprofile Hid]].
  pose proof Hacquire as [[Hvalid _] [_ [_ [Hlookup [Htype _]]]]].
  pose proof (q_pend_abort_progress_initial sg eid acquired_2) as Hprogress.
  Exists active_2 acquired_2 initial_2.
  unfold q_del_loop_group_context, q_del_loop_facts; entailer!.
Qed.

Lemma proof_of_OSQDel_which_implies_wit_6 : OSQDel_which_implies_wit_6.
Proof.
  left; intros; subst pe.
  unfold q_del_loop_group_context at 1; Intros.
  pose proof H as [Hacquire [Hprofile [Heid [Hint [Hwaiting [Hvalid [Hnode [Htype Hprogress]]]]]]]].
  assert (Hzero : q_post_group acquired_2 initial_2 = 0 /\ tasks_waiting = 0).
  { rewrite Hwaiting in *; unfold q_del_waiting in *.
    destruct (Z.eqb (q_post_group acquired_2 initial_2) 0) eqn:Hgroup;
      [apply Z.eqb_eq in Hgroup; auto|lia]. }
  destruct Hzero as [Hgroup Hwaitingzero].
  destruct (q_post_queue_current sg acquired_2 eid initial_2 Hvalid Hnode Htype Hgroup)
    as [q [Hq [Hempty Hqvalid]]].
  destruct (q_del_event_layout__recycle_and_protected_errors sg eid Hprofile Heid)
    as [_ [Hptr [_ Hgrp]]].
  rewrite Hgrp, Hptr.
  sep_apply_l_atomic (q_post_group_cell_merge sg acquired_2 eid initial_2 Hvalid Hnode).
  sep_apply_l_atomic (q_post_pointer_split sg acquired_2 eid initial_2 q Hnode Htype Hq); Intros.
  Exists active_2 acquired_2 initial_2 q; unfold q_del_pointer_context; entailer!.
Qed.

Lemma proof_of_OSQDel_which_implies_wit_7 : OSQDel_which_implies_wit_7.
Proof.
  left; intros; unfold q_pend_abort_output_address in PreH2; subst pq pe.
  rewrite PreH3, PreH4.
  rewrite (q_del_pointer_split_recycle__recycle_and_protected_errors
    environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed
    initial_2 acquired_2 initial_2 nil tasks_waiting choice q_2).
  Intros free slots; Exists active_2 acquired_2 initial_2 free slots q_2.
  unfold q_pend_abort_output_address; entailer!.
Qed.

Lemma proof_of_OSQDel_which_implies_wit_8 : OSQDel_which_implies_wit_8.
Proof.
  left; intros; unfold q_pend_abort_output_address in PreH3; subst pq.
  rewrite PreH4, PreH5.
  unfold q_del_recycle_context at 1; Intros.
  destruct H as [Hfacts [Hqueue Hoption]].
  pose proof Hfacts as [_ [_ [_ [_ [Hwaiting _]]]]].
  pose proof Hqueue as [_ [_ [_ [_ [Hempty _]]]]].
  assert (Hwaitingzero : tasks_waiting = 0).
  { rewrite Hwaiting; unfold q_del_waiting, q_post_group; rewrite Hempty; reflexivity. }
  rewrite Hwaitingzero in Hfacts, Hoption.
  subst tasks_waiting.
  Exists active_2 acquired_2 (q_delete_recycle_state sg acquired_2 eid initial q) (QDelBufferSnapshot q slots).
  sep_apply_r_atomic (q_del_recycle_restore__recycle_and_protected_errors
    environment critical saved_local sg caller active_2 mask cpu_sr pe before acquired_2 eid observed
    initial acquired_2 initial nil 0 choice q free slots PreH1 PreH2).
  unfold q_del_recycle_context; entailer!.
Qed.

Lemma proof_of_OSQDel_which_implies_wit_9 : OSQDel_which_implies_wit_9.
Proof.
  left; intros; apply q_del_nonschedule_finish; lia.
Qed.

Lemma proof_of_OSQDel_which_implies_wit_10 : OSQDel_which_implies_wit_10.
Proof.
  left; intros; subst choice pe.
  unfold q_del_loop_group_context; Intros.
  pose proof H as [Hacquire [Hprofile [Heid [Hint [Hwaiting [Hvalid [Hnode [Htype Hprogress]]]]]]]].
  pose proof (proj1 Hacquire) as Hsave.
  pose proof (q_post_acquire_original_type _ _ _ _ _ _ _ _ _ _ _ _ Hacquire) as Hbeforetype.
  assert (Hgroup : Z.eqb (q_post_group acquired_2 initial) 0 = false).
  { destruct (Z.eqb (q_post_group acquired_2 initial) 0) eqn:Hgroup; [|reflexivity].
    unfold q_del_waiting in Hwaiting; rewrite Hgroup in Hwaiting; contradiction. }
  assert (Heffect : q_del_effect sg eid 0 acquired_2 (event_addr sg eid) 73 0 acquired_2 QDelNoBuffer).
  { unfold q_del_effect; exists error_codes.OS_ERR_TASK_WAITING, false.
    split; [reflexivity|]; split; [reflexivity|]; split.
    - unfold q_delete_critical; exists initial; split; [exact Hnode|].
      cbn [unsigned_last_nbits]. fold (q_post_group acquired_2 initial).
      rewrite Hgroup; cbn; auto.
    - unfold q_del_buffer_release; split; [discriminate|reflexivity]. }
  destruct (q_del_event_layout__recycle_and_protected_errors sg eid Hprofile Heid)
    as [_ [_ [_ Hgrp]]].
  rewrite Hgrp.
  sep_apply_l_atomic (q_post_group_cell_merge sg acquired_2 eid initial Hvalid Hnode).
  Exists active_2 acquired_2.
  unfold q_del_restore_pre, q_del_buffer_rep; rewrite q_post_masked_equiv; entailer!.
Qed.

Lemma proof_of_OSQDel_which_implies_wit_11 : OSQDel_which_implies_wit_11.
Proof.
  left; intros; apply q_del_nonschedule_finish; lia.
Qed.

Lemma proof_of_OSQDel_which_implies_wit_12 : OSQDel_which_implies_wit_12.
Proof.
  unfold OSQDel_which_implies_wit_12; left; intros.
  unfold q_del_loop_group_context; Intros.
  pose proof H as Hfacts.
  destruct H as [Hacquire [Hprofile [Heid [Hint [Hwaiting [Hvalid [Hlookup [Htype Hprogress]]]]]]]].
  assert (Hlayout : event_object_layout_prop sg eid).
  { apply (proj1 (proj2 Hprofile)); exact Heid. }
  pose proof Hlayout as Haddresses.
  destruct Haddresses as [_ [Hgrp _]].
  rewrite PreH1, Hgrp.
  sep_apply (q_post_group_cell_merge sg state_2 eid node_2 Hvalid Hlookup).
  sep_apply (q_pend_abort_wake_split sg state_2 eid node_2 Hvalid Hlookup Htype PreH2 Hlayout).
  Intros tid old.
  Exists active_2 acquired_2 initial_2 state_2 node_2 processed_2 tid old.
  unfold q_del_loop_wake_context; entailer!.
Qed.

Lemma proof_of_OSQDel_which_implies_wit_13 : OSQDel_which_implies_wit_13.
Proof.
  unfold OSQDel_which_implies_wit_13; left; intros.
  unfold q_del_loop_wake_context; Intros.
  destruct H as [Hfacts [Hgroup Hentry]].
  pose proof Hfacts as [Hacquire [Hprofile [Heid [Hint [Hwaiting [Hvalid [Hlookup [Htype Hprogress]]]]]]]].
  pose proof Hentry as [_ [_ [_ [_ [_ [Hhead Hold]]]]]].
  destruct (EventStateDef.waitList node) as [|head tail] eqn:Hlist; [discriminate|].
  inversion Hhead; subst head.
  destruct (event_wake_head sg state eid node tid tail PendQ 0 PendAbort
    Hvalid Hlookup ltac:(rewrite Htype; reflexivity) Hlist)
    as [found [Hfound [Hstep [Hnext Hnext_lookup]]]].
  assert (found = old) by congruence; subst found.
  sep_apply (q_pend_abort_wake_merge sg state eid node tid old priority Hvalid Hlookup Htype Hentry).
  Intros.
  sep_apply (q_pend_abort_mask_frame_wake_update environment critical saved_local sg active_2 cpu_sr acquired_2 state eid node tid old Hold).
  sep_apply (q_post_group_cell_split sg (cross_module_invariants.event_wake_state sg state eid node tid old PendQ 0 PendAbort)
    eid (event_wait.event_set_wait_list node tail) Hnext_lookup).
  Intros.
  assert (Hnext_progress : q_pend_abort_progress sg eid acquired_2
    (cross_module_invariants.event_wake_state sg state eid node tid old PendQ 0 PendAbort) (processed ++ cons priority nil)).
  { eapply q_pend_abort_progress_step; eassumption. }
  assert (Hlayout : event_object_layout_prop sg eid).
  { apply (proj1 (proj2 Hprofile)); exact Heid. }
  destruct Hlayout as [_ [Hgrp _]].
  Exists active_2 acquired_2 initial_2
    (cross_module_invariants.event_wake_state sg state eid node tid old PendQ 0 PendAbort)
    (event_wait.event_set_wait_list node tail) (processed ++ cons priority nil).
  rewrite PreH1, Hgrp.
  unfold q_del_loop_group_context, q_del_loop_facts; entailer!.
Qed.

Lemma proof_of_OSQDel_which_implies_wit_14 : OSQDel_which_implies_wit_14.
Proof.
  left; intros; subst pe.
  rewrite (q_del_group_split_pointer__recycle_and_protected_errors
    environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2
    eid observed initial_2 state_2 node_2 processed_2 tasks_waiting choice PreH4 ltac:(auto)).
  Intros q; Exists active_2 acquired_2 initial_2 state_2 node_2 processed_2 q; entailer!.
Qed.

Lemma proof_of_OSQDel_which_implies_wit_15 : OSQDel_which_implies_wit_15.
Proof.
  left; intros; unfold q_pend_abort_output_address in PreH2; subst pq pe.
  rewrite PreH3, PreH4.
  rewrite (q_del_pointer_split_recycle__recycle_and_protected_errors
    environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed
    initial_2 state_2 node_2 processed_2 tasks_waiting choice q_2).
  Intros free slots; Exists active_2 acquired_2 initial_2 state_2 node_2 processed_2 free slots q_2.
  unfold q_pend_abort_output_address; entailer!.
Qed.

Lemma proof_of_OSQDel_which_implies_wit_16 : OSQDel_which_implies_wit_16.
Proof.
  left; intros; unfold q_pend_abort_output_address in PreH3; subst pq.
  rewrite PreH4, PreH5.
  Exists active_2 acquired_2 (q_delete_recycle_state sg state eid node q) (QDelBufferSnapshot q slots).
  apply (q_del_recycle_restore__recycle_and_protected_errors
    environment critical saved_local sg caller active_2 mask cpu_sr pe before acquired_2 eid observed
    initial state node processed tasks_waiting choice q free slots PreH1 PreH2).
Qed.

Lemma proof_of_OSQDel_which_implies_wit_17 : OSQDel_which_implies_wit_17.
Proof.
  left; intros.
  unfold q_del_restore_post; Intros returned restored.
  destruct H as [[request [Hrequest Hprefix]] Hvalid].
  destruct request; cbn in Hrequest; subst tasks_waiting; [|lia].
  sep_apply_l_atomic
    (Ucos2Verify.VC.code.queue.spec.q_post_api_spec.q_post_closed_sched_pre
      environment critical saved_local sg returned mask restored
      (PreH2 returned restored 0 0 buffer_2 Hprefix)).
  Exists returned restored buffer_2; entailer!.
  exists true; split; [reflexivity|exact Hprefix].
Qed.

Lemma proof_of_OSQDel_which_implies_wit_18 : OSQDel_which_implies_wit_18.
Proof.
  left; intros; apply q_del_sched_finish; exact PreH1.
Qed.

Lemma proof_of_OSQDel_which_implies_wit_19 : OSQDel_which_implies_wit_19.
Proof.
  left; intros; unfold q_del_after_schedule_context.
  apply derivable1_orp_elim; [entailer!|].
  Intros buffer; apply q_del_nonschedule_finish; assumption.
Qed.

Lemma proof_of_OSQDel_which_implies_wit_20 : OSQDel_which_implies_wit_20.
Proof.
  left; intros; apply q_del_nonschedule_finish; lia.
Qed.

Lemma proof_of_OSQDel_which_implies_wit_21 : OSQDel_which_implies_wit_21.
Proof.
  left; intros; subst pe.
  unfold q_del_loop_group_context; Intros.
  pose proof H as [Hacquire [Hprofile [Heid [Hint [Hwaiting [Hvalid [Hnode [Htype Hprogress]]]]]]]].
  pose proof (proj1 Hacquire) as Hsave.
  pose proof (q_post_acquire_original_type _ _ _ _ _ _ _ _ _ _ _ _ Hacquire) as Hbeforetype.
  assert (Hbyte : unsigned_last_nbits choice 8 = choice).
  { apply unsigned_last_nbits_eq; cbn; lia. }
  assert (Heffect : q_del_effect sg eid choice acquired_2 (event_addr sg eid) 7 0 acquired_2 QDelNoBuffer).
  { unfold q_del_effect; rewrite Hbyte; exists error_codes.OS_ERR_INVALID_OPT, false.
    split; [reflexivity|]; split; [reflexivity|]; split.
    - unfold q_delete_critical; exists initial; split; [exact Hnode|].
      rewrite (proj2 (Z.eqb_neq _ _) PreH3), (proj2 (Z.eqb_neq _ _) PreH4); auto.
    - unfold q_del_buffer_release; split; [discriminate|reflexivity]. }
  destruct (q_del_event_layout__recycle_and_protected_errors sg eid Hprofile Heid)
    as [_ [_ [_ Hgrp]]].
  rewrite Hgrp.
  sep_apply_l_atomic (q_post_group_cell_merge sg acquired_2 eid initial Hvalid Hnode).
  Exists active_2 acquired_2.
  unfold q_del_restore_pre, q_del_buffer_rep; rewrite q_post_masked_equiv; entailer!.
Qed.

