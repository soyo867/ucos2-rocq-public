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
From Ucos2Verify.VC.code.queue Require Import q_pend_abort_goal.
From Ucos2Verify.VC.code.queue Require Import q_pend_abort_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.queue.spec.q_pend_abort_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSQPendAbort_entail_wit_1 : OSQPendAbort_entail_wit_1.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range (&(pe # "os_event" ->ₛ "OSEventType"))
    (event_slot_type_value (EventState before) eid)).
  entailer!.
Qed.

Lemma proof_of_OSQPendAbort_entail_wit_5_2 : OSQPendAbort_entail_wit_5_2.
Proof.
  unfold OSQPendAbort_entail_wit_5_2; left; intros.
  subst opt_pre.
  prop_apply_p (store_uchar_range (&("opt")) option).
  Intros.
  Exists retval_2 active_2 acquired_3 initial_3 tid_2 old_2.
  entailer!.
  rewrite PreH2; reflexivity.
Qed.

Lemma proof_of_OSQPendAbort_entail_wit_6_2 : OSQPendAbort_entail_wit_6_2.
Proof.
  left; intros.
  Exists active_2 acquired_2 released_2; entailer!.
Qed.

Lemma proof_of_OSQPendAbort_return_wit_1 : OSQPendAbort_return_wit_1.
Proof.
  left; intros.
  unfold q_pend_abort_output_address in PreH19; subst perr_pre.
  rewrite PreH2.
  apply q_pend_abort_nonschedule_return; rewrite <- PreH2; exact PreH25.
Qed.

Lemma proof_of_OSQPendAbort_return_wit_2 : OSQPendAbort_return_wit_2.
Proof.
  left; intros.
  unfold q_pend_abort_output_address in PreH2; subst perr.
  destruct PreH1 as [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  apply q_pend_abort_sched_return; assumption.
Qed.

Lemma proof_of_OSQPendAbort_return_wit_3 : OSQPendAbort_return_wit_3.
Proof.
  left; intros.
  unfold q_pend_abort_output_address in PreH14; subst perr_pre.
  subst pe.
  pose proof (Ucos2Verify.lib.event.event_table_layout_select sg eid
    (proj1 (proj2 PreH9)) PreH8) as Hlayout.
  pose proof (proj1 (Ucos2Verify.lib.event.event_object_layout_core_proj
    sg eid Hlayout)) as Htype_address.
  rewrite Htype_address; unfold q_post_type_context.
  sep_apply (Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.sem_query_type_merge_full
    sg before eid PreH10).
  sep_apply (proj2 (q_post_closed_equiv environment critical saved_local sg caller mask before PreH10)).
  apply q_pend_abort_closed_return; [|exact PreH20].
  exists caller, before, false; split; [|split; reflexivity].
  unfold q_pend_abort_prefix_program.
  rewrite (proj2 (Z.eqb_neq _ _) PreH7), (proj2 (Z.eqb_neq _ _) PreH1).
  split; reflexivity.
Qed.

Lemma proof_of_OSQPendAbort_return_wit_4 : OSQPendAbort_return_wit_4.
Proof.
  left; intros.
  unfold q_pend_abort_output_address in PreH3; subst perr_pre.
  apply q_pend_abort_closed_return; [|exact PreH9].
  exists caller, before, false; split; [|split; reflexivity].
  unfold q_pend_abort_prefix_program.
  assert (Hpe : pe = 0) by lia.
  rewrite Hpe; cbn; split; reflexivity.
Qed.

Lemma proof_of_OSQPendAbort_partial_solve_wit_5_pure : OSQPendAbort_partial_solve_wit_5_pure.
Proof.
  left; intros.
  assert (Hgroup : q_post_group acquired initial <> 0).
  { intro Hzero; rewrite Hzero in PreH1; cbn in PreH1; contradiction. }
  entailer!.
Qed.

Lemma proof_of_OSQPendAbort_partial_solve_wit_6_pure : OSQPendAbort_partial_solve_wit_6_pure.
Proof.
  unfold OSQPendAbort_partial_solve_wit_6_pure; left; intros.
  prop_apply_p (store_uchar_range
    (&((pe) # "os_event" ->ₛ "OSEventGrp")) (q_post_group state node)).
  Intros.
  change (0 <= q_post_group state node <= 255) in H.
  rewrite unsigned_last_nbits_eq in PreH1 by (change (0 <= q_post_group state node < 4294967296); lia).
  entailer!.
Qed.

Lemma proof_of_OSQPendAbort_partial_solve_wit_7_pure : OSQPendAbort_partial_solve_wit_7_pure.
Proof.
  left; intros.
  unfold os_sched_global_addresses, sched_new_spec.sched_new_global_addresses in PreH11.
  destruct PreH11 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
  entailer!.
Qed.

Lemma proof_of_OSQPendAbort_partial_solve_wit_9_pure : OSQPendAbort_partial_solve_wit_9_pure.
Proof.
  unfold OSQPendAbort_partial_solve_wit_9_pure; left; intros.
  prop_apply_p (store_uchar_range
    (&((pe) # "os_event" ->ₛ "OSEventGrp")) (q_post_group state node)).
  Intros.
  change (0 <= q_post_group state node <= 255) in H.
  rewrite unsigned_last_nbits_eq in PreH1 by (change (0 <= q_post_group state node < 4294967296); lia).
  entailer!.
Qed.

Lemma proof_of_OSQPendAbort_partial_solve_wit_11_pure : OSQPendAbort_partial_solve_wit_11_pure.
Proof.
  left; intros.
  unfold os_sched_global_addresses, sched_new_spec.sched_new_global_addresses in PreH28.
  destruct PreH28 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
  entailer!.
Qed.

Lemma proof_of_OSQPendAbort_partial_solve_wit_12_pure : OSQPendAbort_partial_solve_wit_12_pure.
Proof.
  left; intros.
  unfold os_sched_global_addresses, sched_new_spec.sched_new_global_addresses in PreH28.
  destruct PreH28 as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
  entailer!.
Qed.

Lemma proof_of_OSQPendAbort_partial_solve_wit_18_pure : OSQPendAbort_partial_solve_wit_18_pure.
Proof.
  left; intros.
  sep_apply (store_uchar_range
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp"))
    (q_post_group acquired initial)).
  Intros.
  rewrite unsigned_last_nbits_eq in PreH1 by (cbn in *; lia).
  entailer!.
Qed.

Lemma proof_of_OSQPendAbort_which_implies_wit_1 : OSQPendAbort_which_implies_wit_1.
Proof.
  left; intros pe observed eid before mask caller sg critical saved_local environment
    Hpe Hprofile Hvalid Hinput.
  pose proof Hinput as [Hzero|[_ [Haddr [Hid [Hslot Hprotocol]]]]]; [contradiction|].
  subst pe.
  pose proof (event_table_layout_select sg eid (proj1 (proj2 Hprofile)) Hid)
    as [[Htype _] _].
  rewrite Htype, (q_post_closed_equiv environment critical saved_local sg caller mask before Hvalid).
  sep_apply (sem_query_type_split_full sg before eid observed Hslot).
  unfold q_post_type_context; entailer!.
Qed.

Lemma proof_of_OSQPendAbort_which_implies_wit_2 : OSQPendAbort_which_implies_wit_2.
Proof.
  right; intros pe observed eid before mask caller sg critical saved_local environment
    Haddr Hpe Hid Hprofile Hvalid Hinput Htype.
  subst pe.
  pose proof (event_table_layout_select sg eid (proj1 (proj2 Hprofile)) Hid)
    as [[Htype_addr _] _].
  rewrite Htype_addr.
  unfold q_post_type_context, q_post_save_pre.
  rewrite (q_post_closed_equiv environment critical saved_local sg caller mask before Hvalid).
  sep_apply (sem_query_type_merge_full sg before eid Hvalid).
  entailer!.
Qed.

Lemma proof_of_OSQPendAbort_which_implies_wit_3 : OSQPendAbort_which_implies_wit_3.
Proof.
  left; intros observed eid before mask caller sg critical saved_local environment
    pevent cpu_sr Haddr Hid Hprofile.
  subst pevent.
  pose proof (event_table_layout_select sg eid (proj1 (proj2 Hprofile)) Hid)
    as [_ [Hgroup _]].
  unfold q_post_save_result; Intros active acquired initial.
  pose proof H as [_ [_ [_ [Hlookup _]]]].
  rewrite (q_post_masked_equiv environment critical saved_local sg active cpu_sr acquired acquired).
  sep_apply (q_post_group_cell_split sg acquired eid initial Hlookup).
  Exists active acquired initial.
  rewrite Hgroup; unfold q_post_group_context; entailer!.
Qed.

Lemma proof_of_OSQPendAbort_which_implies_wit_4 : OSQPendAbort_which_implies_wit_4.
Proof.
  unfold OSQPendAbort_which_implies_wit_4; left; intros.
  unfold q_post_group_context; Intros.
  destruct H as [Hacquire [Hprofile Heid]].
  pose proof Hacquire as [[Hvalid Hsave] [Hbefore [Hobserved [Hlookup [Htype Hgeneration]]]]].
  assert (Hloop : q_pend_abort_loop_facts environment critical sg caller active_2 mask cpu_sr
    before acquired_2 eid observed initial_2 acquired_2 initial_2 nil 0).
  { unfold q_pend_abort_loop_facts.
    refine (conj Hacquire (conj Hprofile (conj Heid (conj PreH2
      (conj Hvalid (conj Hlookup (conj Htype _))))))).
    split; [apply q_pend_abort_progress_initial|].
    symmetry; apply event_pend_abort_count_nil. }
  Exists active_2 acquired_2 initial_2.
  unfold q_pend_abort_loop_group_context; entailer!.
Qed.

Lemma proof_of_OSQPendAbort_which_implies_wit_5 : OSQPendAbort_which_implies_wit_5.
Proof.
  unfold OSQPendAbort_which_implies_wit_5; left; intros.
  unfold q_pend_abort_loop_group_context; Intros.
  pose proof H as Hfacts.
  destruct H as [Hacquire [Hprofile [Heid [Hinitial_nonzero
    [Hvalid [Hlookup [Htype [Hprogress Hcount]]]]]]]].
  pose proof Hacquire as [[Hacquired Hsave] [Hbefore [Hobserved [Hinitial [Hinitial_type Hgeneration]]]]].
  pose proof (q_pend_abort_progress_nonempty_count_bound sg eid acquired_2 state_2
    processed_2 initial_2 node_2 Hacquired Hinitial Hinitial_type Hvalid Hlookup Htype
    PreH2 Hprogress) as Hbound.
  rewrite <- Hcount in Hbound.
  pose proof (event_table_layout_select sg eid (proj1 (proj2 Hprofile)) Heid) as Hlayout.
  pose proof Hlayout as [_ [Hgroup_address Htable_address]].
  subst pevent; rewrite Hgroup_address.
  sep_apply_l_atomic (q_post_group_cell_merge sg state_2 eid node_2 Hvalid Hlookup).
  sep_apply_l_atomic (q_pend_abort_wake_split sg state_2 eid node_2 Hvalid Hlookup Htype PreH2 Hlayout).
  Intros tid old.
  Exists active_2 acquired_2 initial_2 state_2 node_2 processed_2 tid old.
  unfold q_pend_abort_loop_wake_context; entailer!.
Qed.

Lemma proof_of_OSQPendAbort_which_implies_wit_6 : OSQPendAbort_which_implies_wit_6.
Proof.
  unfold OSQPendAbort_which_implies_wit_6; left; intros.
  unfold q_pend_abort_loop_wake_context; Intros.
  destruct H as [Hfacts [Hnonzero Hentry]].
  pose proof Hfacts as [Hacquire [Hprofile [Heid [Hinitial_nonzero
    [Hvalid [Hlookup [Htype [Hprogress Hcount]]]]]]]].
  pose proof Hentry as [_ [_ [_ [_ [_ [_ Hold]]]]]].
  sep_apply_l_atomic (q_pend_abort_wake_merge sg state eid node tid old priority
    Hvalid Hlookup Htype Hentry).
  Intros.
  rename H into Hstep.
  destruct (event_wake_decompose sg state eid node PendQ 0 PendAbort priority
    (cross_module_invariants.event_wake_state sg state eid node tid old PendQ 0 PendAbort)
    Hvalid Hlookup ltac:(rewrite Htype; reflexivity) Hnonzero Hstep)
    as [head [tail [previous [Hlist [Hprevious [Hpriority [Hnext [Hnext_valid Hnext_lookup]]]]]]]].
  pose proof (q_pend_abort_progress_step sg eid acquired_2 state processed node priority
    (cross_module_invariants.event_wake_state sg state eid node tid old PendQ 0 PendAbort)
    Hprogress Hlookup Hnonzero Hstep) as Hnext_progress.
  assert (Hnext_count : nbr_tasks + 1 = event_pend_abort_count (processed ++ priority :: nil)).
  { rewrite q_pend_abort_count_increment by (rewrite <- Hcount; lia).
    rewrite <- Hcount; reflexivity. }
  assert (Hnext_type : EventStateDef.eventType (event_set_wait_list node tail) = OS_EVENT_TYPE_Q)
    by exact Htype.
  assert (Hnext_facts : q_pend_abort_loop_facts environment critical sg caller active_2 mask cpu_sr
    before acquired_2 eid observed initial_2
    (cross_module_invariants.event_wake_state sg state eid node tid old PendQ 0 PendAbort)
    (event_set_wait_list node tail) (processed ++ priority :: nil) (nbr_tasks + 1)).
  { exact (conj Hacquire (conj Hprofile (conj Heid (conj Hinitial_nonzero
      (conj Hnext_valid (conj Hnext_lookup (conj Hnext_type (conj Hnext_progress Hnext_count)))))))). }
  sep_apply_l_atomic (q_pend_abort_mask_frame_wake_update environment critical saved_local sg
    active_2 cpu_sr acquired_2 state eid node tid old Hold).
  sep_apply_l_atomic (q_post_group_cell_split sg
    (cross_module_invariants.event_wake_state sg state eid node tid old PendQ 0 PendAbort) eid
    (event_set_wait_list node tail) Hnext_lookup).
  Intros.
  pose proof (event_table_layout_select sg eid (proj1 (proj2 Hprofile)) Heid) as [_ [Hgroup_address Htable_address]].
  Exists active_2 acquired_2 initial_2
    (cross_module_invariants.event_wake_state sg state eid node tid old PendQ 0 PendAbort)
    (event_set_wait_list node tail) (processed ++ priority :: nil).
  subst pevent; rewrite Hgroup_address.
  unfold q_pend_abort_loop_group_context; entailer!.
Qed.

Lemma proof_of_OSQPendAbort_which_implies_wit_7 : OSQPendAbort_which_implies_wit_7.
Proof.
  unfold OSQPendAbort_which_implies_wit_7; left; intros.
  unfold q_pend_abort_loop_group_context; Intros.
  destruct H as [Hacquire [Hprofile [Heid [Hinitial_nonzero
    [Hvalid [Hlookup [Htype [Hprogress Hcount]]]]]]]].
  pose proof Hacquire as [Hsave [Hbefore [Hobserved [Hinitial [Hinitial_type Hgeneration]]]]].
  pose proof (q_post_acquire_original_type environment critical sg caller active_2 mask cpu_sr
    before acquired_2 eid observed initial Hacquire) as Hbefore_type.
  pose proof (q_pend_abort_progress_done sg eid acquired_2 state processed node Hprogress Hlookup PreH4)
    as Hbroadcast.
  pose proof (q_pend_abort_broadcast_critical sg eid acquired_2 initial processed state
    Hinitial Hinitial_nonzero Hbroadcast) as Hcritical.
  subst option.
  assert (Heffect : q_pend_abort_effect sg eid 1 acquired_2 nbr_tasks 14 1 state).
  { exists error_codes.OS_ERR_PEND_ABORT, true; split; [reflexivity|]; split; [reflexivity|].
    rewrite unsigned_last_nbits_eq by (cbn; lia).
    rewrite Hcount; exact Hcritical. }
  pose proof (event_table_layout_select sg eid (proj1 (proj2 Hprofile)) Heid) as [_ [Hgroup_address Htable_address]].
  subst pe; rewrite Hgroup_address.
  sep_apply_l_atomic (q_post_group_cell_merge sg state eid node Hvalid Hlookup).
  Exists active_2 acquired_2 state.
  unfold q_pend_abort_restore_pre; rewrite q_post_masked_equiv; entailer!.
Qed.

Lemma proof_of_OSQPendAbort_which_implies_wit_8 : OSQPendAbort_which_implies_wit_8.
Proof.
  unfold OSQPendAbort_which_implies_wit_8; left; intros.
  unfold q_pend_abort_loop_wake_context; Intros.
  destruct H as [Hfacts [Hnonzero Hentry]].
  pose proof Hfacts as [Hacquire [Hprofile [Heid [Hinitial_nonzero
    [Hvalid [Hlookup [Htype [Hprogress Hcount]]]]]]]].
  pose proof Hentry as [_ [_ [_ [_ [_ [_ Hold]]]]]].
  pose proof Hacquire as [Hsave Hrest].
  pose proof (q_post_acquire_original_type environment critical sg caller active_2 mask cpu_sr
    before acquired_2 eid observed initial Hacquire) as Hbefore_type.
  sep_apply_l_atomic (q_pend_abort_wake_merge sg acquired_2 eid initial tid old priority
    Hvalid Hlookup Htype Hentry).
  Intros.
  rename H into Hstep.
  destruct (event_wake_decompose sg acquired_2 eid initial PendQ 0 PendAbort priority
    (cross_module_invariants.event_wake_state sg acquired_2 eid initial tid old PendQ 0 PendAbort)
    Hvalid Hlookup ltac:(rewrite Htype; reflexivity) Hnonzero Hstep)
    as [head [tail [previous [Hlist [Hprevious [Hpriority [Hnext [Hnext_valid Hnext_lookup]]]]]]]].
  assert (Heffect : q_pend_abort_effect sg eid option acquired_2 1 14 1
    (cross_module_invariants.event_wake_state sg acquired_2 eid initial tid old PendQ 0 PendAbort)).
  { exists error_codes.OS_ERR_PEND_ABORT, true; split; [reflexivity|]; split; [reflexivity|].
    rewrite unsigned_last_nbits_eq by (cbn; lia).
    eapply q_pend_abort_single_critical; eassumption. }
  sep_apply_l_atomic (q_pend_abort_mask_frame_wake_update environment critical saved_local sg
    active_2 cpu_sr acquired_2 acquired_2 eid initial tid old Hold).
  Exists active_2 acquired_2 (cross_module_invariants.event_wake_state sg acquired_2 eid initial tid old PendQ 0 PendAbort).
  unfold q_pend_abort_restore_pre; rewrite q_post_masked_equiv; entailer!.
Qed.

Lemma proof_of_OSQPendAbort_which_implies_wit_9 : OSQPendAbort_which_implies_wit_9.
Proof.
  unfold OSQPendAbort_which_implies_wit_9; left; intros.
  unfold q_pend_abort_loop_group_context; Intros.
  pose proof H as Hfacts.
  destruct H as [Hacquire [Hprofile [Heid [Hnonzero
    [Hvalid [Hlookup [Htype [Hprogress Hcount]]]]]]]].
  pose proof (event_table_layout_select sg eid (proj1 (proj2 Hprofile)) Heid) as Hlayout.
  pose proof Hlayout as [_ [Hgroup_address Htable_address]].
  subst pevent; rewrite Hgroup_address.
  sep_apply_l_atomic (q_post_group_cell_merge sg acquired_2 eid initial_2 Hvalid Hlookup).
  sep_apply_l_atomic (q_pend_abort_wake_split sg acquired_2 eid initial_2 Hvalid Hlookup Htype Hnonzero Hlayout).
  Intros tid old.
  Exists active_2 acquired_2 initial_2 tid old.
  unfold q_pend_abort_loop_wake_context; entailer!.
Qed.

Lemma proof_of_OSQPendAbort_which_implies_wit_10 : OSQPendAbort_which_implies_wit_10.
Proof.
  left; intros; apply q_pend_abort_restore_schedule; assumption.
Qed.

Lemma proof_of_OSQPendAbort_which_implies_wit_11 : OSQPendAbort_which_implies_wit_11.
Proof.
  left; intros; subst pe.
  unfold q_post_group_context; Intros.
  destruct H as [Hacquire [Hprofile Heid]].
  pose proof (q_post_acquire_original_type environment critical sg caller active_2 mask cpu_sr
    before acquired_2 eid observed initial Hacquire) as Htype.
  destruct Hacquire as [Hsave [Hobserved [Hqueue_before [Hlookup [Hqueue Hg]]]]].
  pose proof (proj1 Hsave) as Hvalid.
  pose proof (Ucos2Verify.lib.event.event_table_layout_select sg eid
    (proj1 (proj2 Hprofile)) Heid) as Hlayout.
  pose proof (proj1 (Ucos2Verify.lib.event.event_object_layout_wait_proj
    sg eid Hlayout)) as Hgroup_address.
  rewrite Hgroup_address.
  sep_apply (q_post_group_cell_merge sg acquired_2 eid initial Hvalid Hlookup).
  assert (Heffect : q_pend_abort_effect sg eid option acquired_2 0 0 0 acquired_2).
  { exists Ucos2Verify.lib.error_codes.OS_ERR_NONE, false; repeat split; try reflexivity.
    eapply q_pend_abort_empty_critical; eauto. }
  Exists active_2 acquired_2.
  unfold q_pend_abort_restore_pre.
  rewrite (q_post_masked_equiv environment critical saved_local sg active_2 cpu_sr
    acquired_2 acquired_2).
  entailer!.
Qed.

