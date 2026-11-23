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
From Ucos2Verify.VC.code.mbox Require Import mbox_pend_abort_goal.
From Ucos2Verify.VC.code.mbox Require Import mbox_pend_abort_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_pend_abort_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSMboxPendAbort_entail_wit_1 : OSMboxPendAbort_entail_wit_1.
Proof.
  unfold OSMboxPendAbort_entail_wit_1; left; intros.
  prop_apply_p (store_uchar_range (&(pe # "os_event" ->ₛ "OSEventType"))
    (event_slot_type_value (EventState before) eid)).
  Intros.
  change (0 <= event_slot_type_value (EventState before) eid <= 255) in H.
  entailer!.
Qed.

Lemma proof_of_OSMboxPendAbort_entail_wit_5_2 : OSMboxPendAbort_entail_wit_5_2.
Proof.
  unfold OSMboxPendAbort_entail_wit_5_2; left; intros.
  prop_apply_p (store_uchar_range (&("opt")) opt_pre).
  Intros.
  change (0 <= opt_pre <= 255) in H.
  Exists retval_2 active_2 acquired_3 initial_3 tid_2 old_2.
  entailer!.
  rewrite PreH2, PreH20; entailer!.
Qed.

Lemma proof_of_OSMboxPendAbort_entail_wit_6_2 : OSMboxPendAbort_entail_wit_6_2.
Proof.
  unfold OSMboxPendAbort_entail_wit_6_2; left; intros.
  Exists active_2 acquired_2 released_2; entailer!.
Qed.

Lemma proof_of_OSMboxPendAbort_return_wit_1 : OSMboxPendAbort_return_wit_1.
Proof.
  left; intros.
  unfold mbox_pend_abort_output_address in PreH19; subst perr_pre.
  rewrite <- PreH2.
  apply mbox_pend_abort_nonschedule_return; exact PreH25.
Qed.

Lemma proof_of_OSMboxPendAbort_return_wit_2 : OSMboxPendAbort_return_wit_2.
Proof.
  left; intros.
  destruct PreH1 as [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  unfold mbox_pend_abort_output_address in PreH2; subst perr.
  apply mbox_pend_abort_sched_return; assumption.
Qed.

Lemma proof_of_OSMboxPendAbort_return_wit_3 : OSMboxPendAbort_return_wit_3.
Proof.
  left; intros.
  unfold mbox_pend_abort_output_address in PreH14; subst perr_pre.
  pose proof (proj1 PreH9) as Hprofile.
  destruct Hprofile as [_ [_ [_ [_ [Htype _]]]]].
  rewrite Htype; rewrite PreH6 at 1.
  sep_apply_l_atomic (mbox_pend_abort_type_merge environment critical saved_local
    sg caller mask before eid PreH10).
  apply mbox_pend_abort_closed_return; [|exact PreH20].
  exists caller, before, false; split; [|split; reflexivity].
  unfold mbox_pend_abort_prefix_program.
  rewrite (proj2 (Z.eqb_neq _ _) PreH7), (proj2 (Z.eqb_neq _ _) PreH1).
  split; reflexivity.
Qed.

Lemma proof_of_OSMboxPendAbort_return_wit_4 : OSMboxPendAbort_return_wit_4.
Proof.
  left; intros.
  unfold mbox_pend_abort_output_address in PreH3; subst perr_pre.
  apply mbox_pend_abort_closed_return; [|exact PreH9].
  exists caller, before, false; split; [|split; reflexivity].
  assert (Hpe : pe = 0) by lia.
  unfold mbox_pend_abort_prefix_program; rewrite Hpe; simpl.
  split; reflexivity.
Qed.

Lemma proof_of_OSMboxPendAbort_partial_solve_wit_5_pure : OSMboxPendAbort_partial_solve_wit_5_pure.
Proof.
  unfold OSMboxPendAbort_partial_solve_wit_5_pure; left; intros.
  assert (Hnonzero : q_post_group acquired initial <> 0).
  { intro Hzero. rewrite Hzero in PreH1. vm_compute in PreH1. contradiction. }
  entailer!.
Qed.

Lemma proof_of_OSMboxPendAbort_partial_solve_wit_6_pure : OSMboxPendAbort_partial_solve_wit_6_pure.
Proof.
  unfold OSMboxPendAbort_partial_solve_wit_6_pure; left; intros.
  assert (Hnonzero : q_post_group state node <> 0).
  { intro Hzero; apply PreH1; rewrite Hzero; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSMboxPendAbort_partial_solve_wit_7_pure : OSMboxPendAbort_partial_solve_wit_7_pure.
Proof.
  left; intros.
  unfold sched_spec.os_sched_global_addresses,
    sched_new_spec.sched_new_global_addresses in PreH11.
  decompose [and] PreH11; entailer!.
Qed.

Lemma proof_of_OSMboxPendAbort_partial_solve_wit_9_pure : OSMboxPendAbort_partial_solve_wit_9_pure.
Proof.
  unfold OSMboxPendAbort_partial_solve_wit_9_pure; left; intros.
  prop_apply (store_uchar_range (&((pe) # "os_event" ->ₛ "OSEventGrp"))
    (q_post_group state node)).
  Intros.
  assert (Hcast : unsigned_last_nbits (q_post_group state node) 32 =
    q_post_group state node).
  { apply unsigned_last_nbits_eq; change (0 <= q_post_group state node < 4294967296).
    change (0 <= q_post_group state node <= 255) in H; lia. }
  rewrite Hcast in PreH1; entailer!.
Qed.

Lemma proof_of_OSMboxPendAbort_partial_solve_wit_11_pure : OSMboxPendAbort_partial_solve_wit_11_pure.
Proof.
  left; intros.
  unfold sched_spec.os_sched_global_addresses,
    sched_new_spec.sched_new_global_addresses in PreH28.
  decompose [and] PreH28; entailer!.
Qed.

Lemma proof_of_OSMboxPendAbort_partial_solve_wit_12_pure : OSMboxPendAbort_partial_solve_wit_12_pure.
Proof.
  left; intros.
  unfold sched_spec.os_sched_global_addresses,
    sched_new_spec.sched_new_global_addresses in PreH28.
  decompose [and] PreH28; entailer!.
Qed.

Lemma proof_of_OSMboxPendAbort_partial_solve_wit_18_pure : OSMboxPendAbort_partial_solve_wit_18_pure.
Proof.
  unfold OSMboxPendAbort_partial_solve_wit_18_pure; left; intros.
  prop_apply_p (store_uchar_range
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp"))
    (q_post_group acquired initial)).
  Intros.
  change (0 <= q_post_group acquired initial <= 255) in H.
  rewrite unsigned_last_nbits_eq in PreH1 by (change (0 <= q_post_group acquired initial < 4294967296); lia).
  entailer!.
Qed.

Lemma proof_of_OSMboxPendAbort_which_implies_wit_1 : OSMboxPendAbort_which_implies_wit_1.
Proof.
  unfold OSMboxPendAbort_which_implies_wit_1; left; intros.
  destruct (proj1 PreH4) as [Hzero | [_ [Haddr [Hid Hpublic]]]]; [contradiction|].
  destruct (proj1 PreH2) as [_ [_ [_ [_ [Htype Hptr]]]]].
  rewrite Haddr, Htype.
  sep_apply_l_atomic (mbox_pend_abort_type_split environment critical saved_local sg caller mask
    before pe eid observed PreH3 PreH1 PreH4).
  entailer!.
  rewrite <- Haddr; exact PreH4.
Qed.

Lemma proof_of_OSMboxPendAbort_which_implies_wit_2 : OSMboxPendAbort_which_implies_wit_2.
Proof.
  unfold OSMboxPendAbort_which_implies_wit_2; left; intros.
  destruct (proj1 PreH4) as [_ [_ [_ [_ [Htype Hptr]]]]].
  subst pe; rewrite Htype.
  sep_apply_l_atomic (mbox_pend_abort_type_merge environment critical saved_local sg caller mask before eid PreH5).
  unfold mbox_pend_abort_save_pre; entailer!.
Qed.

Lemma proof_of_OSMboxPendAbort_which_implies_wit_3 : OSMboxPendAbort_which_implies_wit_3.
Proof.
  unfold OSMboxPendAbort_which_implies_wit_3; left; intros.
  unfold mbox_pend_abort_save_result; Intros active acquired initial.
  pose proof H as Hfacts.
  destruct Hfacts as [Hsave [Hobserved [Htype [Hlookup Hcurrent]]]].
  rewrite (q_post_masked_equiv environment critical saved_local sg active cpu_sr acquired acquired).
  sep_apply_l_atomic (q_post_group_cell_split sg acquired eid initial Hlookup).
  Intros.
  pose proof (proj1 (event_object_layout_wait_proj sg eid
    (event_table_layout_select sg eid (proj2 PreH3) PreH2))) as Hgroup.
  Exists active acquired initial.
  rewrite PreH1, Hgroup.
  unfold mbox_pend_abort_group_context; entailer!.
Qed.

Lemma proof_of_OSMboxPendAbort_which_implies_wit_4 : OSMboxPendAbort_which_implies_wit_4.
Proof.
  unfold OSMboxPendAbort_which_implies_wit_4; left; intros.
  unfold mbox_pend_abort_group_context; Intros.
  destruct H as [Hacquire [Hprofile Hid]].
  pose proof Hacquire as Hfacts.
  destruct Hfacts as [Hsave [Hobserved [Htype [Hlookup [Hcurrent Hgeneration]]]]].
  pose proof (proj1 Hsave) as Hvalid.
  pose proof (mbox_pend_abort_progress_initial sg eid acquired_2) as Hprogress.
  pose proof event_pend_abort_count_nil as Hcount.
  Exists active_2 acquired_2 initial_2.
  unfold mbox_pend_abort_loop_group_context, mbox_pend_abort_loop_facts.
  entailer!.
Qed.

Lemma proof_of_OSMboxPendAbort_which_implies_wit_5 : OSMboxPendAbort_which_implies_wit_5.
Proof.
  unfold OSMboxPendAbort_which_implies_wit_5; left; intros.
  unfold mbox_pend_abort_loop_group_context; Intros.
  pose proof H as [Hacquire [Hprofile [Hid [Hinitial_nonzero
    [Hvalid [Hlookup [Htype [Hprogress Hcount]]]]]]]].
  pose proof Hacquire as [Hsave [_ [_ [Hinitial_lookup [Hinitial_type Hg]]]]].
  pose proof (mbox_pend_abort_progress_nonempty_count_bound sg eid acquired_2
    state_2 processed_2 initial_2 node_2 (proj1 Hsave) Hinitial_lookup Hinitial_type
    Hvalid Hlookup Htype PreH2 Hprogress) as Hbound.
  pose proof ((proj2 Hprofile) eid Hid) as Hlayout.
  pose proof (proj1 (proj2 Hlayout)) as Hgroup_address.
  rewrite PreH1, Hgroup_address.
  sep_apply_l_atomic (q_post_group_cell_merge sg state_2 eid node_2 Hvalid Hlookup).
  sep_apply_l_atomic (mbox_pend_abort_wake_split sg state_2 eid node_2
    Hvalid Hlookup Htype PreH2 Hlayout).
  Intros tid old.
  Exists active_2 acquired_2 initial_2 state_2 node_2 processed_2 tid old.
  unfold mbox_pend_abort_loop_wake_context; entailer!; try lia.
Qed.

Lemma proof_of_OSMboxPendAbort_which_implies_wit_6 : OSMboxPendAbort_which_implies_wit_6.
Proof.
  unfold OSMboxPendAbort_which_implies_wit_6; left; intros.
  unfold mbox_pend_abort_loop_wake_context; Intros.
  pose proof H as [Hfacts [Hnonzero Hentry]].
  pose proof Hfacts as [Hacquire [Hprofile [Hid [Hinitial_nonzero
    [Hvalid [Hlookup [Htype [Hprogress Hcount]]]]]]]].
  pose proof Hentry as [_ [_ [_ [_ [_ [_ Hold]]]]]].
  sep_apply_l_atomic (mbox_pend_abort_wake_merge sg state eid node tid old priority
    Hvalid Hlookup Htype Hentry).
  Intros.
  set (next := cross_module_invariants.event_wake_state sg state eid node tid old PendMbox 0 PendAbort) in *.
  assert (Hkind : event_type_to_pend_type (EventStateDef.eventType node) = Some PendMbox)
    by (rewrite Htype; reflexivity).
  destruct (event_wake_decompose sg state eid node PendMbox 0 PendAbort priority next
    Hvalid Hlookup Hkind Hnonzero H0)
    as [head [tail [previous [Hlist [Hprevious [Hpriority [Hnext [Hnext_valid Hnext_lookup]]]]]]]].
  sep_apply_l_atomic (mbox_pend_abort_mask_frame_wake_update environment critical saved_local
    sg active_2 cpu_sr acquired_2 state eid node tid old Hold).
  fold next.
  sep_apply_l_atomic (q_post_group_cell_split sg next eid (event_set_wait_list node tail) Hnext_lookup).
  Intros.
  pose proof (mbox_pend_abort_progress_step sg eid acquired_2 state processed node priority next
    Hprogress Hlookup Hnonzero H0) as Hnext_progress.
  assert (Hnext_count : nbr_tasks + 1 = event_pend_abort_count (processed ++ cons priority nil)).
  { rewrite mbox_pend_abort_count_increment by (rewrite <- Hcount; lia); lia. }
  pose proof ((proj2 Hprofile) eid Hid) as Hlayout.
  pose proof (proj1 (proj2 Hlayout)) as Hgroup_address.
  rewrite PreH1, Hgroup_address.
  Exists active_2 acquired_2 initial_2 next (event_set_wait_list node tail) (processed ++ cons priority nil).
  unfold mbox_pend_abort_loop_group_context, mbox_pend_abort_loop_facts.
  entailer!; try assumption.
Qed.

Lemma proof_of_OSMboxPendAbort_which_implies_wit_7 : OSMboxPendAbort_which_implies_wit_7.
Proof.
  unfold OSMboxPendAbort_which_implies_wit_7; left; intros.
  unfold mbox_pend_abort_loop_group_context; Intros.
  pose proof H as [Hacquire [Hprofile [Hid [Hinitial_nonzero
    [Hvalid [Hlookup [Htype [Hprogress Hcount]]]]]]]].
  pose proof Hacquire as [Hsave [_ [_ [Hinitial_lookup [Hinitial_type Hg]]]]].
  pose proof (mbox_pend_abort_acquire_original_type environment critical sg caller active_2
    mask cpu_sr before acquired_2 eid observed initial Hacquire) as Horiginal_type.
  pose proof (mbox_pend_abort_progress_done sg eid acquired_2 state processed node
    Hprogress Hlookup PreH4) as Hbroadcast.
  assert (Heffect : mbox_pend_abort_effect sg eid option acquired_2 nbr_tasks 14 1 state).
  { unfold mbox_pend_abort_effect; exists error_codes.OS_ERR_PEND_ABORT, true.
    split; [reflexivity|]; split; [reflexivity|].
    rewrite PreH3, Hcount.
    change (mbox_pend_abort_critical sg eid 1 acquired_2
      (event_pend_abort_count processed, (error_codes.OS_ERR_PEND_ABORT, true)) state).
    apply (mbox_pend_abort_broadcast_critical sg eid acquired_2 initial processed state
      Hinitial_lookup Hinitial_nonzero Hbroadcast). }
  pose proof ((proj2 Hprofile) eid Hid) as Hlayout.
  pose proof (proj1 (proj2 Hlayout)) as Hgroup_address.
  rewrite PreH1, Hgroup_address.
  sep_apply_l_atomic (q_post_group_cell_merge sg state eid node Hvalid Hlookup).
  Exists active_2 acquired_2 state.
  unfold mbox_pend_abort_restore_pre.
  rewrite (q_post_masked_equiv environment critical saved_local sg active_2 cpu_sr acquired_2 state).
  entailer!.
Qed.

Lemma proof_of_OSMboxPendAbort_which_implies_wit_8 : OSMboxPendAbort_which_implies_wit_8.
Proof.
  unfold OSMboxPendAbort_which_implies_wit_8; left; intros.
  unfold mbox_pend_abort_loop_wake_context; Intros.
  pose proof H as [Hfacts [Hnonzero Hentry]].
  pose proof Hfacts as [Hacquire [Hprofile [Hid [Hinitial_nonzero
    [Hvalid [Hlookup [Htype [Hprogress Hcount]]]]]]]].
  pose proof Hacquire as [Hsave Hacquire_rest].
  pose proof Hentry as [_ [_ [_ [_ [_ [_ Hold]]]]]].
  pose proof (mbox_pend_abort_acquire_original_type environment critical sg caller active_2
    mask cpu_sr before acquired_2 eid observed initial Hacquire) as Horiginal_type.
  sep_apply_l_atomic (mbox_pend_abort_wake_merge sg acquired_2 eid initial tid old priority
    Hvalid Hlookup Htype Hentry).
  Intros.
  set (next := cross_module_invariants.event_wake_state sg acquired_2 eid initial tid old PendMbox 0 PendAbort) in *.
  assert (Hkind : event_type_to_pend_type (EventStateDef.eventType initial) = Some PendMbox)
    by (rewrite Htype; reflexivity).
  destruct (event_wake_decompose sg acquired_2 eid initial PendMbox 0 PendAbort priority next
    Hvalid Hlookup Hkind Hnonzero H0)
    as [head [tail [previous [Hlist [Hprevious [Hpriority [Hnext [Hnext_valid Hnext_lookup]]]]]]]].
  sep_apply_l_atomic (mbox_pend_abort_mask_frame_wake_update environment critical saved_local
    sg active_2 cpu_sr acquired_2 acquired_2 eid initial tid old Hold).
  fold next.
  assert (Heffect : mbox_pend_abort_effect sg eid option acquired_2 1 14 1 next).
  { unfold mbox_pend_abort_effect; exists error_codes.OS_ERR_PEND_ABORT, true.
    split; [reflexivity|]; split; [reflexivity|].
    rewrite unsigned_last_nbits_eq by (change (0 <= option < 256); lia).
    exact (mbox_pend_abort_single_critical sg eid option acquired_2 initial priority next
      Hlookup Hnonzero PreH2 H0). }
  Exists active_2 acquired_2 next.
  unfold mbox_pend_abort_restore_pre.
  rewrite (q_post_masked_equiv environment critical saved_local sg active_2 cpu_sr acquired_2 next).
  entailer!.
Qed.

Lemma proof_of_OSMboxPendAbort_which_implies_wit_9 : OSMboxPendAbort_which_implies_wit_9.
Proof.
  unfold OSMboxPendAbort_which_implies_wit_9; left; intros.
  unfold mbox_pend_abort_loop_group_context; Intros.
  pose proof H as [Hacquire [Hprofile [Hid [Hinitial_nonzero
    [Hvalid [Hlookup [Htype [Hprogress Hcount]]]]]]]].
  pose proof ((proj2 Hprofile) eid Hid) as Hlayout.
  pose proof (proj1 (proj2 Hlayout)) as Hgroup_address.
  rewrite PreH1, Hgroup_address.
  sep_apply_l_atomic (q_post_group_cell_merge sg acquired_2 eid initial_2 Hvalid Hlookup).
  sep_apply_l_atomic (mbox_pend_abort_wake_split sg acquired_2 eid initial_2
    Hvalid Hlookup Htype Hinitial_nonzero Hlayout).
  Intros tid old.
  Exists active_2 acquired_2 initial_2 tid old.
  unfold mbox_pend_abort_loop_wake_context; entailer!.
Qed.

Lemma proof_of_OSMboxPendAbort_which_implies_wit_10 : OSMboxPendAbort_which_implies_wit_10.
Proof.
  left; intros.
  apply mbox_pend_abort_restore_schedule; exact PreH1.
Qed.

Lemma proof_of_OSMboxPendAbort_which_implies_wit_11 : OSMboxPendAbort_which_implies_wit_11.
Proof.
  left; intros.
  unfold mbox_pend_abort_group_context; Intros.
  destruct H as [Hacquire [Hprofile Hid]].
  pose proof (proj1 Hacquire) as Hsave.
  pose proof (proj1 Hsave) as Hvalid.
  pose proof (proj1 (proj2 (proj2 (proj2 Hacquire)))) as Hlookup.
  pose proof (mbox_pend_abort_acquire_original_type environment critical sg
    caller active_2 mask cpu_sr before acquired_2 eid observed initial Hacquire) as Htype.
  pose proof (proj1 (proj2 ((proj2 Hprofile) eid Hid))) as Hgroup.
  rewrite PreH1, Hgroup.
  sep_apply (q_post_group_cell_merge sg acquired_2 eid initial Hvalid Hlookup).
  assert (Heffect : mbox_pend_abort_effect sg eid option acquired_2 0 0 0 acquired_2).
  { exists Ucos2Verify.lib.error_codes.OS_ERR_NONE, false; split; [reflexivity|].
    split; [reflexivity|].
    eapply mbox_pend_abort_empty_critical; eassumption. }
  Exists active_2 acquired_2.
  unfold mbox_pend_abort_restore_pre.
  rewrite (q_post_masked_equiv environment critical saved_local sg active_2
    cpu_sr acquired_2 acquired_2).
  entailer!.
Qed.

