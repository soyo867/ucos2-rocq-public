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
From Ucos2Verify.VC.code.queue Require Import q_post_goal.
From Ucos2Verify.VC.code.queue Require Import q_post_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.queue.spec.q_post_api_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.
Local Open Scope sac.

Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.error_codes.

Lemma proof_of_OSQPost_entail_wit_1 : OSQPost_entail_wit_1.
Proof.
  unfold OSQPost_entail_wit_1; left; intros.
  prop_apply_p (store_uchar_range
    (&(pe # "os_event" ->ₛ "OSEventType"))
    (event_slot_type_value before.(EventState) eid)).
  entailer!.
Qed.

Lemma proof_of_OSQPost_entail_wit_2 : OSQPost_entail_wit_2.
Proof.
  unfold OSQPost_entail_wit_2; left; intros.
  subst pmsg_pre.
  rewrite PreH2 in *.
  Exists retval_2 active_2 acquired_3 current_3 tid_2 old_2.
  entailer!.
Qed.

Lemma proof_of_OSQPost_entail_wit_3_1 : OSQPost_entail_wit_3_1.
Proof.
  unfold OSQPost_entail_wit_3_1; left; intros.
  subst pmsg_pre. rewrite PreH11 in *.
  unfold q_post_slot_frame; Intros.
  assert (Hnext : q_post_next_in q_4 = q_4.(qStart)).
  { unfold q_post_next_in, Ucos2Verify.lib.event.sizeof_ptr.
    change (queue_in_addr q_4 + 4 = queue_end_addr q_4) in PreH1.
    rewrite (proj2 (Z.eqb_eq _ _) PreH1); reflexivity. }
  Exists active_2 acquired_3 current_3 free_2 slots_2 q_4.
  rewrite Hnext; entailer!.
Qed.

Lemma proof_of_OSQPost_entail_wit_3_2 : OSQPost_entail_wit_3_2.
Proof.
  unfold OSQPost_entail_wit_3_2; left; intros.
  subst pmsg_pre. rewrite PreH11 in *.
  unfold q_post_slot_frame; Intros.
  assert (Hnext : q_post_next_in q_4 = queue_in_addr q_4 + 4).
  { unfold q_post_next_in, Ucos2Verify.lib.event.sizeof_ptr.
    change (queue_in_addr q_4 + 4 <> queue_end_addr q_4) in PreH1.
    rewrite (proj2 (Z.eqb_neq _ _) PreH1); reflexivity. }
  Exists active_2 acquired_3 current_3 free_2 slots_2 q_4.
  rewrite Hnext; entailer!.
Qed.

Lemma proof_of_OSQPost_return_wit_1 : OSQPost_return_wit_1.
Proof.
  unfold OSQPost_return_wit_1; left; intros.
  apply q_post_nonschedule_return; exact PreH3.
Qed.

Lemma proof_of_OSQPost_return_wit_2 : OSQPost_return_wit_2.
Proof.
  unfold OSQPost_return_wit_2; left; intros.
  rewrite <- PreH7.
  apply q_post_nonschedule_return; exact PreH29.
Qed.

Lemma proof_of_OSQPost_return_wit_3 : OSQPost_return_wit_3.
Proof.
  unfold OSQPost_return_wit_3; left; intros.
  destruct PreH1 as [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  eapply q_post_sched_return; [exact Hprefix|exact PreH3].
Qed.

Lemma proof_of_OSQPost_return_wit_4 : OSQPost_return_wit_4.
Proof.
  unfold OSQPost_return_wit_4; left; intros.
  assert (Hresult : q_post_caller_result environment critical sg caller mask
    pe eid message before 1 caller before).
  { exists caller, before, false; split.
    - unfold q_post_prefix_program.
      rewrite (proj2 (Z.eqb_neq _ _) PreH7),
        (proj2 (Z.eqb_neq _ _) PreH1).
      split; reflexivity.
    - split; reflexivity. }
  sep_apply_r_atomic (q_post_closed_return environment critical saved_local sg
    caller caller mask pe eid message before before 1 X Hresult PreH19).
  pose proof PreH9 as [_ [Hlayout _]].
  destruct (Hlayout eid PreH8) as [[Htype [Hptr Hcnt]] Hremaining_layout].
  rewrite (q_post_closed_equiv environment critical saved_local sg caller mask before PreH10).
  unfold q_post_type_context.
  rewrite PreH6, Htype.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid PreH10).
  entailer!.
Qed.

Lemma proof_of_OSQPost_return_wit_5 : OSQPost_return_wit_5.
Proof.
  unfold OSQPost_return_wit_5; left; intros.
  assert (Hzero : pe = 0) by congruence.
  assert (Hresult : q_post_caller_result environment critical sg caller mask
    pe eid message before 4 caller before).
  { exists caller, before, false; split.
    - unfold q_post_prefix_program; rewrite Hzero; split; reflexivity.
    - split; reflexivity. }
  apply q_post_closed_return; [exact Hresult|exact PreH8].
Qed.

Lemma proof_of_OSQPost_partial_solve_wit_5_pure : OSQPost_partial_solve_wit_5_pure.
Proof.
  unfold OSQPost_partial_solve_wit_5_pure; left; intros.
  assert (Hnonzero : q_post_group acquired current <> 0).
  { intro Hzero; rewrite Hzero in PreH1; apply PreH1; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSQPost_partial_solve_wit_6_pure : OSQPost_partial_solve_wit_6_pure.
Proof.
  unfold OSQPost_partial_solve_wit_6_pure; left; intros.
  destruct PreH26 as [_ [_ [_ [_ [_ [Htable [_ Hnew]]]]]]].
  destruct Hnew as [Hunmap [Hgroup [Hrows Hhigh]]].
  entailer!.
Qed.

Lemma proof_of_OSQPost_partial_solve_wit_11_pure : OSQPost_partial_solve_wit_11_pure.
Proof.
  unfold OSQPost_partial_solve_wit_11_pure; left; intros.
  prop_apply_p (store_uchar_range
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp")) (q_post_group acquired current)).
  Intros_p Hrange.
  change (0 <= q_post_group acquired current <= 255) in Hrange.
  assert (Hbits : unsigned_last_nbits (q_post_group acquired current) 32 = q_post_group acquired current).
  { apply unsigned_last_nbits_eq; change (0 <= q_post_group acquired current < 4294967296); lia. }
  rewrite Hbits in PreH1; entailer!.
Qed.

Lemma proof_of_OSQPost_which_implies_wit_1 : OSQPost_which_implies_wit_1.
Proof.
  unfold OSQPost_which_implies_wit_1; left; intros.
  pose proof PreH4 as [Hzero|[_ [Haddr [Hid [Hslot Hhandle]]]]]; [contradiction|].
  subst pe.
  pose proof PreH2 as [_ [Hlayout _]].
  destruct (Hlayout eid Hid) as [[Htype Hrest] Hwait].
  rewrite (q_post_closed_equiv environment critical saved_local sg caller mask before PreH3).
  sep_apply_l_atomic (sem_query_type_split_full sg before eid observed Hslot).
  unfold q_post_type_context; rewrite Htype; entailer!.
Qed.

Lemma proof_of_OSQPost_which_implies_wit_2 : OSQPost_which_implies_wit_2.
Proof.
  unfold OSQPost_which_implies_wit_2; left; intros.
  subst pe.
  pose proof PreH4 as [_ [Hlayout _]].
  destruct (Hlayout eid PreH3) as [[Htype Hrest] Hwait].
  unfold q_post_type_context; rewrite Htype.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid PreH5).
  unfold q_post_save_pre.
  rewrite (q_post_closed_equiv environment critical saved_local sg caller mask before PreH5).
  entailer!.
Qed.

Lemma proof_of_OSQPost_which_implies_wit_3 : OSQPost_which_implies_wit_3.
Proof.
  unfold OSQPost_which_implies_wit_3; left; intros.
  unfold q_post_save_result; Intros active acquired current.
  pose proof H as [Hsave [Hobserved [Hotype [Hcurrent [Hctype Hg]]]]].
  pose proof (proj1 Hsave) as Hvalid.
  pose proof PreH3 as [_ [Hlayout _]].
  destruct (Hlayout eid PreH2) as [Hcore [Hgrp Htbl]].
  rewrite q_post_masked_equiv.
  sep_apply_l_atomic (q_post_group_cell_split sg acquired eid current Hcurrent).
  Exists active acquired current.
  unfold q_post_group_context; rewrite PreH1, Hgrp; entailer!.
Qed.

Lemma proof_of_OSQPost_which_implies_wit_4 : OSQPost_which_implies_wit_4.
Proof.
  unfold OSQPost_which_implies_wit_4; left; intros.
  unfold q_post_group_context; Intros.
  destruct H as [Hacquire [Hprofile Hid]].
  pose proof Hacquire as [Hsave [Hobserved [Hotype [Hcurrent [Hctype Hg]]]]].
  pose proof (proj1 Hsave) as Hvalid.
  pose proof Hprofile as [_ [Hlayout _]].
  pose proof (Hlayout eid Hid) as Hobject.
  destruct Hobject as [Hcore [Hgrp Htbl]].
  rewrite PreH1, Hgrp.
  sep_apply_l_atomic (q_post_group_cell_merge sg acquired_2 eid current_2 Hvalid Hcurrent).
  sep_apply_l_atomic (q_post_wake_split sg acquired_2 eid current_2 Hvalid Hcurrent Hctype PreH2 (Hlayout eid Hid)).
  Intros tid old; Exists active_2 acquired_2 current_2 tid old.
  unfold q_post_wake_context, q_post_sched_group, q_post_sched_rows; entailer!.
Qed.

Lemma proof_of_OSQPost_which_implies_wit_5 : OSQPost_which_implies_wit_5.
Proof.
  unfold OSQPost_which_implies_wit_5; left; intros.
  unfold q_post_wake_context; Intros.
  destruct H as [Hacquire [Hprofile [Hid [Hgroup Hentry]]]].
  pose proof Hacquire as [Hsave [Hobserved [Hotype [Hcurrent [Hctype Hg]]]]].
  pose proof (proj1 Hsave) as Hvalid.
  pose proof (q_post_acquire_original_type _ _ _ _ _ _ _ _ _ _ _ _ Hacquire) as Htype.
  pose proof Hentry as [_ [_ [_ [_ [_ [Hhead Hold]]]]]].
  destruct current.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
  injection Hhead as Hhead; subst head.
  destruct (q_post_wake_head sg acquired_2 eid current tid tail message Hvalid Hcurrent Hctype Hlist)
    as [found [Hfound [Hactual [Hafter Hafter_node]]]].
  assert (found = old) by congruence; subst found.
  unfold q_post_sched_group, q_post_sched_rows.
  sep_apply_l_atomic (q_post_wake_merge sg acquired_2 eid current tid old message priority
    Hvalid Hcurrent Hctype Hentry).
  Intros released.
  unfold q_post_wake_result in H.
  rewrite Hactual in H; injection H as Hpriority Hreleased; subst released.
  sep_apply_l_atomic (q_post_mask_frame_wake_update environment critical saved_local sg active_2
    cpu_sr acquired_2 acquired_2 eid current tid old message Hold).
  assert (Heffect : q_post_effect sg eid message acquired_2 0 1
    (event_wake_state sg acquired_2 eid current tid old PendQ message PendOK)).
  { exists OS_ERR_NONE, true; split; [reflexivity|]; split; [reflexivity|].
    eapply q_post_wake_critical; [exact Hcurrent|exact Hgroup|exact Hactual]. }
  Exists active_2 acquired_2 (event_wake_state sg acquired_2 eid current tid old PendQ message PendOK).
  unfold q_post_restore_pre; rewrite q_post_masked_equiv; entailer!.
Qed.

Lemma proof_of_OSQPost_which_implies_wit_6 : OSQPost_which_implies_wit_6.
Proof.
  unfold OSQPost_which_implies_wit_6; left; intros.
  apply q_post_restored_schedule_pre; exact PreH1.
Qed.

Lemma proof_of_OSQPost_which_implies_wit_7 : OSQPost_which_implies_wit_7.
Proof.
  unfold OSQPost_which_implies_wit_7; left; intros.
  unfold q_post_group_context; Intros.
  destruct H as [Hacquire [Hprofile Hid]].
  pose proof Hacquire as [Hsave [Hobserved [Hotype [Hcurrent [Hctype Hg]]]]].
  pose proof (proj1 Hsave) as Hvalid.
  pose proof Hprofile as [_ [Hlayout _]].
  destruct (Hlayout eid Hid) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]].
  rewrite PreH1, Hgrp.
  sep_apply_l_atomic (q_post_group_cell_merge sg acquired_2 eid current_2 Hvalid Hcurrent).
  destruct (q_post_queue_current sg acquired_2 eid current_2 Hvalid Hcurrent Hctype PreH2)
    as [q [Hq [Hempty Hqvalid]]].
  sep_apply_l_atomic (q_post_pointer_split sg acquired_2 eid current_2 q Hcurrent Hctype Hq).
  Exists active_2 acquired_2 current_2 q.
  unfold q_post_pointer_context; rewrite Hptr; entailer!.
Qed.

Lemma proof_of_OSQPost_which_implies_wit_8 : OSQPost_which_implies_wit_8.
Proof.
  unfold OSQPost_which_implies_wit_8; left; intros.
  unfold q_post_pointer_context; Intros.
  destruct H as [Hacquire [Hprofile [Hid [Hgroup [Hq [Hempty Hqvalid]]]]]].
  pose proof Hacquire as [Hsave [Hobserved [Hotype [Hcurrent [Hctype Hg]]]]].
  pose proof (proj1 Hsave) as Hvalid.
  pose proof Hprofile as [_ [Hlayout _]].
  destruct (Hlayout eid Hid) as [[Htype [Hptr Hcnt]] Hwait].
  rewrite PreH2, Hptr.
  sep_apply_l_atomic (q_post_pointer_merge sg acquired_2 eid current_2 q_2 Hvalid Hcurrent Hctype Hq).
  sep_apply_l_atomic (q_post_queue_split sg acquired_2 eid current_2 q_2 Hcurrent Hctype Hq Hempty).
  Intros free slots.
  pose proof Hqvalid as [Hqid [_ [Hsize Hrest]]].
  pose proof (queue_entries_in_range sg (@nil TaskID) q_2 Hqvalid) as Hcount.
  rewrite (q_post_qcb_cells_equiv sg q_2 Hprofile Hqid).
  Exists active_2 acquired_2 current_2 free slots q_2.
  unfold q_post_store_context, q_post_qcb_cells; rewrite PreH1; entailer!.
Qed.

Lemma proof_of_OSQPost_which_implies_wit_9 : OSQPost_which_implies_wit_9.
Proof.
  unfold OSQPost_which_implies_wit_9; left; intros.
  unfold q_post_store_context; Intros.
  destruct H as [Hacquire [Hprofile [Hgroup [Hbase Hfacts]]]].
  pose proof (proj1 Hacquire) as Hsave.
  pose proof Hfacts as [Hvalid [Hcurrent [Hctype [Hq [Hempty [Hqvalid Hrest]]]]]].
  pose proof (proj1 Hqvalid) as Hqid.
  pose proof (q_post_acquire_original_type _ _ _ _ _ _ _ _ _ _ _ _ Hacquire) as Htype.
  pose proof (q_post_full_critical sg acquired_2 eid current q message Hcurrent Hq Hgroup ltac:(lia)) as Hstep.
  assert (Heffect : q_post_effect sg eid message acquired_2 30 0 acquired_2).
  { exists OS_ERR_Q_FULL, false; repeat split; assumption || reflexivity. }
  rewrite Hbase.
  pose proof (proj2 (q_post_qcb_cells_equiv sg q Hprofile Hqid)) as Hqcb.
  unfold q_post_qcb_cells in Hqcb; sep_apply_l_atomic Hqcb.
  sep_apply_l_atomic (q_post_queue_merge_original sg acquired_2 eid current q free slots Hfacts).
  Exists active_2 acquired_2.
  unfold q_post_restore_pre; rewrite q_post_masked_equiv; entailer!.
Qed.

Lemma proof_of_OSQPost_which_implies_wit_10 : OSQPost_which_implies_wit_10.
Proof.
  unfold OSQPost_which_implies_wit_10; left; intros.
  unfold q_post_store_context; Intros.
  destruct H as [Hacquire [Hprofile [Hgroup [Hbase Hfacts]]]].
  pose proof Hfacts as [Hvalid [Hcurrent [Hctype [Hq [Hempty [Hqvalid Hrest]]]]]].
  pose proof (q_post_nonfull_bounds sg q_2 Hqvalid PreH1) as [Hsize [Hin [Hcount Hend]]].
  sep_apply_l_atomic (q_post_slot_split sg q_2 slots_2 Hqvalid PreH1).
  Exists active_2 acquired_2 current_2 free_2 slots_2 q_2.
  unfold q_post_store_context, q_post_slot_frame; entailer!.
Qed.

Lemma proof_of_OSQPost_which_implies_wit_11 : OSQPost_which_implies_wit_11.
Proof.
  unfold OSQPost_which_implies_wit_11; left; intros.
  unfold q_post_store_context, q_post_slot_frame; Intros.
  destruct H as [Hacquire [Hprofile [Hgroup [Hbase Hfacts]]]].
  pose proof (proj1 Hacquire) as Hsave.
  pose proof Hfacts as [Hvalid [Hcurrent [Hctype [Hq [Hempty [Hqvalid [Hbinding [Hpart [Hslots Hmodel]]]]]]]]].
  pose proof (proj1 Hqvalid) as Hqid.
  pose proof (q_post_acquire_original_type _ _ _ _ _ _ _ _ _ _ _ _ Hacquire) as Htype.
  pose proof (q_post_enqueue_back_some q message PreH2) as Henqueue.
  pose proof (q_post_enqueue_critical sg acquired_2 eid current q message slots
    (q_post_enqueued_fields q message) Hcurrent Hq Hgroup Hslots Henqueue) as Hstep.
  assert (Hreleased : UCOS2_state_inv sg (q_post_enqueue_state acquired_2 eid current q message slots)).
  { eapply q_post_critical_preserves_validity; [exact Hvalid|exact Hcurrent|exact Hctype|exact Hstep]. }
  assert (Heffect : q_post_effect sg eid message acquired_2 0 0
    (q_post_enqueue_state acquired_2 eid current q message slots)).
  { exists OS_ERR_NONE, false; split; [reflexivity|]; split; [reflexivity|exact Hstep]. }
  rewrite Hbase.
  pose proof (proj1 (q_post_qcb_enqueued_equiv sg q message Hprofile Hqid PreH2)) as Hqcb.
  unfold q_post_qcb_cells in Hqcb; sep_apply_l_atomic Hqcb.
  sep_apply_l_atomic (q_post_enqueue_merge sg acquired_2 eid current q free slots message Hfacts PreH2).
  sep_apply_l_atomic (q_post_mask_frame_event_update environment critical saved_local sg active_2
    cpu_sr acquired_2 acquired_2 (q_post_enqueue_state acquired_2 eid current q message slots) eq_refl).
  Exists active_2 acquired_2 (q_post_enqueue_state acquired_2 eid current q message slots).
  unfold q_post_restore_pre; rewrite q_post_masked_equiv; entailer!.
Qed.
