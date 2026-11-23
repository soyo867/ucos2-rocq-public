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
From Ucos2Verify.VC.code.queue Require Import q_post_opt_goal.
From Ucos2Verify.VC.code.queue Require Import q_post_opt_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.queue.spec.q_post_opt_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSQPostOpt_entail_wit_1 : OSQPostOpt_entail_wit_1.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range (&("opt")) opt_pre).
  entailer!.
  change (0 <= opt_pre <= 255) in H; lia.
Qed.

Lemma proof_of_OSQPostOpt_entail_wit_2 : OSQPostOpt_entail_wit_2.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range (&(pe # "os_event" ->ₛ "OSEventType"))
    (event_slot_type_value (EventState before) eid)).
  entailer!; change (0 <= event_slot_type_value (EventState before) eid <= 255) in H; lia.
Qed.

Lemma proof_of_OSQPostOpt_entail_wit_7 : OSQPostOpt_entail_wit_7.
Proof.
  left; intros.
  subst opt_pre pmsg_pre pevent_pre pe.
  Exists retval_2 active_2 acquired_3 current_3 tid_2 old_2.
  entailer!.
Qed.

Lemma proof_of_OSQPostOpt_entail_wit_8_1 : OSQPostOpt_entail_wit_8_1.
Proof.
  unfold OSQPostOpt_entail_wit_8_1; left; intros.
  Exists active_2 acquired_3 current_3 free_2 slots_2 q_5.
  unfold q_post_store_context, q_post_opt_front_slot_frame; Intros.
  assert (Hvalid : queue_fields_consistency sg nil q_5)
    by (unfold q_post_queue_facts in *; tauto).
  assert (Hroom : queue_entries q_5 < qSize q_5) by tauto.
  pose proof (q_post_nonfull_bounds sg q_5 Hvalid Hroom) as [_ [_ [Hcount _]]].
  assert (Hout : queue_end_addr q_5 + (-1 * sizeof(PTR)) = q_post_opt_next_out q_5).
  { unfold q_post_opt_next_out; rewrite (proj2 (Z.eqb_eq _ _) PreH1); reflexivity. }
  rewrite Hout, PreH34, PreH35, PreH15; entailer!; congruence.
Qed.

Lemma proof_of_OSQPostOpt_entail_wit_8_2 : OSQPostOpt_entail_wit_8_2.
Proof.
  unfold OSQPostOpt_entail_wit_8_2; left; intros.
  Exists active_2 acquired_3 current_3 free_2 slots_2 q_5.
  unfold q_post_store_context, q_post_opt_front_slot_frame; Intros.
  assert (Hvalid : queue_fields_consistency sg nil q_5)
    by (unfold q_post_queue_facts in *; tauto).
  assert (Hroom : queue_entries q_5 < qSize q_5) by tauto.
  pose proof (q_post_nonfull_bounds sg q_5 Hvalid Hroom) as [_ [_ [Hcount _]]].
  assert (Hout : queue_out_addr q_5 + (-1 * sizeof(PTR)) = q_post_opt_next_out q_5).
  { unfold q_post_opt_next_out; rewrite (proj2 (Z.eqb_neq _ _) PreH1); reflexivity. }
  rewrite Hout, PreH34, PreH35, PreH15; entailer!; congruence.
Qed.

Lemma proof_of_OSQPostOpt_entail_wit_9_1 : OSQPostOpt_entail_wit_9_1.
Proof.
  unfold OSQPostOpt_entail_wit_9_1; left; intros.
  Exists active_2 acquired_2 current_2 free_2 slots_2 q_2.
  unfold q_post_opt_written_in, q_post_opt_written_out, q_post_opt_written_buffer,
    q_post_front_requested.
  rewrite (proj2 (Z.eqb_neq _ _) PreH4); cbn [negb]; entailer!.
Qed.

Lemma proof_of_OSQPostOpt_entail_wit_9_2 : OSQPostOpt_entail_wit_9_2.
Proof.
  unfold OSQPostOpt_entail_wit_9_2; left; intros.
  Exists active_2 acquired_3 current_3 free_2 slots_2 q_5.
  unfold q_post_opt_written_in, q_post_opt_written_out, q_post_opt_written_buffer,
    q_post_front_requested.
  rewrite PreH35 in PreH2; rewrite PreH2; cbn [Z.eqb negb].
  unfold q_post_store_context, q_post_slot_frame; Intros.
  assert (Hvalid : queue_fields_consistency sg nil q_5)
    by (unfold q_post_queue_facts in *; tauto).
  assert (Hroom : queue_entries q_5 < qSize q_5) by tauto.
  pose proof (q_post_nonfull_bounds sg q_5 Hvalid Hroom) as [_ [_ [Hcount _]]].
  assert (Hin : q_post_next_in q_5 = qStart q_5).
  { change (queue_in_addr q_5 + 4 = queue_end_addr q_5) in PreH1.
    unfold q_post_next_in, Ucos2Verify.lib.event.sizeof_ptr.
    rewrite (proj2 (Z.eqb_eq _ _) PreH1); reflexivity. }
  rewrite Hin, PreH34, PreH35, PreH15; entailer!; congruence.
Qed.

Lemma proof_of_OSQPostOpt_entail_wit_9_3 : OSQPostOpt_entail_wit_9_3.
Proof.
  unfold OSQPostOpt_entail_wit_9_3; left; intros.
  Exists active_2 acquired_3 current_3 free_2 slots_2 q_5.
  unfold q_post_opt_written_in, q_post_opt_written_out, q_post_opt_written_buffer,
    q_post_front_requested.
  rewrite PreH35 in PreH2; rewrite PreH2; cbn [Z.eqb negb].
  unfold q_post_store_context, q_post_slot_frame; Intros.
  assert (Hvalid : queue_fields_consistency sg nil q_5)
    by (unfold q_post_queue_facts in *; tauto).
  assert (Hroom : queue_entries q_5 < qSize q_5) by tauto.
  pose proof (q_post_nonfull_bounds sg q_5 Hvalid Hroom) as [_ [_ [Hcount _]]].
  assert (Hin : q_post_next_in q_5 = queue_in_addr q_5 + (1 * sizeof(PTR))).
  { change (queue_in_addr q_5 + 4 <> queue_end_addr q_5) in PreH1.
    unfold q_post_next_in, Ucos2Verify.lib.event.sizeof_ptr.
    rewrite (proj2 (Z.eqb_neq _ _) PreH1); reflexivity. }
  rewrite Hin, PreH34, PreH35, PreH15; entailer!; congruence.
Qed.

Lemma proof_of_OSQPostOpt_return_wit_1 : OSQPostOpt_return_wit_1.
Proof.
  left; intros; apply q_post_opt_nonschedule_return; assumption.
Qed.

Lemma proof_of_OSQPostOpt_return_wit_2 : OSQPostOpt_return_wit_2.
Proof.
  left; intros; rewrite <- PreH7.
  apply q_post_opt_nonschedule_return; assumption.
Qed.

Lemma proof_of_OSQPostOpt_return_wit_3 : OSQPostOpt_return_wit_3.
Proof.
  left; intros.
  destruct PreH1 as [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  apply q_post_opt_sched_return; assumption.
Qed.

Lemma proof_of_OSQPostOpt_return_wit_4 : OSQPostOpt_return_wit_4.
Proof.
  left; intros.
  destruct PreH1 as [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  apply q_post_opt_sched_return; assumption.
Qed.

Lemma proof_of_OSQPostOpt_return_wit_5 : OSQPostOpt_return_wit_5.
Proof.
  left; intros; rewrite <- PreH3.
  unfold q_post_opt_schedule_flag; rewrite (proj2 (Z.eqb_neq _ _) PreH1).
  apply q_post_opt_nonschedule_return; assumption.
Qed.

Lemma proof_of_OSQPostOpt_return_wit_6 : OSQPostOpt_return_wit_6.
Proof.
  left; intros.
  unfold q_post_opt_schedule_flag; rewrite (proj2 (Z.eqb_neq _ _) PreH1).
  apply q_post_opt_nonschedule_return; assumption.
Qed.

Lemma proof_of_OSQPostOpt_return_wit_7 : OSQPostOpt_return_wit_7.
Proof.
  left; intros.
  assert (Hresult : q_post_opt_caller_result environment critical sg caller mask
    pe eid message options before 1 caller before).
  { exists caller, before, false; split.
    - unfold q_post_opt_prefix_program.
      rewrite (proj2 (Z.eqb_neq _ _) PreH5), (proj2 (Z.eqb_neq _ _) PreH1).
      split; reflexivity.
    - split; reflexivity. }
  sep_apply_r_atomic (q_post_opt_closed_return environment critical saved_local sg
    caller caller mask pe eid message options before before 1 X Hresult PreH22).
  rewrite (q_post_closed_equiv environment critical saved_local sg caller mask before PreH8).
  unfold q_post_type_context.
  pose proof (proj1 (proj1 ((proj1 (proj2 PreH7)) eid PreH6))) as Htype_address.
  rewrite PreH4, Htype_address.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid PreH8).
  entailer!.
Qed.

Lemma proof_of_OSQPostOpt_return_wit_8 : OSQPostOpt_return_wit_8.
Proof.
  left; intros.
  assert (Hpe : pe = 0) by lia.
  apply q_post_opt_closed_return; [|exact PreH13].
  exists caller, before, false; split.
  - unfold q_post_opt_prefix_program; rewrite Hpe; cbn; split; reflexivity.
  - split; reflexivity.
Qed.

Lemma proof_of_OSQPostOpt_partial_solve_wit_5_pure : OSQPostOpt_partial_solve_wit_5_pure.
Proof.
  left; intros.
  assert (Hgroup : q_post_group acquired current <> 0).
  { intro Hzero; rewrite Hzero in PreH2; vm_compute in PreH2; contradiction. }
  entailer!.
Qed.

Lemma proof_of_OSQPostOpt_partial_solve_wit_6_pure : OSQPostOpt_partial_solve_wit_6_pure.
Proof.
  left; intros.
  assert (Hgroup : q_post_group state node <> 0).
  { intro Hzero; rewrite Hzero in PreH1; vm_compute in PreH1; contradiction. }
  entailer!.
Qed.

Lemma proof_of_OSQPostOpt_partial_solve_wit_7_pure : OSQPostOpt_partial_solve_wit_7_pure.
Proof.
  left; intros.
  unfold os_sched_global_addresses, sched_new_global_addresses in PreH10.
  entailer!.
Qed.

Lemma proof_of_OSQPostOpt_partial_solve_wit_9_pure : OSQPostOpt_partial_solve_wit_9_pure.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range (&(pe # "os_event" ->ₛ "OSEventGrp"))
    (q_post_group state node)); Intros.
  change (0 <= q_post_group state node <= 255) in H.
  rewrite unsigned_last_nbits_eq in PreH1 by
    (change (0 <= q_post_group state node < 4294967296); lia).
  entailer!.
Qed.

Lemma proof_of_OSQPostOpt_partial_solve_wit_10_pure : OSQPostOpt_partial_solve_wit_10_pure.
Proof.
  left; intros.
  assert (Hgroup : q_post_group acquired current <> 0).
  { intro Hzero; rewrite Hzero in PreH2.
    apply PreH2; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSQPostOpt_partial_solve_wit_11_pure : OSQPostOpt_partial_solve_wit_11_pure.
Proof.
  left; intros.
  unfold os_sched_global_addresses, sched_new_spec.sched_new_global_addresses in PreH30.
  entailer!; tauto.
Qed.

Lemma proof_of_OSQPostOpt_partial_solve_wit_19_pure : OSQPostOpt_partial_solve_wit_19_pure.
Proof.
  left; intros.
  match goal with
  | |- context [store_uchar ?address (q_post_group acquired current)] =>
      sep_apply (store_uchar_range address (q_post_group acquired current))
  end.
  Intros.
  rewrite unsigned_last_nbits_eq in PreH1 by
    (change (0 <= q_post_group acquired current < 4294967296); change (0 <= q_post_group acquired current <= 255) in H; lia).
  entailer!.
Qed.

Lemma proof_of_OSQPostOpt_which_implies_wit_1 : OSQPostOpt_which_implies_wit_1.
Proof.
  left; intros pe observed eid before mask caller sg critical saved_local environment
    Hpe Hprofile Hvalid Hinput.
  pose proof Hinput as [Hzero|[_ [Haddr [Heid [Hslot Hhandle]]]]]; [contradiction|].
  pose proof (proj1 (proj1 (proj1 (proj2 Hprofile) eid Heid))) as Htypeaddr.
  subst pe; rewrite Htypeaddr.
  rewrite (q_post_closed_equiv environment critical saved_local sg caller mask before Hvalid).
  unfold q_post_type_context.
  sep_apply_l_atomic (sem_query_type_split_full sg before eid observed Hslot).
  Intros; entailer!.
Qed.

Lemma proof_of_OSQPostOpt_which_implies_wit_2 : OSQPostOpt_which_implies_wit_2.
Proof.
  left; intros pe observed eid before mask caller sg critical saved_local environment
    Haddr Hpe Heid Hprofile Hvalid Hinput Htype.
  pose proof (proj1 (proj1 (proj1 (proj2 Hprofile) eid Heid))) as Htypeaddr.
  subst pe; rewrite Htypeaddr.
  unfold q_post_type_context, q_post_save_pre.
  rewrite (q_post_closed_equiv environment critical saved_local sg caller mask before Hvalid).
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid Hvalid).
  entailer!.
Qed.

Lemma proof_of_OSQPostOpt_which_implies_wit_3 : OSQPostOpt_which_implies_wit_3.
Proof.
  left; intros observed eid before mask caller sg critical saved_local environment
    pevent cpu_sr Haddr Heid Hprofile.
  pose proof (proj1 (proj2 (proj1 (proj2 Hprofile) eid Heid))) as Hgroupaddr.
  subst pevent; rewrite Hgroupaddr.
  unfold q_post_save_result; Intros active acquired current.
  pose proof H as [_ [_ [_ [Hnode _]]]].
  rewrite q_post_masked_equiv.
  sep_apply_l_atomic (q_post_group_cell_split sg acquired eid current Hnode).
  Intros; Exists active acquired current.
  unfold q_post_group_context; entailer!.
Qed.

Lemma proof_of_OSQPostOpt_which_implies_wit_4 : OSQPostOpt_which_implies_wit_4.
Proof.
  left; intros.
  unfold q_post_group_context; Intros.
  destruct H as [Hacquire [Hprofile Heid]].
  pose proof Hacquire as [[Hvalid _] [_ [_ [Hnode [Htype _]]]]].
  Exists active_2 acquired_2 initial_2 acquired_2 initial_2.
  unfold q_post_opt_loop_context, q_post_opt_loop_facts.
  pose proof (q_post_opt_broadcast_cont_start sg eid message acquired_2).
  entailer!.
Qed.

Lemma proof_of_OSQPostOpt_which_implies_wit_5 : OSQPostOpt_which_implies_wit_5.
Proof.
  left; intros.
  prop_apply_p (q_post_opt_loop_context_facts__broadcast environment critical saved_local
    sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 message state_2 node_2).
  Intros.
  pose proof H as [_ [Hprofile [Heid _]]].
  pose proof (proj1 (proj2 (proj1 (proj2 Hprofile) eid Heid))) as Hgroupaddr.
  rewrite PreH1, Hgroupaddr.
  sep_apply_l_atomic (q_post_opt_loop_wake_split environment critical saved_local sg caller
    active_2 mask cpu_sr before acquired_2 eid observed initial_2 message state_2 node_2 PreH2).
  Intros tid old.
  Exists active_2 acquired_2 initial_2 state_2 node_2 tid old; entailer!.
Qed.

Lemma proof_of_OSQPostOpt_which_implies_wit_6 : OSQPostOpt_which_implies_wit_6.
Proof.
  left; intros.
  sep_apply_l_atomic (q_post_opt_loop_wake_merge environment critical saved_local sg caller
    active_2 mask cpu_sr before acquired_2 eid observed initial_2 message state_2 node_2 tid old priority).
  Intros after next.
  prop_apply_p (q_post_opt_loop_context_facts__broadcast environment critical saved_local
    sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 message after next).
  Intros.
  pose proof H as [_ [Hprofile [Heid _]]].
  pose proof (proj1 (proj2 (proj1 (proj2 Hprofile) eid Heid))) as Hgroupaddr.
  rewrite PreH1, Hgroupaddr.
  Exists active_2 acquired_2 initial_2 after next; entailer!.
Qed.

Lemma proof_of_OSQPostOpt_which_implies_wit_7 : OSQPostOpt_which_implies_wit_7.
Proof.
  left; intros.
  prop_apply_p (q_post_opt_loop_context_facts__broadcast environment critical saved_local
    sg caller active_2 mask cpu_sr before acquired_2 eid observed initial message state node).
  Intros.
  pose proof H as [_ [Hprofile [Heid _]]].
  pose proof (proj1 (proj2 (proj1 (proj2 Hprofile) eid Heid))) as Hgroupaddr.
  subst pe; rewrite Hgroupaddr.
  Exists active_2 acquired_2 state.
  apply (q_post_opt_loop_restore environment critical saved_local sg caller active_2 mask cpu_sr
    before acquired_2 (event_addr sg eid) eid observed initial message options state node);
    assumption.
Qed.

Lemma proof_of_OSQPostOpt_which_implies_wit_8 : OSQPostOpt_which_implies_wit_8.
Proof.
  left; intros; subst pevent.
  unfold q_post_group_context; Intros.
  destruct H as [Hacquire [Hprofile Heid]].
  pose proof Hacquire as [Hsave [Hbefore [Hbeforetype [Hnode [Htype Hgeneration]]]]].
  pose proof (proj1 Hsave) as Hvalid.
  pose proof (proj1 (proj2 Hprofile) eid Heid) as Hlayout.
  rewrite (proj1 (proj2 Hlayout)).
  sep_apply (q_post_group_cell_merge sg acquired_2 eid current_2 Hvalid Hnode).
  sep_apply (q_post_wake_split sg acquired_2 eid current_2 Hvalid Hnode Htype PreH2 Hlayout).
  Intros tid old.
  Exists active_2 acquired_2 current_2 tid old.
  unfold q_post_wake_context, q_post_sched_group, q_post_sched_rows; entailer!.
Qed.

Lemma proof_of_OSQPostOpt_which_implies_wit_9 : OSQPostOpt_which_implies_wit_9.
Proof.
  left; intros.
  unfold q_post_wake_context; Intros.
  destruct H as [Hacquire [Hprofile [Heid [Hgroup Hentry]]]].
  pose proof Hacquire as [Hsave [Hbefore [Hbeforetype [Hnode [Htype Hgeneration]]]]].
  pose proof (proj1 Hsave) as Hvalid.
  pose proof (q_post_acquire_original_type environment critical sg caller active_2 mask cpu_sr
    before acquired_2 eid observed current Hacquire) as Horiginaltype.
  unfold q_post_sched_group, q_post_sched_rows.
  sep_apply (q_post_wake_merge sg acquired_2 eid current tid old message priority
    Hvalid Hnode Htype Hentry).
  Intros after.
  pose proof (q_post_opt_single_wake_critical sg acquired_2 eid current message options priority after
    Hnode Hgroup PreH2 H) as Hcritical.
  destruct (q_post_wake_decompose sg acquired_2 eid current message priority after
    Hvalid Hnode Htype Hgroup H)
    as [selected [tail [previous [Hlist [Hold [Hpriority [Hafter [Haftervalid Hafterlookup]]]]]]]].
  subst after.
  sep_apply (q_post_mask_frame_wake_update environment critical saved_local sg active_2 cpu_sr
    acquired_2 acquired_2 eid current selected previous message Hold).
  Exists active_2 acquired_2
    (cross_module_invariants.event_wake_state sg acquired_2 eid current selected previous PendQ message PendOK).
  assert (Heffect : q_post_opt_effect sg eid message options acquired_2 0
    (q_post_opt_schedule_flag options)
    (cross_module_invariants.event_wake_state sg acquired_2 eid current selected previous PendQ message PendOK)).
  { exists error_codes.OS_ERR_NONE, (Z.eqb (Z.land options 4) 0).
    split; [reflexivity|]; split; [reflexivity|exact Hcritical]. }
  unfold q_post_opt_restore_pre; rewrite q_post_masked_equiv; entailer!.
Qed.

Lemma proof_of_OSQPostOpt_which_implies_wit_10 : OSQPostOpt_which_implies_wit_10.
Proof.
  left; intros.
  unfold q_post_opt_schedule_flag; rewrite PreH1; cbn.
  apply q_post_opt_restored_schedule_pre; exact PreH2.
Qed.

Lemma proof_of_OSQPostOpt_which_implies_wit_11 : OSQPostOpt_which_implies_wit_11.
Proof.
  left; intros; subst pevent.
  unfold q_post_group_context; Intros.
  destruct H as [Hacquire [Hprofile Heid]].
  pose proof Hacquire as [Hsave [Hbefore [Hbeforetype [Hnode [Htype Hgeneration]]]]].
  pose proof (proj1 Hsave) as Hvalid.
  pose proof (proj1 (proj2 Hprofile) eid Heid) as Hlayout.
  rewrite (proj1 (proj2 Hlayout)), (proj1 (proj2 (proj1 Hlayout))).
  sep_apply (q_post_group_cell_merge sg acquired_2 eid current_2 Hvalid Hnode).
  destruct (q_post_queue_current sg acquired_2 eid current_2 Hvalid Hnode Htype PreH2)
    as [q [Hq [Hempty Hqvalid]]].
  sep_apply (q_post_pointer_split sg acquired_2 eid current_2 q Hnode Htype Hq).
  Exists active_2 acquired_2 current_2 q.
  unfold q_post_pointer_context; entailer!.
Qed.

Lemma proof_of_OSQPostOpt_which_implies_wit_12 : OSQPostOpt_which_implies_wit_12.
Proof.
  left; intros; subst pq pevent.
  unfold q_post_pointer_context; Intros.
  destruct H as [Hacquire [Hprofile [Heid [Hgroup [Hq [Hempty Hqvalid]]]]]].
  pose proof Hacquire as [Hsave [Hbefore [Hbeforetype [Hnode [Htype Hgeneration]]]]].
  pose proof (proj1 Hsave) as Hvalid.
  pose proof (proj1 (proj2 Hprofile) eid Heid) as Hlayout.
  rewrite (proj1 (proj2 (proj1 Hlayout))).
  sep_apply (q_post_pointer_merge sg acquired_2 eid current_2 q_2 Hvalid Hnode Htype Hq).
  sep_apply (q_post_queue_split sg acquired_2 eid current_2 q_2 Hnode Htype Hq Hempty).
  Intros free slots.
  pose proof (queue_core.queue_entries_in_range sg nil q_2 Hqvalid) as Hcount.
  pose proof (proj1 Hqvalid) as Hqid.
  pose proof (proj1 (proj2 (proj2 Hqvalid))) as Hsize.
  rewrite (q_post_opt_qcb_cells_equiv sg q_2 Hprofile Hqid).
  Exists active_2 acquired_2 current_2 free slots q_2.
  unfold q_post_opt_qcb_cells, q_post_store_context; entailer!.
Qed.

Lemma proof_of_OSQPostOpt_which_implies_wit_13 : OSQPostOpt_which_implies_wit_13.
Proof.
  left; intros.
  unfold q_post_store_context; Intros.
  destruct H as [Hacquire [Hprofile [Hgroup [Hbase Hqueue]]]].
  subst pq.
  pose proof Hacquire as [Hsave [Hbefore [Hbeforetype [Hnode [Htype Hgeneration]]]]].
  pose proof Hqueue as [Hvalid [Hlookup [Hqtype [Hq [Hempty [Hqvalid Hrest]]]]]].
  pose proof (q_post_acquire_original_type environment critical sg caller active_2 mask cpu_sr
    before acquired_2 eid observed current Hacquire) as Horiginaltype.
  pose proof (q_post_opt_full_critical sg acquired_2 eid current q message options
    Hnode Hq Hgroup ltac:(lia)) as Hcritical.
  pose proof (proj2 (q_post_opt_qcb_cells_equiv sg q Hprofile (proj1 Hqvalid))) as Hcells.
  unfold q_post_opt_qcb_cells in Hcells.
  sep_apply Hcells.
  sep_apply (q_post_queue_merge_original sg acquired_2 eid current q free slots Hqueue).
  Exists active_2 acquired_2.
  assert (Heffect : q_post_opt_effect sg eid message options acquired_2 30 0 acquired_2).
  { exists error_codes.OS_ERR_Q_FULL, false.
    split; [reflexivity|]; split; [reflexivity|exact Hcritical]. }
  unfold q_post_opt_restore_pre; rewrite q_post_masked_equiv; entailer!.
Qed.

Lemma proof_of_OSQPostOpt_which_implies_wit_14 : OSQPostOpt_which_implies_wit_14.
Proof.
  unfold OSQPostOpt_which_implies_wit_14; left; intros.
  Exists active_2 acquired_2 current_2 free_2 slots_2 q_2.
  unfold q_post_store_context; Intros.
  assert (Hvalid : queue_fields_consistency sg nil q_2)
    by (unfold q_post_queue_facts in *; tauto).
  pose proof (q_post_nonfull_bounds sg q_2 Hvalid PreH1) as [_ [_ [Hcount Hin]]].
  pose proof (q_post_opt_front_nonfull_bounds sg q_2 Hvalid PreH1) as [_ [_ [_ Hout]]].
  entailer!.
Qed.

Lemma proof_of_OSQPostOpt_which_implies_wit_15 : OSQPostOpt_which_implies_wit_15.
Proof.
  unfold OSQPostOpt_which_implies_wit_15; left; intros.
  Exists active_2 acquired_2 current_2 q_2 free_2 slots_2.
  unfold q_post_store_context; Intros.
  assert (Hvalid : queue_fields_consistency sg nil q_2)
    by (unfold q_post_queue_facts in *; tauto).
  sep_apply (q_post_opt_front_slot_split sg q_2 slots_2 Hvalid PreH1).
  unfold q_post_opt_front_slot_frame; entailer!.
Qed.

Lemma proof_of_OSQPostOpt_which_implies_wit_16 : OSQPostOpt_which_implies_wit_16.
Proof.
  unfold OSQPostOpt_which_implies_wit_16; left; intros.
  Exists active_2 acquired_2 current_2 q_2 free_2 slots_2.
  unfold q_post_store_context; Intros.
  assert (Hvalid : queue_fields_consistency sg nil q_2)
    by (unfold q_post_queue_facts in *; tauto).
  sep_apply (q_post_slot_split sg q_2 slots_2 Hvalid PreH1).
  unfold q_post_slot_frame; entailer!.
Qed.

Lemma proof_of_OSQPostOpt_which_implies_wit_17 : OSQPostOpt_which_implies_wit_17.
Proof.
  unfold OSQPostOpt_which_implies_wit_17; left; intros.
  unfold q_post_store_context; Intros.
  assert (Hacq : q_post_acquire_facts environment critical sg caller active_2 mask cpu_sr
    before acquired_2 eid observed current) by tauto.
  assert (Hprofile : q_post_profile sg) by tauto.
  assert (Hgroup : q_post_group acquired_2 current = 0) by tauto.
  assert (Hbase : pq = qcb_addr sg (qID q)) by tauto.
  assert (Hfacts : q_post_queue_facts sg acquired_2 eid current q free slots) by tauto.
  pose proof Hfacts as [Hvalid [Hlookup [Htype [Hq [Hempty [Hqvalid
    [Hbinding [Hpart [Hslots Hmodel]]]]]]]]].
  pose proof (q_post_opt_enqueue_critical sg acquired_2 eid current q message options slots
    Hlookup Hq Hgroup Hslots PreH2) as Hstep.
  pose proof (q_post_critical_preserves_validity sg (QueuePostOptions options) acquired_2
    eid current message _ _ Hvalid Hlookup Htype Hstep) as Hafter.
  pose proof (q_post_acquire_original_type _ _ _ _ _ _ _ _ _ _ _ _ Hacq) as Horiginal.
  assert (Heffect : q_post_opt_effect sg eid message options acquired_2 0 0
    (q_post_opt_enqueue_state options acquired_2 eid current q message slots)).
  { exists error_codes.OS_ERR_NONE, false; auto. }
  rewrite Hbase.
  pose proof (proj1 (q_post_opt_qcb_enqueued_equiv sg options q message Hprofile
    (proj1 Hqvalid))) as Hcells.
  unfold q_post_opt_qcb_cells in Hcells; sep_apply Hcells.
  sep_apply (q_post_opt_enqueue_merge sg options acquired_2 eid current q free slots message Hfacts PreH2).
  sep_apply (q_post_mask_frame_event_update environment critical saved_local sg active_2 cpu_sr
    acquired_2 acquired_2 (q_post_opt_enqueue_state options acquired_2 eid current q message slots) eq_refl).
  Exists active_2 acquired_2 (q_post_opt_enqueue_state options acquired_2 eid current q message slots).
  unfold q_post_opt_restore_pre; rewrite q_post_masked_equiv; entailer!.
  unfold q_post_acquire_facts in Hacq; tauto.
Qed.

