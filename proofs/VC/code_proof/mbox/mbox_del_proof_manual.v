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
From Ucos2Verify.VC.code.mbox Require Import mbox_del_goal.
From Ucos2Verify.VC.code.mbox Require Import mbox_del_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_del_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSMboxDel_entail_wit_1 : OSMboxDel_entail_wit_1.
Proof.
  unfold OSMboxDel_entail_wit_1; left; intros.
  prop_apply_p (store_uchar_range (&((pe) # "os_event" ->ₛ "OSEventType"))
    (event_slot_type_value (EventState before) eid)).
  Intros.
  change (0 <= event_slot_type_value (EventState before) eid <= 255) in H.
  entailer!; lia.
Qed. 

Lemma proof_of_OSMboxDel_entail_wit_2 : OSMboxDel_entail_wit_2.
Proof.
  unfold OSMboxDel_entail_wit_2; left; intros.
  prop_apply_p (store_uchar_range (&("OSIntNesting")) (q_del_int_nesting before)).
  Intros.
  change (0 <= q_del_int_nesting before <= 255) in H.
  entailer!; lia.
Qed. 

Lemma proof_of_OSMboxDel_entail_wit_3_1 : OSMboxDel_entail_wit_3_1.
Proof.
  left; intros.
  assert (Hnonzero : q_post_group acquired_2 initial_2 <> 0).
  { intro Hzero; rewrite Hzero in PreH1; apply PreH1; reflexivity. }
  assert (Hwaiting : 1 = q_del_waiting acquired_2 initial_2).
  { unfold q_del_waiting; rewrite (proj2 (Z.eqb_neq _ _) Hnonzero); reflexivity. }
  Exists active_2 acquired_2 initial_2.
  subst pe opt_pre; entailer!.
Qed.

Lemma proof_of_OSMboxDel_entail_wit_3_2 : OSMboxDel_entail_wit_3_2.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp"))
    (q_post_group acquired_2 initial_2)); Intros.
  assert (Hrange : 0 <= q_post_group acquired_2 initial_2 < 2 ^ 32).
  { change (0 <= q_post_group acquired_2 initial_2 <= 255) in H; lia. }
  rewrite (unsigned_last_nbits_eq _ _ Hrange) in PreH1.
  assert (Hwaiting : 0 = q_del_waiting acquired_2 initial_2).
  { unfold q_del_waiting; rewrite PreH1; reflexivity. }
  Exists active_2 acquired_2 initial_2.
  subst pe opt_pre; entailer!.
Qed.

Lemma proof_of_OSMboxDel_entail_wit_7_1 : OSMboxDel_entail_wit_7_1.
Proof.
  right; intros.
  unfold mbox_del_after_schedule_context.
  Left; entailer!.
Qed.

Lemma proof_of_OSMboxDel_entail_wit_7_2 : OSMboxDel_entail_wit_7_2.
Proof.
  right; intros.
  assert (Hwaiting : tasks_waiting <> 1).
  { intro Heq; subst tasks_waiting; apply PreH1; reflexivity. }
  unfold mbox_del_after_schedule_context.
  Right; subst pe choice; entailer!.
Qed.

Lemma proof_of_OSMboxDel_return_wit_1 : OSMboxDel_return_wit_1.
Proof.
  left; intros.
  unfold mbox_pend_abort_output_address in PreH1; subst perr.
  apply mbox_del_finish_return; exact PreH2.
Qed.

Lemma proof_of_OSMboxDel_return_wit_2 : OSMboxDel_return_wit_2.
Proof.
  unfold OSMboxDel_return_wit_2; left; intros.
  pose proof (proj1 PreH11) as Hintaddr.
  rewrite Hintaddr.
  sep_apply_l_atomic (q_del_interrupt_merge environment critical saved_local sg caller mask before PreH8).
  assert (Hresult : mbox_del_caller_result environment critical sg caller mask pe eid choice before
    pe 15 caller before).
  { exists caller, before, false; split; [|split; reflexivity].
    unfold mbox_del_prefix_program.
    assert (Hpositive : 0 < q_del_int_nesting before) by lia.
    rewrite (proj2 (Z.eqb_neq _ _) PreH5), PreH10,
      (proj2 (Z.ltb_lt 0 (q_del_int_nesting before)) Hpositive); cbn; auto. }
  unfold mbox_pend_abort_output_address in PreH25; rewrite PreH25.
  apply (mbox_del_closed_return environment critical saved_local sg caller caller mask
    pe eid choice before before error_addr pe 15 X Hresult PreH31).
Qed. 

Lemma proof_of_OSMboxDel_return_wit_3 : OSMboxDel_return_wit_3.
Proof.
  unfold OSMboxDel_return_wit_3; left; intros.
  assert (Htypeaddr : (&((pe) # "os_event" ->ₛ "OSEventType")) =
    event_addr sg eid + OSEventType_off).
  { rewrite PreH6; exact (proj1 (mbox_del_event_layout sg eid PreH9 PreH8)). }
  rewrite Htypeaddr.
  sep_apply_l_atomic (mbox_post_type_merge environment critical saved_local sg caller mask before eid PreH10).
  assert (Hresult : mbox_del_caller_result environment critical sg caller mask pe eid choice before
    pe 1 caller before).
  { exists caller, before, false; split; [|split; reflexivity].
    unfold mbox_del_prefix_program.
    rewrite (proj2 (Z.eqb_neq _ _) PreH7), (proj2 (Z.eqb_neq _ _) PreH1); auto. }
  unfold mbox_pend_abort_output_address in PreH14; rewrite PreH14.
  apply (mbox_del_closed_return environment critical saved_local sg caller caller mask
    pe eid choice before before error_addr pe 1 X Hresult PreH20).
Qed. 

Lemma proof_of_OSMboxDel_return_wit_4 : OSMboxDel_return_wit_4.
Proof.
  unfold OSMboxDel_return_wit_4; left; intros.
  assert (Hpe : pe = 0) by lia.
  assert (Hresult : mbox_del_caller_result environment critical sg caller mask pe eid choice before
    pe 4 caller before).
  { exists caller, before, false; split; [|split; reflexivity].
    unfold mbox_del_prefix_program; rewrite Hpe; cbn; auto. }
  unfold mbox_pend_abort_output_address in PreH3; rewrite PreH3, PreH2.
  apply (mbox_del_closed_return environment critical saved_local sg caller caller mask
    pe eid choice before before error_addr pe 4 X Hresult PreH9).
Qed. 

Lemma proof_of_OSMboxDel_partial_solve_wit_7_pure : OSMboxDel_partial_solve_wit_7_pure.
Proof.
  left; intros.
  unfold q_del_waiting in *.
  destruct (Z.eqb (q_post_group acquired initial) 0);
    rewrite unsigned_last_nbits_eq in PreH1 by (cbn; lia);
    entailer!; lia.
Qed.

Lemma proof_of_OSMboxDel_partial_solve_wit_11_pure : OSMboxDel_partial_solve_wit_11_pure.
Proof.
  left; intros.
  unfold q_del_waiting in *.
  destruct (Z.eqb (q_post_group acquired initial) 0);
    rewrite unsigned_last_nbits_eq in PreH1 by (cbn; lia);
    entailer!; lia.
Qed.

Lemma proof_of_OSMboxDel_partial_solve_wit_14_pure : OSMboxDel_partial_solve_wit_14_pure.
Proof.
  left; intros.
  assert (Hnonzero : q_post_group state node <> 0).
  { intro Hzero; rewrite Hzero in PreH1; apply PreH1; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSMboxDel_partial_solve_wit_15_pure : OSMboxDel_partial_solve_wit_15_pure.
Proof.
  left; intros.
  unfold os_sched_global_addresses, sched_new_global_addresses in PreH9.
  entailer!; tauto.
Qed.

Lemma proof_of_OSMboxDel_partial_solve_wit_17_pure : OSMboxDel_partial_solve_wit_17_pure.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range
    (&((pe) # "os_event" ->ₛ "OSEventGrp")) (q_post_group state node)); Intros.
  assert (Hrange : 0 <= q_post_group state node < 2 ^ 32).
  { change (0 <= q_post_group state node <= 255) in H; lia. }
  rewrite (unsigned_last_nbits_eq _ _ Hrange) in PreH1.
  entailer!.
Qed.

Lemma proof_of_OSMboxDel_partial_solve_wit_20_pure : OSMboxDel_partial_solve_wit_20_pure.
Proof.
  left; intros.
  unfold mbox_del_restore_post; Intros returned current.
  destruct H as [[request [Hrequest Hprefix]] Hvalid].
  destruct request; cbn in Hrequest; subst tasks_waiting.
  - entailer!.
  - cbn in PreH1; discriminate.
Qed.

Lemma proof_of_OSMboxDel_partial_solve_wit_26_pure : OSMboxDel_partial_solve_wit_26_pure.
Proof.
  left; intros.
  prop_apply (store_uchar_range (&("opt")) choice).
  Intros.
  entailer!.
Qed.

Lemma proof_of_OSMboxDel_which_implies_wit_1 : OSMboxDel_which_implies_wit_1.
Proof.
  unfold OSMboxDel_which_implies_wit_1; left; intros.
  pose proof PreH4 as Hinput.
  destruct Hinput as [Hzero|[_ [Haddr [Hid Hpublic]]]]; [contradiction|].
  assert (Htypeaddr : (&((pe) # "os_event" ->ₛ "OSEventType")) =
    event_addr sg eid + OSEventType_off).
  { rewrite Haddr; exact (proj1 (mbox_del_event_layout sg eid PreH2 Hid)). }
  rewrite Htypeaddr.
  sep_apply_l_atomic (mbox_del_type_split environment critical saved_local sg caller mask before pe eid observed
    PreH3 PreH1 PreH4).
  entailer!.
Qed. 

Lemma proof_of_OSMboxDel_which_implies_wit_2 : OSMboxDel_which_implies_wit_2.
Proof.
  unfold OSMboxDel_which_implies_wit_2; right; intros.
  assert (Htypeaddr : (&((pe) # "os_event" ->ₛ "OSEventType")) =
    event_addr sg eid + OSEventType_off).
  { rewrite PreH1; exact (proj1 (mbox_del_event_layout sg eid PreH4 PreH3)). }
  rewrite Htypeaddr.
  sep_apply_l_atomic (mbox_post_type_merge environment critical saved_local sg caller mask before eid PreH5).
  pose proof (proj1 PreH8) as Hintaddr; rewrite Hintaddr.
  apply q_del_interrupt_split; exact PreH5.
Qed. 

Lemma proof_of_OSMboxDel_which_implies_wit_3 : OSMboxDel_which_implies_wit_3.
Proof.
  unfold OSMboxDel_which_implies_wit_3; right; intros.
  pose proof (proj1 PreH9) as Hintaddr; rewrite Hintaddr.
  sep_apply_l_atomic (q_del_interrupt_merge environment critical saved_local sg caller mask before PreH5).
  pose proof (mbox_del_call_input_acquire critical sg caller pe before eid observed
    PreH2 PreH7 PreH8 PreH6) as Hacquire.
  unfold mbox_pend_abort_save_pre; entailer!.
Qed. 

Lemma proof_of_OSMboxDel_which_implies_wit_4 : OSMboxDel_which_implies_wit_4.
Proof.
  left; intros.
  unfold mbox_pend_abort_save_result; Intros active acquired initial.
  pose proof H as [Hsave [_ [_ [Hnode _]]]].
  destruct (mbox_del_event_layout sg eid PreH3 PreH2) as [_ [_ [_ Hgrp]]].
  rewrite q_post_masked_equiv.
  sep_apply_l_atomic (q_post_group_cell_split sg acquired eid initial Hnode); Intros.
  Exists active acquired initial.
  rewrite PreH1, Hgrp.
  unfold mbox_pend_abort_group_context; entailer!.
Qed.

Lemma proof_of_OSMboxDel_which_implies_wit_5 : OSMboxDel_which_implies_wit_5.
Proof.
  left; intros.
  unfold mbox_pend_abort_group_context; Intros.
  destruct H as [Hacquire [Hprofile Heid]].
  pose proof Hacquire as [[Hvalid _] [_ [_ [Hnode [Htype _]]]]].
  pose proof (mbox_pend_abort_progress_initial sg eid acquired_2) as Hprogress.
  assert (Hfacts : mbox_del_loop_facts environment critical sg caller active_2 mask cpu_sr
    before acquired_2 eid observed initial_2 acquired_2 initial_2 nil tasks_waiting).
  { unfold mbox_del_loop_facts; tauto. }
  Exists active_2 acquired_2 initial_2.
  unfold mbox_del_loop_group_context; entailer!.
Qed.

Lemma proof_of_OSMboxDel_which_implies_wit_6 : OSMboxDel_which_implies_wit_6.
Proof.
  left; intros.
  unfold mbox_del_loop_group_context at 1; Intros.
  pose proof H as [Hacquire [Hprofile [Heid [Hint [Hwaiting Hrest]]]]].
  assert (Hzero : q_post_group acquired_2 initial_2 = 0).
  { unfold q_del_waiting in Hwaiting.
    destruct (Z.eqb (q_post_group acquired_2 initial_2) 0) eqn:Hgroup;
      [apply Z.eqb_eq; exact Hgroup|lia]. }
  assert (Hwaitingzero : tasks_waiting = 0).
  { rewrite Hwaiting; unfold q_del_waiting; rewrite Hzero; reflexivity. }
  Exists active_2 acquired_2 initial_2.
  rewrite PreH1, PreH5.
  pose proof (mbox_del_group_split_recycle environment critical saved_local
    sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2
    acquired_2 initial_2 nil tasks_waiting choice Hzero ltac:(left; auto)) as Hsplit.
  entailer!.
  match type of Hsplit with
  | ?P |-- _ =>
      match goal with
      | |- _ |-- ?Q =>
          assert (Hsplit_normalized : P |-- Q) by (sep_apply_l_atomic Hsplit; entailer!)
      end
  end.
  sep_apply_r_atomic Hsplit_normalized.
  unfold mbox_del_loop_group_context; entailer!.
Qed.

Lemma proof_of_OSMboxDel_which_implies_wit_7 : OSMboxDel_which_implies_wit_7.
Proof.
  left; intros.
  unfold mbox_del_recycle_context at 1; Intros.
  pose proof H as [Hfacts [Hnone [Hempty Hoption]]].
  pose proof Hfacts as [_ [_ [_ [_ [Hwaiting Hrest]]]]].
  assert (Hwaitingzero : tasks_waiting = 0).
  { rewrite Hwaiting; unfold q_del_waiting, q_post_group.
    rewrite Hempty; reflexivity. }
  subst tasks_waiting.
  rewrite Hwaitingzero in *.
  Exists active_2 acquired_2 (event_delete_recycle_state sg acquired_2 eid initial).
  rewrite PreH3.
  sep_apply_r_atomic (mbox_del_recycle_restore environment critical saved_local
    sg caller active_2 mask cpu_sr pe before acquired_2 eid observed initial
    acquired_2 initial nil 0 choice PreH1 PreH2).
  unfold mbox_del_recycle_context; entailer!.
Qed.

Lemma proof_of_OSMboxDel_which_implies_wit_8 : OSMboxDel_which_implies_wit_8.
Proof.
  left; intros; apply mbox_del_nonschedule_finish; lia.
Qed.

Lemma proof_of_OSMboxDel_which_implies_wit_9 : OSMboxDel_which_implies_wit_9.
Proof.
  left; intros.
  unfold mbox_del_loop_group_context; Intros.
  destruct H as [Hacquire [Hprofile [Heid [Hint [Hwaiting [Hvalid [Hnode [Htype Hprogress]]]]]]]].
  assert (Hgroup : q_post_group acquired_2 initial <> 0).
  { intro Hzero; apply PreH4; rewrite Hwaiting; unfold q_del_waiting; rewrite Hzero; reflexivity. }
  pose proof (mbox_pend_abort_acquire_original_type _ _ _ _ _ _ _ _ _ _ _ _ Hacquire) as Hbeforetype.
  pose proof (proj1 Hacquire) as Hsave.
  assert (Heffect : mbox_del_effect sg eid choice acquired_2 pe 73 0 acquired_2).
  { subst choice; unfold mbox_del_effect.
    exists Ucos2Verify.lib.error_codes.OS_ERR_TASK_WAITING, false;
      split; [reflexivity|]; split; [reflexivity|].
    unfold mbox_delete_critical, event_delete_critical.
    exists initial; split; [exact Hnode|].
    rewrite (unsigned_last_nbits_eq 0 8 ltac:(cbn; lia)).
    cbn; fold (q_post_group acquired_2 initial).
    rewrite (proj2 (Z.eqb_neq _ _) Hgroup); cbn; split; [rewrite PreH1; reflexivity|reflexivity]. }
  destruct (mbox_del_event_layout sg eid Hprofile Heid) as [_ [_ [_ Hgrpaddr]]].
  rewrite PreH1 at 1; rewrite Hgrpaddr.
  sep_apply_l_atomic (q_post_group_cell_merge sg acquired_2 eid initial Hvalid Hnode).
  Exists active_2 acquired_2.
  unfold mbox_del_restore_pre; rewrite q_post_masked_equiv; entailer!.
Qed.

Lemma proof_of_OSMboxDel_which_implies_wit_10 : OSMboxDel_which_implies_wit_10.
Proof.
  left; intros; apply mbox_del_nonschedule_finish; lia.
Qed.

Lemma proof_of_OSMboxDel_which_implies_wit_11 : OSMboxDel_which_implies_wit_11.
Proof.
  left; intros.
  unfold mbox_del_loop_group_context; Intros.
  pose proof H as [Hacquire [Hprofile [Heid [Hint [Hwaiting [Hvalid [Hnode [Htype Hprogress]]]]]]]].
  destruct (mbox_del_event_layout sg eid Hprofile Heid) as [_ [_ [_ Hgrp]]].
  assert (Hlayout : event_object_layout_prop sg eid).
  { exact (proj2 Hprofile eid Heid). }
  rewrite PreH1, Hgrp.
  sep_apply_l_atomic (q_post_group_cell_merge sg state_2 eid node_2 Hvalid Hnode).
  sep_apply_l_atomic (mbox_pend_abort_wake_split sg state_2 eid node_2 Hvalid Hnode Htype PreH2 Hlayout).
  Intros tid old.
  Exists active_2 acquired_2 initial_2 state_2 node_2 processed_2 tid old.
  unfold mbox_del_loop_wake_context; entailer!.
Qed.

Lemma proof_of_OSMboxDel_which_implies_wit_12 : OSMboxDel_which_implies_wit_12.
Proof.
  left; intros.
  unfold mbox_del_loop_wake_context; Intros.
  destruct H as [Hfacts [Hnonzero Hentry]].
  pose proof Hfacts as [Hacquire [Hprofile [Heid [Hint [Hwaiting [Hvalid [Hnode [Htype Hprogress]]]]]]]].
  pose proof Hentry as [_ [_ [_ [_ [_ [Hhead Hold]]]]]].
  destruct (EventStateDef.waitList node) as [|head tail] eqn:Hlist; [discriminate|].
  inversion Hhead; subst head.
  destruct (event_wake_spec.event_wake_head sg state eid node tid tail PendMbox 0 PendAbort
    Hvalid Hnode ltac:(rewrite Htype; reflexivity) Hlist)
    as [found [Hfound [Hstep [Hnext Hnextnode]]]].
  assert (found = old) by congruence; subst found.
  sep_apply_l_atomic (mbox_pend_abort_mask_frame_wake_update environment critical saved_local sg
    active_2 cpu_sr acquired_2 state eid node tid old Hold).
  sep_apply_l_atomic (mbox_pend_abort_wake_merge sg state eid node tid old priority
    Hvalid Hnode Htype Hentry); Intros.
  assert (Hprogress_next : mbox_pend_abort_progress sg eid acquired_2
    (cross_module_invariants.event_wake_state sg state eid node tid old PendMbox 0 PendAbort)
    (processed ++ priority :: nil)).
  { eapply mbox_pend_abort_progress_step; eassumption. }
  assert (Hfacts_next : mbox_del_loop_facts environment critical sg caller active_2 mask cpu_sr
    before acquired_2 eid observed initial_2
    (cross_module_invariants.event_wake_state sg state eid node tid old PendMbox 0 PendAbort)
    (event_wait.event_set_wait_list node tail) (processed ++ priority :: nil) tasks_waiting).
  { unfold mbox_del_loop_facts; simpl; tauto. }
  sep_apply_l_atomic (q_post_group_cell_split sg
    (cross_module_invariants.event_wake_state sg state eid node tid old PendMbox 0 PendAbort)
    eid (event_wait.event_set_wait_list node tail) Hnextnode); Intros.
  Exists active_2 acquired_2 initial_2
    (cross_module_invariants.event_wake_state sg state eid node tid old PendMbox 0 PendAbort)
    (event_wait.event_set_wait_list node tail) (processed ++ priority :: nil).
  destruct (mbox_del_event_layout sg eid Hprofile Heid) as [_ [_ [_ Hgrp]]].
  rewrite PreH1, Hgrp.
  unfold mbox_del_loop_group_context; entailer!.
Qed.

Lemma proof_of_OSMboxDel_which_implies_wit_13 : OSMboxDel_which_implies_wit_13.
Proof.
  left; intros.
  Exists active_2 acquired_2 initial_2 state_2 node_2 processed_2.
  rewrite PreH1, PreH5.
  sep_apply_l_atomic (mbox_del_group_split_recycle environment critical saved_local
    sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2
    state_2 node_2 processed_2 tasks_waiting choice PreH4 ltac:(right; exact PreH3)).
  entailer!.
Qed.

Lemma proof_of_OSMboxDel_which_implies_wit_14 : OSMboxDel_which_implies_wit_14.
Proof.
  left; intros.
  Exists active_2 acquired_2 (event_delete_recycle_state sg state eid node).
  rewrite PreH3.
  apply (mbox_del_recycle_restore environment critical saved_local
    sg caller active_2 mask cpu_sr pe before acquired_2 eid observed initial
    state node processed tasks_waiting choice PreH1 PreH2).
Qed.

Lemma proof_of_OSMboxDel_which_implies_wit_15 : OSMboxDel_which_implies_wit_15.
Proof.
  left; intros.
  unfold mbox_del_restore_post; Intros returned current.
  destruct H as [Hresult Hvalid].
  pose proof Hresult as [request [Hrequest Hprefix]].
  destruct request; cbn in Hrequest; [subst tasks_waiting|lia].
  sep_apply_r_atomic (mbox_del_restore_schedule environment critical saved_local sg caller mask
    pe eid choice before 0 0 PreH2).
  unfold mbox_del_restore_post; Exists returned current; entailer!.
Qed.

Lemma proof_of_OSMboxDel_which_implies_wit_16 : OSMboxDel_which_implies_wit_16.
Proof.
  left; intros; apply mbox_del_sched_finish; exact PreH1.
Qed.

Lemma proof_of_OSMboxDel_which_implies_wit_17 : OSMboxDel_which_implies_wit_17.
Proof.
  left; intros; unfold mbox_del_after_schedule_context.
  apply derivable1_orp_elim.
  - entailer!.
  - Intros; apply mbox_del_nonschedule_finish; assumption.
Qed.

Lemma proof_of_OSMboxDel_which_implies_wit_18 : OSMboxDel_which_implies_wit_18.
Proof.
  left; intros; apply mbox_del_nonschedule_finish; lia.
Qed.

Lemma proof_of_OSMboxDel_which_implies_wit_19 : OSMboxDel_which_implies_wit_19.
Proof.
  left; intros.
  unfold mbox_del_loop_group_context; Intros.
  destruct H as [Hacquire [Hprofile [Heid [Hint [Hwaiting [Hvalid [Hnode [Htype Hprogress]]]]]]]].
  pose proof (mbox_pend_abort_acquire_original_type _ _ _ _ _ _ _ _ _ _ _ _ Hacquire) as Hbeforetype.
  pose proof (proj1 Hacquire) as Hsave.
  assert (Heffect : mbox_del_effect sg eid choice acquired_2 pe 7 0 acquired_2).
  { unfold mbox_del_effect.
    exists Ucos2Verify.lib.error_codes.OS_ERR_INVALID_OPT, false;
      split; [reflexivity|]; split; [reflexivity|].
    unfold mbox_delete_critical, event_delete_critical.
    exists initial; split; [exact Hnode|].
    rewrite (unsigned_last_nbits_eq choice 8 ltac:(cbn; lia)).
    rewrite (proj2 (Z.eqb_neq _ _) PreH3), (proj2 (Z.eqb_neq _ _) PreH4).
    split; [rewrite PreH1; reflexivity|reflexivity]. }
  destruct (mbox_del_event_layout sg eid Hprofile Heid) as [_ [_ [_ Hgrpaddr]]].
  rewrite PreH1 at 1; rewrite Hgrpaddr.
  sep_apply_l_atomic (q_post_group_cell_merge sg acquired_2 eid initial Hvalid Hnode).
  Exists active_2 acquired_2.
  unfold mbox_del_restore_pre; rewrite q_post_masked_equiv; entailer!.
Qed.

