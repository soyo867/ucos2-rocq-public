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
From Ucos2Verify.VC.code.sem Require Import del_goal.
From Ucos2Verify.VC.code.sem Require Import del_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.sem.spec.sem_del_source_api_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSSemDel_entail_wit_1 : OSSemDel_entail_wit_1.
Proof.
  unfold OSSemDel_entail_wit_1; left; intros.
  prop_apply_p (store_uchar_range (&((pe) # "os_event" ->ₛ "OSEventType"))
    (event_slot_type_value (EventState before) eid)).
  Intros.
  change (0 <= event_slot_type_value (EventState before) eid <= 255) in H.
  entailer!; lia.
Qed. 

Lemma proof_of_OSSemDel_entail_wit_2 : OSSemDel_entail_wit_2.
Proof.
  unfold OSSemDel_entail_wit_2; left; intros.
  prop_apply_p (store_uchar_range (&("OSIntNesting")) (q_del_int_nesting before)).
  Intros.
  change (0 <= q_del_int_nesting before <= 255) in H.
  entailer!; lia.
Qed. 

Lemma proof_of_OSSemDel_entail_wit_3_1 : OSSemDel_entail_wit_3_1.
Proof.
  left; intros.
  assert (Hnonzero : q_post_group acquired_2 initial_2 <> 0).
  { intro Hzero; rewrite Hzero in PreH1; apply PreH1; reflexivity. }
  assert (Hwaiting : 1 = q_del_waiting acquired_2 initial_2).
  { unfold q_del_waiting; rewrite (proj2 (Z.eqb_neq _ _) Hnonzero); reflexivity. }
  Exists active_2 acquired_2 initial_2.
  subst pe opt_pre; entailer!.
Qed.

Lemma proof_of_OSSemDel_entail_wit_3_2 : OSSemDel_entail_wit_3_2.
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

Lemma proof_of_OSSemDel_entail_wit_7_1 : OSSemDel_entail_wit_7_1.
Proof.
  right; intros.
  unfold sem_del_source_api_after_schedule_context.
  Left; entailer!.
Qed.

Lemma proof_of_OSSemDel_entail_wit_7_2 : OSSemDel_entail_wit_7_2.
Proof.
  right; intros.
  assert (Hwaiting : tasks_waiting <> 1).
  { intro Heq; subst tasks_waiting; apply PreH1; reflexivity. }
  unfold sem_del_source_api_after_schedule_context.
  Right; subst pe choice; entailer!.
Qed.

Lemma proof_of_OSSemDel_return_wit_1 : OSSemDel_return_wit_1.
Proof.
  left; intros.
  unfold sem_del_source_api_output_address in PreH1; subst perr.
  apply sem_del_source_api_finish_return; exact PreH2.
Qed.

Lemma proof_of_OSSemDel_return_wit_2 : OSSemDel_return_wit_2.
Proof.
  unfold OSSemDel_return_wit_2; left; intros.
  match goal with H : os_sched_global_addresses _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof (proj1 H) as Hintaddr end.
  rewrite Hintaddr.
  sep_apply_l_atomic (q_del_interrupt_merge environment critical saved_local sg caller mask before ltac:(assumption)).
  assert (Hresult : sem_del_source_api_caller_result environment critical sg caller mask pe eid choice before
    pe 15 caller before).
  { apply sem_del_source_api_isr_result; try assumption; lia. }
  match goal with H : sem_del_source_api_output_address _ _ |- _ =>
    unfold sem_del_source_api_output_address in H; rewrite <- H end.
  apply (sem_del_source_api_closed_return environment critical saved_local sg caller caller mask
    pe eid choice before before error_addr pe 15 X Hresult ltac:(assumption)).
Qed. 

Lemma proof_of_OSSemDel_return_wit_3 : OSSemDel_return_wit_3.
Proof.
  unfold OSSemDel_return_wit_3; left; intros.
  assert (Htypeaddr : (&((pe) # "os_event" ->ₛ "OSEventType")) =
    event_addr sg eid + OSEventType_off).
  { rewrite PreH6; exact (proj1 (sem_del_source_api_event_layout sg eid ltac:(assumption))). }
  rewrite Htypeaddr.
  sep_apply_l_atomic (sem_del_source_api_type_merge environment critical saved_local sg caller mask before eid ltac:(assumption)).
  assert (Hresult : sem_del_source_api_caller_result environment critical sg caller mask pe eid choice before
    pe 1 caller before).
  { apply sem_del_source_api_wrong_type_result; assumption. }
  match goal with H : sem_del_source_api_output_address _ _ |- _ =>
    unfold sem_del_source_api_output_address in H; rewrite <- H end.
  apply (sem_del_source_api_closed_return environment critical saved_local sg caller caller mask
    pe eid choice before before error_addr pe 1 X Hresult ltac:(assumption)).
Qed. 

Lemma proof_of_OSSemDel_return_wit_4 : OSSemDel_return_wit_4.
Proof.
  unfold OSSemDel_return_wit_4; left; intros.
  assert (Hpe : pe = 0) by lia.
  assert (Hresult : sem_del_source_api_caller_result environment critical sg caller mask pe eid choice before
    pe 4 caller before).
  { rewrite Hpe; apply sem_del_source_api_null_result. }
  match goal with H : sem_del_source_api_output_address _ _ |- _ =>
    unfold sem_del_source_api_output_address in H; rewrite <- H end.
  rewrite PreH2.
  apply (sem_del_source_api_closed_return environment critical saved_local sg caller caller mask
    pe eid choice before before error_addr pe 4 X Hresult ltac:(assumption)).
Qed. 

Lemma proof_of_OSSemDel_return_wit_5 : OSSemDel_return_wit_5.
Proof.
  unfold OSSemDel_return_wit_5; left; intros.
  assert (Hpe : pe = 0) by lia.
  assert (Hresult : sem_del_source_api_caller_result environment critical sg caller mask pe eid choice before
    pe 4 caller before) by (rewrite Hpe; apply sem_del_source_api_null_result).
  match goal with H : sem_del_source_api_output_address _ _ |- _ =>
    unfold sem_del_source_api_output_address in H; rewrite <- H end.
  rewrite PreH2.
  apply (sem_del_source_api_closed_return environment critical saved_local sg caller caller mask
    pe eid choice before before error_addr pe 4 X Hresult ltac:(assumption)).
Qed.

Lemma proof_of_OSSemDel_partial_solve_wit_7_pure : OSSemDel_partial_solve_wit_7_pure.
Proof.
  left; intros.
  unfold q_del_waiting in *.
  destruct (Z.eqb (q_post_group acquired initial) 0);
    rewrite unsigned_last_nbits_eq in PreH1 by (cbn; lia);
    entailer!; lia.
Qed.

Lemma proof_of_OSSemDel_partial_solve_wit_11_pure : OSSemDel_partial_solve_wit_11_pure.
Proof.
  left; intros.
  unfold q_del_waiting in *.
  destruct (Z.eqb (q_post_group acquired initial) 0);
    rewrite unsigned_last_nbits_eq in PreH1 by (cbn; lia);
    entailer!; lia.
Qed.

Lemma proof_of_OSSemDel_partial_solve_wit_14_pure : OSSemDel_partial_solve_wit_14_pure.
Proof.
  left; intros.
  assert (Hnonzero : q_post_group state node <> 0).
  { intro Hzero; rewrite Hzero in PreH1; apply PreH1; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSSemDel_partial_solve_wit_15_pure : OSSemDel_partial_solve_wit_15_pure.
Proof.
  left; intros.
  unfold os_sched_global_addresses, sched_new_global_addresses in PreH9.
  entailer!; tauto.
Qed.

Lemma proof_of_OSSemDel_partial_solve_wit_17_pure : OSSemDel_partial_solve_wit_17_pure.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range
    (&((pe) # "os_event" ->ₛ "OSEventGrp")) (q_post_group state node)); Intros.
  assert (Hrange : 0 <= q_post_group state node < 2 ^ 32).
  { change (0 <= q_post_group state node <= 255) in H; lia. }
  rewrite (unsigned_last_nbits_eq _ _ Hrange) in PreH1.
  entailer!.
Qed.

Lemma proof_of_OSSemDel_partial_solve_wit_20_pure : OSSemDel_partial_solve_wit_20_pure.
Proof.
  left; intros.
  unfold sem_del_source_api_restore_post; Intros returned current.
  destruct H as [[request [Hrequest Hprefix]] Hvalid].
  destruct request; cbn in Hrequest; subst tasks_waiting.
  - entailer!.
  - cbn in PreH1; discriminate.
Qed.

Lemma proof_of_OSSemDel_partial_solve_wit_26_pure : OSSemDel_partial_solve_wit_26_pure.
Proof.
  left; intros.
  prop_apply (store_uchar_range (&("opt")) choice).
  Intros.
  entailer!.
Qed.

Lemma proof_of_OSSemDel_which_implies_wit_1 : OSSemDel_which_implies_wit_1.
Proof.
  unfold OSSemDel_which_implies_wit_1; left; intros.
  pose proof PreH5 as Hinput.
  destruct Hinput as [Hzero|[_ [Haddr [Hid Hpublic]]]]; [contradiction|].
  assert (Htypeaddr : (&((pe) # "os_event" ->ₛ "OSEventType")) =
    event_addr sg eid + OSEventType_off).
  { rewrite Haddr; exact (proj1 (sem_del_source_api_event_layout sg eid PreH2)). }
  rewrite Htypeaddr.
  sep_apply_l_atomic (sem_del_source_api_type_split environment critical saved_local sg caller mask before pe eid observed
    PreH4 PreH1 PreH5).
  entailer!.
Qed. 

Lemma proof_of_OSSemDel_which_implies_wit_2 : OSSemDel_which_implies_wit_2.
Proof.
  unfold OSSemDel_which_implies_wit_2; right; intros.
  assert (Htypeaddr : (&((pe) # "os_event" ->ₛ "OSEventType")) =
    event_addr sg eid + OSEventType_off).
  { rewrite PreH1; exact (proj1 (sem_del_source_api_event_layout sg eid PreH4)). }
  rewrite Htypeaddr.
  pose proof (proj1 PreH9) as Hintaddr; rewrite Hintaddr.
  apply (sem_del_source_api_type_to_interrupt environment critical saved_local sg caller mask before eid PreH6).
Qed. 

Lemma proof_of_OSSemDel_which_implies_wit_3 : OSSemDel_which_implies_wit_3.
Proof.
  unfold OSSemDel_which_implies_wit_3; right; intros.
  pose proof (proj1 PreH9) as Hintaddr; rewrite Hintaddr.
  apply sem_del_source_api_interrupt_to_save; assumption.
Qed. 

Lemma proof_of_OSSemDel_which_implies_wit_4 : OSSemDel_which_implies_wit_4.
Proof.
  left; intros.
  destruct (sem_del_source_api_event_layout sg eid PreH3) as [_ [_ [_ Hgrp]]].
  sep_apply_l_atomic (sem_del_source_api_save_group_split environment critical saved_local sg caller mask cpu_sr
    before eid observed PreH4 PreH2 PreH3); Intros active acquired initial.
  Exists active acquired initial.
  rewrite PreH1, Hgrp.
  entailer!.
Qed.

Lemma proof_of_OSSemDel_which_implies_wit_5 : OSSemDel_which_implies_wit_5.
Proof.
  left; intros.
  sep_apply_l_atomic (sem_del_source_api_acquired_loop_start environment critical saved_local sg caller active_2 mask cpu_sr
    before acquired_2 eid observed initial_2 tasks_waiting PreH2 PreH3).
  Exists active_2 acquired_2 initial_2.
  entailer!.
Qed.

Lemma proof_of_OSSemDel_which_implies_wit_6 : OSSemDel_which_implies_wit_6.
Proof.
  left; intros.
  unfold sem_del_source_api_loop_group_context at 1; Intros.
  pose proof H as [Hacquire [Hprofile [Heid [Hlayout [Hint [Hwaiting Hrest]]]]]].
  destruct (sem_del_source_api_event_layout sg eid Hlayout) as [Ht [Hp [Hc Hg]]].
  assert (Hzero : sem_del_group acquired_2 initial_2 = 0) by (destruct Hwaiting as [[? ?]|[? ?]]; lia).
  assert (Hwaitingzero : tasks_waiting = 0) by (destruct Hwaiting as [[? ?]|[? ?]]; lia).
  Exists active_2 acquired_2 initial_2.
  rewrite PreH1, PreH5, Ht, Hp, Hc, Hg.
  pose proof (sem_del_source_api_group_split_recycle environment critical saved_local
    sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2
    acquired_2 initial_2 tasks_waiting choice Hzero ltac:(left; auto)) as Hsplit.
  entailer!.
  match type of Hsplit with
  | ?P |-- _ =>
      match goal with
      | |- _ |-- ?Q =>
          assert (Hsplit_normalized : P |-- Q) by (sep_apply_l_atomic Hsplit; entailer!)
      end
  end.
  sep_apply_r_atomic Hsplit_normalized.
  unfold sem_del_source_api_loop_group_context; entailer!.
Qed.

Lemma proof_of_OSSemDel_which_implies_wit_7 : OSSemDel_which_implies_wit_7.
Proof.
  left; intros.
  unfold sem_del_source_api_recycle_context at 1; Intros.
  pose proof H as [Hfacts [Hzero Hoption]].
  pose proof Hfacts as [_ [_ [_ [Hlayout [_ [Hwaiting Hrest]]]]]].
  destruct (sem_del_source_api_event_layout sg eid Hlayout) as [Ht [Hp [Hc Hg]]].
  assert (Hwaitingzero : tasks_waiting = 0) by (destruct Hwaiting as [[? ?]|[? ?]]; congruence).
  subst tasks_waiting.
  Exists active_2 acquired_2 (event_delete_recycle_state sg acquired_2 eid initial).
  rewrite PreH1, PreH3, Ht, Hp, Hc.
  sep_apply_r_atomic (sem_del_source_api_recycle_restore environment critical saved_local
    sg caller active_2 mask cpu_sr (event_addr sg eid) before acquired_2 eid observed initial
    acquired_2 initial 0 choice eq_refl ltac:(lia)).
  unfold sem_del_source_api_recycle_context; entailer!.
Qed.

Lemma proof_of_OSSemDel_which_implies_wit_8 : OSSemDel_which_implies_wit_8.
Proof.
  left; intros; apply sem_del_source_api_nonschedule_finish; lia.
Qed.

Lemma proof_of_OSSemDel_which_implies_wit_9 : OSSemDel_which_implies_wit_9.
Proof.
  left; intros.
  unfold sem_del_source_api_loop_group_context at 1; Intros.
  pose proof H as [Hacquire [Hprofile [Heid [Hlayout [Hint [Hwaiting [Hprefix [Hnode [Htype Hvalid]]]]]]]]].
  assert (Hgroup : sem_del_group acquired_2 initial <> 0) by (destruct Hwaiting as [[? ?]|[? ?]]; lia).
  destruct (sem_del_source_api_event_layout sg eid Hlayout) as [_ [_ [_ Hgrpaddr]]].
  subst choice.
  rewrite PreH1, Hgrpaddr.
  Exists active_2 acquired_2.
  sep_apply_r_atomic (sem_del_source_api_unchanged_restore environment critical saved_local
    sg caller active_2 mask cpu_sr (event_addr sg eid) before acquired_2 eid observed initial tasks_waiting
    0 (event_addr sg eid) 73 eq_refl ltac:(lia) ltac:(lia)
    (sem_del_critical_no_pend_waiting sg acquired_2 eid initial Hnode Hgroup)).
  unfold sem_del_source_api_loop_group_context; entailer!.
Qed.

Lemma proof_of_OSSemDel_which_implies_wit_10 : OSSemDel_which_implies_wit_10.
Proof.
  left; intros; apply sem_del_source_api_nonschedule_finish; lia.
Qed.

Lemma proof_of_OSSemDel_which_implies_wit_11 : OSSemDel_which_implies_wit_11.
Proof.
  left; intros.
  unfold sem_del_source_api_loop_group_context at 1; Intros.
  pose proof H as [_ [_ [_ [Hlayout _]]]].
  destruct (sem_del_source_api_event_layout sg eid Hlayout) as [_ [_ [_ Hgrp]]].
  rewrite PreH1, Hgrp.
  pose proof (sem_del_source_api_loop_split_wake environment critical saved_local sg caller active_2 mask cpu_sr
    before acquired_2 eid observed initial_2 state_2 node_2 tasks_waiting PreH2) as Hsplit.
  match type of Hsplit with ?P |-- _ =>
    match goal with |- _ |-- ?Q =>
      assert (Hnormalized : P |-- Q) by
        (sep_apply_l_atomic Hsplit; Intros tid old;
         Exists active_2 acquired_2 initial_2 state_2 node_2 tid old; entailer!) end end.
  sep_apply_r_atomic Hnormalized; unfold sem_del_source_api_loop_group_context; entailer!.
Qed.

Lemma proof_of_OSSemDel_which_implies_wit_12 : OSSemDel_which_implies_wit_12.
Proof.
  left; intros.
  sep_apply_l_atomic (sem_del_source_api_loop_merge_wake environment critical saved_local sg caller active_2 mask cpu_sr
    before acquired_2 eid observed initial_2 state node tasks_waiting tid old priority).
  Intros next next_node.
  unfold sem_del_source_api_loop_group_context at 1; Intros.
  pose proof H as [_ [_ [_ [Hlayout _]]]].
  destruct (sem_del_source_api_event_layout sg eid Hlayout) as [_ [_ [_ Hgrp]]].
  Exists active_2 acquired_2 initial_2 next next_node.
  rewrite PreH1, Hgrp; unfold sem_del_source_api_loop_group_context; entailer!.
Qed.

Lemma proof_of_OSSemDel_which_implies_wit_13 : OSSemDel_which_implies_wit_13.
Proof.
  left; intros.
  unfold sem_del_source_api_loop_group_context at 1; Intros.
  pose proof H as [_ [_ [_ [Hlayout _]]]].
  destruct (sem_del_source_api_event_layout sg eid Hlayout) as [Ht [Hp [Hc Hg]]].
  Exists active_2 acquired_2 initial_2 state_2 node_2.
  rewrite PreH1, PreH5, Ht, Hp, Hc, Hg.
  pose proof (sem_del_source_api_group_split_recycle environment critical saved_local
    sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2
    state_2 node_2 tasks_waiting choice PreH4 ltac:(right; exact PreH3)) as Hsplit.
  entailer!.
  match type of Hsplit with ?P |-- _ =>
    match goal with |- _ |-- ?Q =>
      assert (Hnormalized : P |-- Q) by (sep_apply_l_atomic Hsplit; entailer!) end end.
  sep_apply_r_atomic Hnormalized; unfold sem_del_source_api_loop_group_context; entailer!.
Qed.

Lemma proof_of_OSSemDel_which_implies_wit_14 : OSSemDel_which_implies_wit_14.
Proof.
  left; intros.
  unfold sem_del_source_api_recycle_context at 1; Intros.
  pose proof H as [[_ [_ [_ [Hlayout _]]]] _].
  destruct (sem_del_source_api_event_layout sg eid Hlayout) as [Ht [Hp [Hc Hg]]].
  Exists active_2 acquired_2 (event_delete_recycle_state sg state eid node).
  rewrite PreH1, PreH3, Ht, Hp, Hc.
  sep_apply_r_atomic (sem_del_source_api_recycle_restore environment critical saved_local
    sg caller active_2 mask cpu_sr (event_addr sg eid) before acquired_2 eid observed initial
    state node tasks_waiting choice eq_refl ltac:(lia)).
  unfold sem_del_source_api_recycle_context; entailer!.
Qed.

Lemma proof_of_OSSemDel_which_implies_wit_15 : OSSemDel_which_implies_wit_15.
Proof.
  left; intros.
  unfold sem_del_source_api_restore_post; Intros returned current.
  destruct H as [Hresult Hvalid].
  pose proof Hresult as [request [Hrequest Hprefix]].
  destruct request; cbn in Hrequest; [subst tasks_waiting|lia].
  sep_apply_r_atomic (sem_del_source_api_restore_schedule environment critical saved_local sg caller mask
    pe eid choice before 0 0 PreH2).
  unfold sem_del_source_api_restore_post; Exists returned current; entailer!.
Qed.

Lemma proof_of_OSSemDel_which_implies_wit_16 : OSSemDel_which_implies_wit_16.
Proof.
  left; intros; apply sem_del_source_api_sched_finish; exact PreH1.
Qed.

Lemma proof_of_OSSemDel_which_implies_wit_17 : OSSemDel_which_implies_wit_17.
Proof.
  left; intros; unfold sem_del_source_api_after_schedule_context.
  apply derivable1_orp_elim.
  - entailer!.
  - Intros; apply sem_del_source_api_nonschedule_finish; assumption.
Qed.

Lemma proof_of_OSSemDel_which_implies_wit_18 : OSSemDel_which_implies_wit_18.
Proof.
  left; intros; apply sem_del_source_api_nonschedule_finish; lia.
Qed.

Lemma proof_of_OSSemDel_which_implies_wit_19 : OSSemDel_which_implies_wit_19.
Proof.
  left; intros.
  unfold sem_del_source_api_loop_group_context at 1; Intros.
  pose proof H as [Hacquire [Hprofile [Heid [Hlayout [Hint [Hwaiting [Hprefix [Hnode [Htype Hvalid]]]]]]]]].
  destruct (sem_del_source_api_event_layout sg eid Hlayout) as [_ [_ [_ Hgrpaddr]]].
  rewrite PreH1, Hgrpaddr.
  Exists active_2 acquired_2.
  sep_apply_r_atomic (sem_del_source_api_unchanged_restore environment critical saved_local
    sg caller active_2 mask cpu_sr (event_addr sg eid) before acquired_2 eid observed initial tasks_waiting
    choice (event_addr sg eid) 7 eq_refl ltac:(lia) ltac:(lia)
    (sem_del_critical_invalid_option sg acquired_2 eid initial choice Hnode PreH3 PreH4)).
  unfold sem_del_source_api_loop_group_context; entailer!.
Qed.

