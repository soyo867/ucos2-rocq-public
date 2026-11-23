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
From Ucos2Verify.VC.code.task Require Import task_suspend_goal.
From Ucos2Verify.VC.code.task Require Import task_suspend_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_api_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTaskSuspend_entail_wit_1_1 : OSTaskSuspend_entail_wit_1_1.
Proof.
  left; intros; subst prio_pre.
  unfold task_suspend_call_pre; Intros.
  assert (Hvalid : valid_stable_glob_vars sg) by tauto.
  assert (Hchecks : sg.(osKernelConfig).(cfgArgumentChecks) = true) by tauto.
  assert (Hrange : 0 <= request <= 255) by tauto.
  rewrite (task_suspend_request_promotion_eq__entry_resolution request Hrange) in PreH1.
  subst request.
  assert (Hnone : task_suspend_argument_error sg 255 = None).
  { rewrite (task_suspend_argument_error_eq__entry_resolution sg 255 Hvalid Hchecks).
    reflexivity. }
  rewrite Hnone; Intros.
  entailer!; unfold task_suspend_entry_facts, task_suspend_argument_none; tauto.
Qed. 

Lemma proof_of_OSTaskSuspend_entail_wit_1_2 : OSTaskSuspend_entail_wit_1_2.
Proof.
  left; intros; subst prio_pre.
  unfold task_suspend_call_pre; Intros.
  assert (Hvalid : valid_stable_glob_vars sg) by tauto.
  assert (Hchecks : sg.(osKernelConfig).(cfgArgumentChecks) = true) by tauto.
  assert (Hrange : 0 <= request <= 255) by tauto.
  rewrite (task_suspend_request_promotion_eq__entry_resolution request Hrange) in PreH1.
  assert (Hnone : task_suspend_argument_error sg request = None).
  { rewrite (task_suspend_argument_error_eq__entry_resolution sg request Hvalid Hchecks).
    assert (Hidle : Z.eqb request 63 = false) by (apply Z.eqb_neq; lia).
    assert (Hbelow : Z.leb 63 request = false) by (apply Z.leb_gt; lia).
    rewrite Hidle, Hbelow; reflexivity. }
  rewrite Hnone; Intros.
  entailer!; unfold task_suspend_entry_facts, task_suspend_argument_none; tauto.
Qed. 

Lemma proof_of_OSTaskSuspend_entail_wit_2 : OSTaskSuspend_entail_wit_2.
Proof.
  left; intros.
  unfold task_suspend_save_history_post; Intros acquired_call acquired.
  destruct H as [Hsave Heffect].
  unfold task_suspend_masked.
  assert (Hcarry : UCOS2_inv sg acquired |--
    coq_prop (UCOS2_state_inv sg acquired) && UCOS2_inv sg acquired).
  { unfold UCOS2_inv; entailer!. }
  sep_apply_l_atomic Hcarry; Intros.
  destruct (proj1 PreH2 acquired_call retval acquired Hsave H)
    as [[pointer [priority [residual Hread]]] Hsource].
  Exists acquired_call acquired pointer priority residual.
  assert (Hfacts : task_suspend_acquired_facts critical sg caller request mask before
    retval acquired_call acquired pointer priority residual).
  { unfold task_suspend_acquired_facts; tauto. }
  destruct Hread as [_ [_ [_ [Hsplit Hmerge]]]].
  pose proof PreH5 as [Haddress Haddresses].
  rewrite <- Haddress in Hsplit; cbn [tcb_field_address] in Hsplit.
  sep_apply_l_atomic Hsplit.
  unfold task_suspend_tokens; entailer!.
Qed. 

Lemma proof_of_OSTaskSuspend_entail_wit_3_1 : OSTaskSuspend_entail_wit_3_1.
Proof.
  left; intros.
  pose proof PreH1 as Hfacts.
  destruct Hfacts as (Hentry & _ & _ & _ & _ & Hread).
  pose proof Hentry as (Hvalid & Hchecks & Hrange & Hnone & Halign).
  assert (Hself : sg.(osPrioSelf) = 255) by
    (unfold valid_stable_glob_vars in Hvalid; tauto).
  assert (Hlowest : sg.(osLowestPrio) = 63) by
    (unfold valid_stable_glob_vars in Hvalid; tauto).
  rewrite (task_suspend_request_promotion_eq__entry_resolution request Hrange) in PreH3.
  assert (Hresolved : task_suspend_resolved_priority sg request priority = priority).
  { replace request with sg.(osPrioSelf) by lia.
    apply task_suspend_resolved_priority_self. }
  destruct Hread as [_ [_ [Hpriority _]]].
  pose proof (task_suspend_resolved_priority_in_range__entry_resolution
    sg request priority Hentry Hpriority) as Hselected.
  unfold task_priority_in_range in Hselected; rewrite Hresolved, Hlowest in Hselected.
  sep_apply_l_atomic (store_uchar_undef_store_uchar (&("self")) 1).
  entailer!.
Qed. 

Lemma proof_of_OSTaskSuspend_entail_wit_3_2 : OSTaskSuspend_entail_wit_3_2.
Proof.
  left; intros.
  pose proof PreH1 as Hfacts.
  destruct Hfacts as (Hentry & _ & _ & _ & _ & Hread).
  pose proof Hentry as (Hvalid & Hchecks & Hrange & Hnone & Halign).
  assert (Hself : sg.(osPrioSelf) = 255) by
    (unfold valid_stable_glob_vars in Hvalid; tauto).
  assert (Hlowest : sg.(osLowestPrio) = 63) by
    (unfold valid_stable_glob_vars in Hvalid; tauto).
  rewrite (task_suspend_request_promotion_eq__entry_resolution request Hrange) in PreH4.
  assert (Hresolved : task_suspend_resolved_priority sg request priority = request).
  { apply task_suspend_resolved_priority_explicit; lia. }
  destruct Hread as [_ [_ [Hpriority _]]].
  pose proof (task_suspend_resolved_priority_in_range__entry_resolution
    sg request priority Hentry Hpriority) as Hselected.
  unfold task_priority_in_range in Hselected; rewrite Hresolved, Hlowest in Hselected.
  sep_apply_l_atomic (store_uchar_undef_store_uchar (&("self")) 1).
  entailer!.
Qed. 

Lemma proof_of_OSTaskSuspend_entail_wit_3_3 : OSTaskSuspend_entail_wit_3_3.
Proof.
  left; intros.
  pose proof PreH1 as Hfacts.
  destruct Hfacts as (Hentry & _ & _ & _ & _ & Hread).
  pose proof Hentry as (Hvalid & Hchecks & Hrange & Hnone & Halign).
  assert (Hself : sg.(osPrioSelf) = 255) by
    (unfold valid_stable_glob_vars in Hvalid; tauto).
  assert (Hlowest : sg.(osLowestPrio) = 63) by
    (unfold valid_stable_glob_vars in Hvalid; tauto).
  rewrite (task_suspend_request_promotion_eq__entry_resolution request Hrange) in PreH4.
  assert (Hresolved : task_suspend_resolved_priority sg request priority = request).
  { apply task_suspend_resolved_priority_explicit; lia. }
  destruct Hread as [_ [_ [Hpriority _]]].
  pose proof (task_suspend_resolved_priority_in_range__entry_resolution
    sg request priority Hentry Hpriority) as Hselected.
  unfold task_priority_in_range in Hselected; rewrite Hresolved, Hlowest in Hselected.
  sep_apply_l_atomic (store_uchar_undef_store_uchar (&("self")) 0).
  entailer!.
Qed. 

Lemma proof_of_OSTaskSuspend_entail_wit_4_1 : OSTaskSuspend_entail_wit_4_1.
Proof.
  right; intros.
  rewrite !replace_Znth_Znth in *.
  rewrite Znth_replace_Znth_Same in * by
    (rewrite os_sched_rows_length_eq__fields_bitmap; lia).
  rewrite os_sched_rows_Znth_eq__fields_bitmap in * by lia.
  fold (task_suspend_cleared_row acquired target) in *.
  pose proof (task_suspend_cleared_row_in_range__fields_bitmap acquired target) as Hrow.
  change (unsigned_last_nbits (task_suspend_cleared_row acquired target) 32 = 0) in PreH5.
  rewrite (unsigned_last_nbits_eq (task_suspend_cleared_row acquired target) 32)
    in PreH5 by (change (0 <= task_suspend_cleared_row acquired target < 4294967296); lia).
  assert (Hself : Z.eqb (task_slot_addr sg tid)
    (task_suspend_current_pointer sg acquired) = true) by
    (apply Z.eqb_eq; congruence).
  assert (Hzero : Z.eqb (task_suspend_cleared_row acquired target) 0 = true) by
    (apply Z.eqb_eq; exact PreH5).
  assert (Hselfbyte : 1 = task_suspend_self_byte sg acquired tid).
  { change (1 = if Z.eqb (task_slot_addr sg tid)
      (task_suspend_current_pointer sg acquired) then 1 else 0).
    rewrite Hself; reflexivity. }
  assert (Hgroup : Z.land (os_sched_group acquired)
    (unsigned_last_nbits (Z.lnot (tcb_bit_y_of_prio (curPrio target))) 8) =
    task_suspend_updated_group acquired target).
  { change (Z.land (os_sched_group acquired)
      (unsigned_last_nbits (Z.lnot (tcb_bit_y_of_prio (curPrio target))) 8) = if Z.eqb (task_suspend_cleared_row acquired target) 0 then
      Z.land (os_sched_group acquired)
        (unsigned_last_nbits (Z.lnot (tcb_bit_y_of_prio (curPrio target))) 8)
      else os_sched_group acquired).
    rewrite Hzero; reflexivity. }
  pose proof (uchar_array_missing_i_replace_equiv__fields_bitmap (os_sched_rows acquired)
    (&("OSRdyTbl")) (tcb_y_of_prio (curPrio target)) 0 8
    (task_suspend_cleared_row acquired target) ltac:(lia)) as Hmissing.
  rewrite Z.sub_0_r in Hmissing.
  unfold task_suspend_cleared_row in Hmissing.
  rewrite Hmissing.
  entailer!.
Qed.

Lemma proof_of_OSTaskSuspend_entail_wit_4_2 : OSTaskSuspend_entail_wit_4_2.
Proof.
  right; intros.
  rewrite !replace_Znth_Znth in *.
  rewrite Znth_replace_Znth_Same in * by
    (rewrite os_sched_rows_length_eq__fields_bitmap; lia).
  rewrite os_sched_rows_Znth_eq__fields_bitmap in * by lia.
  fold (task_suspend_cleared_row acquired target) in *.
  pose proof (task_suspend_cleared_row_in_range__fields_bitmap acquired target) as Hrow.
  change (unsigned_last_nbits (task_suspend_cleared_row acquired target) 32 = 0) in PreH5.
  rewrite (unsigned_last_nbits_eq (task_suspend_cleared_row acquired target) 32)
    in PreH5 by (change (0 <= task_suspend_cleared_row acquired target < 4294967296); lia).
  assert (Hself : Z.eqb (task_slot_addr sg tid)
    (task_suspend_current_pointer sg acquired) = false) by
    (apply Z.eqb_neq; congruence).
  assert (Hzero : Z.eqb (task_suspend_cleared_row acquired target) 0 = true) by
    (apply Z.eqb_eq; exact PreH5).
  assert (Hselfbyte : 0 = task_suspend_self_byte sg acquired tid).
  { change (0 = if Z.eqb (task_slot_addr sg tid)
      (task_suspend_current_pointer sg acquired) then 1 else 0).
    rewrite Hself; reflexivity. }
  assert (Hgroup : Z.land (os_sched_group acquired)
    (unsigned_last_nbits (Z.lnot (tcb_bit_y_of_prio (curPrio target))) 8) =
    task_suspend_updated_group acquired target).
  { change (Z.land (os_sched_group acquired)
      (unsigned_last_nbits (Z.lnot (tcb_bit_y_of_prio (curPrio target))) 8) = if Z.eqb (task_suspend_cleared_row acquired target) 0 then
      Z.land (os_sched_group acquired)
        (unsigned_last_nbits (Z.lnot (tcb_bit_y_of_prio (curPrio target))) 8)
      else os_sched_group acquired).
    rewrite Hzero; reflexivity. }
  pose proof (uchar_array_missing_i_replace_equiv__fields_bitmap (os_sched_rows acquired)
    (&("OSRdyTbl")) (tcb_y_of_prio (curPrio target)) 0 8
    (task_suspend_cleared_row acquired target) ltac:(lia)) as Hmissing.
  rewrite Z.sub_0_r in Hmissing.
  unfold task_suspend_cleared_row in Hmissing.
  rewrite Hmissing.
  entailer!.
Qed.

Lemma proof_of_OSTaskSuspend_entail_wit_4_3 : OSTaskSuspend_entail_wit_4_3.
Proof.
  right; intros.
  rewrite !replace_Znth_Znth in *.
  rewrite Znth_replace_Znth_Same in * by
    (rewrite os_sched_rows_length_eq__fields_bitmap; lia).
  rewrite os_sched_rows_Znth_eq__fields_bitmap in * by lia.
  fold (task_suspend_cleared_row acquired target) in *.
  pose proof (task_suspend_cleared_row_in_range__fields_bitmap acquired target) as Hrow.
  change (unsigned_last_nbits (task_suspend_cleared_row acquired target) 32 <> 0) in PreH1.
  rewrite (unsigned_last_nbits_eq (task_suspend_cleared_row acquired target) 32)
    in PreH1 by (change (0 <= task_suspend_cleared_row acquired target < 4294967296); lia).
  assert (Hself : Z.eqb (task_slot_addr sg tid)
    (task_suspend_current_pointer sg acquired) = true) by
    (apply Z.eqb_eq; congruence).
  assert (Hzero : Z.eqb (task_suspend_cleared_row acquired target) 0 = false) by
    (apply Z.eqb_neq; exact PreH1).
  assert (Hselfbyte : 1 = task_suspend_self_byte sg acquired tid).
  { change (1 = if Z.eqb (task_slot_addr sg tid)
      (task_suspend_current_pointer sg acquired) then 1 else 0).
    rewrite Hself; reflexivity. }
  assert (Hgroup : os_sched_group acquired =
    task_suspend_updated_group acquired target).
  { change (os_sched_group acquired = if Z.eqb (task_suspend_cleared_row acquired target) 0 then
      Z.land (os_sched_group acquired)
        (unsigned_last_nbits (Z.lnot (tcb_bit_y_of_prio (curPrio target))) 8)
      else os_sched_group acquired).
    rewrite Hzero; reflexivity. }
  pose proof (uchar_array_missing_i_replace_equiv__fields_bitmap (os_sched_rows acquired)
    (&("OSRdyTbl")) (tcb_y_of_prio (curPrio target)) 0 8
    (task_suspend_cleared_row acquired target) ltac:(lia)) as Hmissing.
  rewrite Z.sub_0_r in Hmissing.
  unfold task_suspend_cleared_row in Hmissing.
  rewrite Hmissing.
  entailer!.
Qed.

Lemma proof_of_OSTaskSuspend_entail_wit_4_4 : OSTaskSuspend_entail_wit_4_4.
Proof.
  right; intros.
  rewrite !replace_Znth_Znth in *.
  rewrite Znth_replace_Znth_Same in * by
    (rewrite os_sched_rows_length_eq__fields_bitmap; lia).
  rewrite os_sched_rows_Znth_eq__fields_bitmap in * by lia.
  fold (task_suspend_cleared_row acquired target) in *.
  pose proof (task_suspend_cleared_row_in_range__fields_bitmap acquired target) as Hrow.
  change (unsigned_last_nbits (task_suspend_cleared_row acquired target) 32 <> 0) in PreH1.
  rewrite (unsigned_last_nbits_eq (task_suspend_cleared_row acquired target) 32)
    in PreH1 by (change (0 <= task_suspend_cleared_row acquired target < 4294967296); lia).
  assert (Hself : Z.eqb (task_slot_addr sg tid)
    (task_suspend_current_pointer sg acquired) = false) by
    (apply Z.eqb_neq; congruence).
  assert (Hzero : Z.eqb (task_suspend_cleared_row acquired target) 0 = false) by
    (apply Z.eqb_neq; exact PreH1).
  assert (Hselfbyte : 0 = task_suspend_self_byte sg acquired tid).
  { change (0 = if Z.eqb (task_slot_addr sg tid)
      (task_suspend_current_pointer sg acquired) then 1 else 0).
    rewrite Hself; reflexivity. }
  assert (Hgroup : os_sched_group acquired =
    task_suspend_updated_group acquired target).
  { change (os_sched_group acquired = if Z.eqb (task_suspend_cleared_row acquired target) 0 then
      Z.land (os_sched_group acquired)
        (unsigned_last_nbits (Z.lnot (tcb_bit_y_of_prio (curPrio target))) 8)
      else os_sched_group acquired).
    rewrite Hzero; reflexivity. }
  pose proof (uchar_array_missing_i_replace_equiv__fields_bitmap (os_sched_rows acquired)
    (&("OSRdyTbl")) (tcb_y_of_prio (curPrio target)) 0 8
    (task_suspend_cleared_row acquired target) ltac:(lia)) as Hmissing.
  rewrite Z.sub_0_r in Hmissing.
  unfold task_suspend_cleared_row in Hmissing.
  rewrite Hmissing.
  entailer!.
Qed.

Lemma proof_of_OSTaskSuspend_entail_wit_5 : OSTaskSuspend_entail_wit_5.
Proof.
  Unfold. right.
  intros frame before request mask caller sg saved_local critical environment X
    acquired_call acquired pointer priority residual tid target prio ptcb y self cpu_sr
    Htargetfacts Hlow Hhigh Hprio Hnotidle Hptcb Hy Hself Htargetfacts' Hfacts Haddresses Hsafe Heffect.
  destruct Htargetfacts as [Hvalid [[Htable Htarget] [Hselected [Hidle Hpriority]]]].
  destruct Hfacts as [Hentry [Hcompleted [Hclients [Hsave [Hvalid' Hread]]]]].
  destruct Hentry as [Hsg Hentry].
  assert (Hstep : task_suspend_step sg request priority acquired 0 self
    (task_suspend_state acquired tid target)).
  { apply task_suspend_step_none. rewrite Hself.
    unfold task_suspend_self_byte, task_suspend_current_pointer.
    replace (Z.eqb (if Z.eqb (task_slot_addr sg tid)
      (encode_task_link sg acquired.(SchedState).(curTaskID)) then 1 else 0) 1)
      with (Z.eqb (task_slot_addr sg tid)
        (encode_task_link sg acquired.(SchedState).(curTaskID)))
      by (destruct (Z.eqb (task_slot_addr sg tid)
        (encode_task_link sg acquired.(SchedState).(curTaskID))); reflexivity).
    apply task_suspend_protected_task; try rewrite <- Hprio; assumption. }
  assert (Hsource : self = 1 -> task_suspend_caller_source sg acquired_call
    (task_suspend_state acquired tid target)).
  { intro Hone.
    pose proof (proj1 (task_suspend_step_none _ _ _ _ _ _) Hstep) as Hprotected.
    rewrite Hone, Z.eqb_refl in Hprotected.
    eapply task_suspend_protected_preserves_caller_source;
      [exact Hvalid|exact Hprotected|].
    eapply (proj2 (proj1 Hcompleted acquired_call cpu_sr acquired Hsave Hvalid));
      eassumption. }
  assert (Hunique : task_priority_unique acquired.(TskState)).
  { destruct Hvalid as [_ [Htasks _]]. unfold task_in_range in Htasks; tauto. }
  assert (Hstructure : sched_ready_structure sg acquired.(TskState) acquired.(SchedState)).
  { apply sched_ready_in_range_implies_structure.
    destruct Hvalid as [_ [_ [[Hready _] _]]]; exact Hready. }
  assert (Hrow : 0 <= target.(curPrio) / 8 < 8).
  { destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]].
    unfold task_priority_in_range in Hpriority.
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  destruct (task_suspend_bitmap_encoding sg acquired.(TskState) acquired.(SchedState)
    tid target Hsg Hunique Htarget Hpriority Hstructure) as [Hgroup Hrows].
  pose proof (task_suspend_status_merge_updated sg acquired.(TskState) tid target) as Hstatus.
  cbn [tcb_field_address] in Hstatus. unfold task_suspend_mask in Hstatus.
  destruct Haddresses as [Hcurrent Haddresses].
  unfold os_sched_global_addresses, sched_new_global_addresses in Haddresses.
  destruct Haddresses as [Hinterrupts [Hlocks [Hhighprio [Hcurprio [Hhightcb
    [Htableaddr [Hcounter [Hunmap [Hgroupaddr [Hrowsaddr Hhighprio']]]]]]]]]].
  subst y.
  rewrite Hcurrent, Hgroupaddr, Hrowsaddr.
  unfold task_suspend_cleared_row, os_sched_rows, tcb_y_of_prio,
    tcb_bit_x_of_prio, tcb_x_of_prio.
  sep_apply_l_atomic Hstatus.
  sep_apply_l_atomic (task_suspend_merge_updated_rows sg acquired.(TskState)
    acquired.(SchedState) tid target Hsg Hunique Htarget Hpriority Hstructure Hrow).
  unfold task_suspend_tokens, task_suspend_masked.
  sep_apply_l_atomic (task_suspend_call_resources_updated environment saved_local sg
    acquired_call acquired tid target Htarget).
  entailer!.
  pose proof (UCOS2_inv_merge_task_suspend sg acquired tid target Hvalid Htarget) as Hmerge.
  cbn zeta in Hmerge. sep_apply_r_atomic Hmerge.
  unfold task_suspend_work_frame, sched_raw_rep, sched_physical_rep.
  cbn [task_suspend_state replace_TskS replace_SchedS TskState SchedState
    sched_remove_ready_task sched_set_ready curSchedPrio highRdyPrio curTaskID highRdyTid
    ctxSwCtr isRunning].
  rewrite Hgroup.
  unfold task_suspend_updated_group, task_suspend_cleared_row, os_sched_group,
    task_suspend_current_pointer, tcb_y_of_prio, tcb_bit_x_of_prio, tcb_bit_y_of_prio,
    tcb_x_of_prio.
  entailer!.
Qed.

Lemma proof_of_OSTaskSuspend_entail_wit_6 : OSTaskSuspend_entail_wit_6.
Proof.
  Unfold. left.
  intros frame before request mask caller sg saved_local critical environment X
    acquired_call acquired pointer priority residual tid target prio self cpu_sr
    Hprio Hself Hfacts Haddresses Hstep Hsource Hsafe Heffect.
  pose proof Hfacts as Hacquired.
  destruct Hfacts as [Hentry [Hcompleted [Hclients [Hsave [Hvalid Hread]]]]].
  destruct (task_suspend_save_observation_same_call _ _ _ _ _ _ _ _ Hsave)
    as [Hsame [Hsaved Hmask]].
  unfold task_suspend_restore_history_post. Intros checkpoint_call checkpoint.
  assert (Hrestore : task_suspend_restore_observation critical sg acquired_call
    checkpoint_call (task_suspend_state acquired tid target) checkpoint) by tauto.
  assert (Hrestore_effect : task_suspend_restore_effect environment critical sg acquired_call
    checkpoint_call (task_suspend_state acquired tid target) checkpoint) by tauto.
  destruct (task_suspend_step_safe_continuation environment critical sg caller mask request before
    cpu_sr acquired_call acquired pointer priority residual 0 self
    (task_suspend_state acquired tid target) checkpoint_call checkpoint X Hacquired Heffect
    Hstep Hrestore_effect Hsafe) as [Hschedule_safe Hreturn_safe].
  assert (Hclients' : task_suspend_scheduler_clients critical checkpoint_call).
  { eapply task_suspend_scheduler_clients_same_call.
    - eapply task_suspend_same_call_trans.
      + eapply task_suspend_restore_observation_same_call; exact Hrestore.
      + exact Hsame.
    - exact Hclients. }
  assert (Hsource' : self = 1 -> task_suspend_caller_source sg checkpoint_call checkpoint).
  { intro Hone.
    apply task_suspend_step_none in Hstep.
    rewrite Hone, Z.eqb_refl in Hstep.
    eapply (proj2 Hcompleted); eauto. }
  rewrite Hmask.
  Exists checkpoint_call checkpoint. entailer!.
Qed.

Lemma proof_of_OSTaskSuspend_return_wit_1 : OSTaskSuspend_return_wit_1.
Proof.
  Unfold. left.
  intros frame before request mask caller sg saved_local critical environment X
    acquired_call acquired pointer priority residual tid target prio self cpu_sr
    checkpoint_call checkpoint Haddresses Hpromoted Hprio Hself Hfacts
    Haddresses' Hstep Hrestore Hclients Hsource Hschedule_safe Hreturn_safe.
  assert (Hone : self = 1).
  { rewrite Hself in Hpromoted |- *.
    unfold task_suspend_self_byte in *.
    destruct (Z.eqb (task_slot_addr sg tid) (task_suspend_current_pointer sg acquired));
      [reflexivity|vm_compute in Hpromoted; discriminate]. }
  destruct Hfacts as [[Hsg [Hchecks [Hrequest [Hnone Haligned]]]]
    [Hcompleted [Hcallerclients [Hsave [Hvalid Hread]]]]].
  apply task_suspend_step_none in Hstep. rewrite Hone, Z.eqb_refl in Hstep.
  unfold task_suspend_refined_call_post, task_suspend_argument_none in *; rewrite Hnone.
  Exists cpu_sr acquired_call acquired pointer priority residual
    (task_suspend_state acquired tid target) checkpoint_call checkpoint true error_codes.OS_ERR_NONE.
  unfold task_suspend_refined_tail_post. entailer!.
Qed.

Lemma proof_of_OSTaskSuspend_return_wit_2 : OSTaskSuspend_return_wit_2.
Proof.
  Unfold. left.
  intros frame before request mask caller sg saved_local critical environment X
    acquired_call acquired pointer priority residual tid target prio self cpu_sr
    checkpoint_call checkpoint Hpromoted Hprio Hself Hfacts
    Haddresses Hstep Hrestore Hclients Hsource Hschedule_safe Hreturn_safe.
  assert (Hzero : self = 0).
  { rewrite Hself in Hpromoted |- *.
    unfold task_suspend_self_byte in *.
    destruct (Z.eqb (task_slot_addr sg tid) (task_suspend_current_pointer sg acquired));
      [exfalso; apply Hpromoted; reflexivity|reflexivity]. }
  destruct Hfacts as [[Hsg [Hchecks [Hrequest [Hnone Haligned]]]]
    [Hcompleted [Hcallerclients [Hsave [Hvalid Hread]]]]].
  apply task_suspend_step_none in Hstep. rewrite Hzero in Hstep.
  specialize (Hreturn_safe ltac:(lia)).
  unfold task_suspend_refined_call_post, task_suspend_argument_none in *; rewrite Hnone.
  Exists cpu_sr acquired_call acquired pointer priority residual
    (task_suspend_state acquired tid target) checkpoint_call checkpoint false error_codes.OS_ERR_NONE.
  unfold task_suspend_refined_tail_post, task_suspend_return_safe in *; entailer!.
Qed.

Lemma proof_of_OSTaskSuspend_return_wit_3 : OSTaskSuspend_return_wit_3.
Proof.
  left; intros.
  eapply task_suspend_restore_history_post_unscheduled_call_post; eassumption.
Qed.

Lemma proof_of_OSTaskSuspend_return_wit_4 : OSTaskSuspend_return_wit_4.
Proof.
  left; intros.
  eapply task_suspend_restore_history_post_unscheduled_call_post; eassumption.
Qed.

Lemma proof_of_OSTaskSuspend_return_wit_5 : OSTaskSuspend_return_wit_5.
Proof.
  left; intros.
  eapply task_suspend_restore_history_post_unscheduled_call_post; eassumption.
Qed.

Lemma proof_of_OSTaskSuspend_return_wit_6 : OSTaskSuspend_return_wit_6.
Proof.
  left; intros; subst prio_pre.
  unfold task_suspend_call_pre, task_suspend_refined_call_post; Intros.
  assert (Hvalid : valid_stable_glob_vars sg) by tauto.
  assert (Hchecks : sg.(osKernelConfig).(cfgArgumentChecks) = true) by tauto.
  assert (Hrange : 0 <= request <= 255) by tauto.
  rewrite (task_suspend_request_promotion_eq__entry_resolution request Hrange) in PreH1, PreH2.
  assert (Herror : task_suspend_argument_error sg request = Some error_codes.OS_ERR_PRIO_INVALID).
  { rewrite (task_suspend_argument_error_eq__entry_resolution sg request Hvalid Hchecks).
    assert (Hidle : Z.eqb request 63 = false) by (apply Z.eqb_neq; assumption).
    assert (Hhigh : Z.leb 63 request = true) by (apply Z.leb_le; lia).
    assert (Hself : Z.eqb request 255 = false) by (apply Z.eqb_neq; assumption).
    rewrite Hidle, Hhigh, Hself; reflexivity. }
  pose proof (task_suspend_argument_safe_return environment critical sg caller mask request before
    error_codes.OS_ERR_PRIO_INVALID X Herror PreH6) as Hreturn.
  rewrite Herror; simpl; entailer!.
Qed. 

Lemma proof_of_OSTaskSuspend_return_wit_7 : OSTaskSuspend_return_wit_7.
Proof.
  left; intros; subst prio_pre; subst request.
  unfold task_suspend_call_pre, task_suspend_refined_call_post; Intros.
  assert (Hvalid : valid_stable_glob_vars sg) by tauto.
  assert (Hchecks : sg.(osKernelConfig).(cfgArgumentChecks) = true) by tauto.
  assert (Herror : task_suspend_argument_error sg 63 = Some error_codes.OS_ERR_TASK_SUSPEND_IDLE).
  { rewrite (task_suspend_argument_error_eq__entry_resolution sg 63 Hvalid Hchecks).
    reflexivity. }
  pose proof (task_suspend_argument_safe_return environment critical sg caller mask 63 before
    error_codes.OS_ERR_TASK_SUSPEND_IDLE X Herror PreH4) as Hreturn.
  rewrite Herror; simpl; entailer!.
Qed. 

Lemma proof_of_OSTaskSuspend_partial_solve_wit_10_pure : OSTaskSuspend_partial_solve_wit_10_pure.
Proof. right; intros; entailer!; congruence. Qed.

Lemma proof_of_OSTaskSuspend_partial_solve_wit_12_pure : OSTaskSuspend_partial_solve_wit_12_pure.
Proof. right; intros; entailer!; congruence. Qed.

Lemma proof_of_OSTaskSuspend_partial_solve_wit_35_pure : OSTaskSuspend_partial_solve_wit_35_pure.
Proof.
  Unfold. left.
  intros frame before request mask caller sg saved_local critical environment X
    acquired_call acquired pointer priority residual tid target prio self cpu_sr
    checkpoint_call checkpoint Hpromoted Hprio Hself Hfacts
    Haddresses Hstep Hrestore Hclients Hsource Hschedule_safe Hreturn_safe.
  assert (Hone : self = 1).
  { rewrite Hself in Hpromoted |- *.
    unfold task_suspend_self_byte in *.
    destruct (Z.eqb (task_slot_addr sg tid) (task_suspend_current_pointer sg acquired));
      [reflexivity|vm_compute in Hpromoted; discriminate]. }
  specialize (Hsource Hone). entailer!.
Qed.

Lemma proof_of_OSTaskSuspend_partial_solve_wit_36_pure : OSTaskSuspend_partial_solve_wit_36_pure.
Proof.
  left; intros.
  assert (Hone : self = 1).
  { rewrite PreH3 in PreH1 |- *.
    unfold task_suspend_self_byte in *.
    destruct (Z.eqb (task_slot_addr sg tid) (task_suspend_current_pointer sg acquired));
      [reflexivity|vm_compute in PreH1; discriminate]. }
  specialize (PreH10 Hone); entailer!.
Qed.

Lemma proof_of_OSTaskSuspend_which_implies_wit_1 : OSTaskSuspend_which_implies_wit_1.
Proof.
  left; intros.
  assert (Hnone : task_suspend_argument_error sg request = None).
  { destruct PreH1 as (_ & _ & _ & Hnone & _); exact Hnone. }
  unfold task_suspend_call_pre; rewrite Hnone; entailer!.
Qed. 

Lemma proof_of_OSTaskSuspend_which_implies_wit_2 : OSTaskSuspend_which_implies_wit_2.
Proof.
  left; intros.
  pose proof PreH1 as (_ & _ & _ & _ & _ & Hread).
  destruct Hread as [_ [_ [_ [_ Hmerge]]]].
  pose proof PreH2 as [Haddress Haddresses].
  rewrite <- Haddress in Hmerge; cbn [tcb_field_address] in Hmerge.
  sep_apply Hmerge; entailer!.
Qed. 

Lemma proof_of_OSTaskSuspend_which_implies_wit_3 : OSTaskSuspend_which_implies_wit_3.
Proof.
  right; intros.
  pose proof (proj1 (proj1 PreH3)) as Hstable.
  assert (Hidle : sg.(osTaskIdlePrio) = 63).
  { unfold valid_stable_glob_vars in Hstable; lia. }
  assert (Hrange : task_priority_in_range sg sg.(osTaskIdlePrio)).
  { unfold task_priority_in_range, valid_stable_glob_vars in *; lia. }
  assert (Hstep : task_suspend_step sg request priority acquired 71 0 acquired).
  { exists Ucos2Verify.lib.error_codes.OS_ERR_TASK_SUSPEND_IDLE; split; [reflexivity|].
    apply task_suspend_protected_resolved_idle; [exact Hrange|congruence]. }
  unfold task_suspend_tokens, task_suspend_masked; entailer!.
Qed.

Lemma proof_of_OSTaskSuspend_which_implies_wit_4 : OSTaskSuspend_which_implies_wit_4.
Proof.
  right; intros.
  assert (Htable : sg.(g_OSTCBPrioTbl) = &( "OSTCBPrioTbl" )).
  { symmetry; unfold task_suspend_addresses, os_sched_global_addresses in PreH1; tauto. }
  sep_apply_l_atomic (UCOS2_inv_open_task_storage_sched sg acquired).
  Intros.
  rewrite task_public_storage_prio_tbl_equiv.
  pose proof (store_prio_tbl_split_cell sg acquired.(TskState).(prioTbl) prio
    ltac:(lia)) as Hsplit.
  rewrite Htable in Hsplit; sep_apply_l_atomic Hsplit.
  unfold task_suspend_table_frame, task_suspend_table_value; entailer!.
Qed.

Lemma proof_of_OSTaskSuspend_which_implies_wit_5 : OSTaskSuspend_which_implies_wit_5.
Proof.
  right; intros.
  assert (Htable : sg.(g_OSTCBPrioTbl) = &( "OSTCBPrioTbl" )).
  { symmetry; unfold task_suspend_addresses, os_sched_global_addresses in PreH1; tauto. }
  pose proof (ptr_array_missing_i_in_range__lookup_errors sg.(g_OSTCBPrioTbl)
    prio 0 64 (map (fun q => prio_tbl_entry_to_addr sg (acquired.(TskState).(prioTbl) q))
      (SumLib.ZRange.Zrange 0 64))) as Hrange.
  change (store_prio_tbl_missing_i sg acquired.(TskState).(prioTbl) prio |--
    coq_prop (0 <= prio < 64)) in Hrange.
  unfold task_suspend_table_frame; prop_apply Hrange; Intros.
  pose proof (store_prio_tbl_merge_cell sg acquired.(TskState).(prioTbl) prio
    ltac:(lia)) as Hmerge.
  rewrite Htable in Hmerge.
  unfold task_suspend_table_value; sep_apply Hmerge.
  sep_apply (proj2 (task_public_storage_prio_tbl_equiv sg acquired.(TskState))).
  sep_apply (UCOS2_inv_merge_updated_task_storage_sched sg acquired acquired PreH2 eq_refl).
  entailer!.
Qed.

Lemma proof_of_OSTaskSuspend_which_implies_wit_6 : OSTaskSuspend_which_implies_wit_6.
Proof.
  right; intros.
  destruct PreH5 as [Hentry [Hcompleted [Hclients [Hsave [Hvalid Hread]]]]].
  pose proof (task_suspend_resolved_priority_in_range__lookup_errors
    sg request acquired pointer priority residual Hentry Hread) as Hrange.
  pose proof (proj1 Hentry) as Hstable.
  assert (Hidle : sg.(osTaskIdlePrio) = 63).
  { unfold valid_stable_glob_vars in Hstable; lia. }
  assert (Hfree : acquired.(TskState).(prioTbl) prio = PTFree).
  { unfold task_suspend_table_value in PreH2.
    destruct (acquired.(TskState).(prioTbl) prio) as [| |tid] eqn:Htable;
      cbn [prio_tbl_entry_to_addr] in PreH2; [reflexivity|congruence|].
    destruct (task_suspend_table_task_lookup__lookup_errors sg acquired prio tid
      Hvalid ltac:(rewrite PreH4; exact Hrange) Htable)
      as [target [Htarget [Hslot Hpriority]]].
    pose proof (valid_stable_address_pos sg sg.(g_OSTCBTbl) Hstable
      ltac:(unfold stable_global_addresses; simpl; auto)) as Hbase.
    unfold task_slot_in_range in Hslot.
    unfold task_slot_addr, tcb_configured_size, tcb_layout_size in PreH2.
    destruct sg.(osKernelConfig).(cfgEventMultiEnabled);
      destruct sg.(osKernelConfig).(cfgTaskProfile); lia. }
  assert (Hstep : task_suspend_step sg request priority acquired 72 0 acquired).
  { exists Ucos2Verify.lib.error_codes.OS_ERR_TASK_SUSPEND_PRIO; split; [reflexivity|].
    apply task_suspend_protected_free; [exact Hrange|congruence|].
    rewrite <- PreH4; exact Hfree. }
  unfold task_suspend_tokens, task_suspend_masked; entailer!.
Qed.

Lemma proof_of_OSTaskSuspend_which_implies_wit_7 : OSTaskSuspend_which_implies_wit_7.
Proof.
  right; intros.
  destruct PreH5 as [Hentry [Hcompleted [Hclients [Hsave [Hvalid Hread]]]]].
  pose proof (task_suspend_resolved_priority_in_range__lookup_errors
    sg request acquired pointer priority residual Hentry Hread) as Hrange.
  pose proof (proj1 Hentry) as Hstable.
  assert (Hidle : sg.(osTaskIdlePrio) = 63).
  { unfold valid_stable_glob_vars in Hstable; lia. }
  assert (Haligned : sg.(g_OSTCBTbl) mod 4 = 0)
    by (unfold task_suspend_entry_facts in Hentry; tauto).
  pose proof (task_suspend_table_value_reserved sg acquired prio Haligned
    ltac:(congruence)) as Hreserved.
  assert (Hstep : task_suspend_step sg request priority acquired 67 0 acquired).
  { exists Ucos2Verify.lib.error_codes.OS_ERR_TASK_NOT_EXIST; split; [reflexivity|].
    apply task_suspend_protected_reserved; [exact Hrange|congruence|].
    rewrite <- PreH4; exact Hreserved. }
  unfold task_suspend_tokens, task_suspend_masked; entailer!.
Qed.

Lemma proof_of_OSTaskSuspend_which_implies_wit_8 : OSTaskSuspend_which_implies_wit_8.
Proof.
  left; intros.
  sep_apply_l_atomic (UCOS2_inv_open_task_storage_sched sg acquired); Intros.
  assert (Hvalid : UCOS2_state_inv sg acquired) by assumption.
  pose proof (proj1 (proj1 Hvalid)) as Hstable.
  assert (Hrange : task_priority_in_range sg prio).
  { unfold task_priority_in_range, valid_stable_glob_vars in *; lia. }
  assert (Hidle : sg.(osTaskIdlePrio) = 63).
  { unfold valid_stable_glob_vars in Hstable; lia. }
  unfold task_suspend_table_value in PreH2.
  destruct (acquired.(TskState).(prioTbl) prio) as [| |tid] eqn:Htable;
    cbn [prio_tbl_entry_to_addr] in PreH2; try contradiction.
  destruct (task_suspend_table_task_lookup__lookup_errors sg acquired prio tid
    Hvalid Hrange Htable) as [target [Htarget [Hslot Hpriority]]].
  Exists target tid.
  assert (Htargetfacts : task_suspend_target_facts sg acquired prio tid target).
  { unfold task_suspend_target_facts, task_suspend_lookup.
    split; [exact Hvalid|]; split; [split; assumption|].
    split; [exact Hrange|]; split; [lia|exact Hpriority]. }
  pose proof PreH1 as Haddresses.
  unfold task_suspend_addresses, os_sched_global_addresses,
    sched_new_global_addresses in Haddresses.
  assert (Hcurrent : &( "OSTCBCur" ) = sg.(g_OSTCBCur)) by tauto.
  assert (Hgroup : &( "OSRdyGrp" ) = sg.(g_OSRdyGrp)) by tauto.
  assert (Hrows : &( "OSRdyTbl" ) = sg.(g_OSRdyTbl)) by tauto.
  unfold task_suspend_work_frame, task_suspend_current_pointer, os_sched_group,
    os_sched_rows, Ucos2Verify.lib.sched.sched_raw_rep,
    Ucos2Verify.lib.sched.sched_physical_rep.
  rewrite Ucos2Verify.lib.sched.sched_rows_array_equiv.
  rewrite <- Hcurrent, <- Hgroup, <- Hrows.
  entailer!.
Qed.

Lemma proof_of_OSTaskSuspend_which_implies_wit_9 : OSTaskSuspend_which_implies_wit_9.
Proof.
  right; intros; subst ptcb.
  destruct PreH1 as [Hinv [[Hlookup Htarget] [Hselected [Hidle Hpriority]]]].
  assert (Hsg : valid_stable_glob_vars sg) by
    (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile in Hinv; tauto).
  pose proof (task_priority_y_in_range__fields_bitmap sg _ Hsg Hpriority) as Hy.
  pose proof (task_public_storage_split_field sg (TskState acquired) tid target
    (TCBCommonField TCBY) Htarget (tcb_configured_common_field_in _ _ _)) as Hsplit.
  change (task_public_storage sg (TskState acquired) |--
    (tcb_field_address (task_slot_addr sg tid) TCBY) # UChar |->
      tcb_y_of_prio (curPrio target) **
    task_public_storage_without_field sg (TskState acquired) tid target
      (TCBCommonField TCBY)) in Hsplit.
  sep_apply_l_atomic Hsplit; entailer!.
Qed.

Lemma proof_of_OSTaskSuspend_which_implies_wit_10 : OSTaskSuspend_which_implies_wit_10.
Proof.
  right; intros; subst ptcb.
  destruct PreH1 as [_ [[_ Htarget] _]].
  exact (task_public_storage_merge_field sg (TskState acquired) tid target
    (TCBCommonField TCBY) Htarget (tcb_configured_common_field_in _ _ _)).
Qed.

Lemma proof_of_OSTaskSuspend_which_implies_wit_11 : OSTaskSuspend_which_implies_wit_11.
Proof.
  right; intros; subst ptcb.
  destruct PreH1 as [_ [[_ Htarget] _]].
  pose proof (Ucos2Verify.lib.sched.bitmap_single_bit_in_range 8
    (tcb_x_of_prio (curPrio target))
    ltac:(unfold tcb_x_of_prio; apply Z.mod_pos_bound; lia)) as Hbits.
  fold (tcb_bit_x_of_prio (curPrio target)) in Hbits.
  pose proof (task_public_storage_split_field sg (TskState acquired) tid target
    (TCBCommonField TCBBitX) Htarget (tcb_configured_common_field_in _ _ _)) as Hsplit.
  change (task_public_storage sg (TskState acquired) |--
    (tcb_field_address (task_slot_addr sg tid) TCBBitX) # UChar |->
      tcb_bit_x_of_prio (curPrio target) **
    task_public_storage_without_field sg (TskState acquired) tid target
      (TCBCommonField TCBBitX)) in Hsplit.
  sep_apply_l_atomic Hsplit; entailer!.
Qed.

Lemma proof_of_OSTaskSuspend_which_implies_wit_12 : OSTaskSuspend_which_implies_wit_12.
Proof.
  right; intros; subst ptcb.
  destruct PreH1 as [_ [[_ Htarget] _]].
  exact (task_public_storage_merge_field sg (TskState acquired) tid target
    (TCBCommonField TCBBitX) Htarget (tcb_configured_common_field_in _ _ _)).
Qed.

Lemma proof_of_OSTaskSuspend_which_implies_wit_13 : OSTaskSuspend_which_implies_wit_13.
Proof.
  right; intros; subst ptcb.
  destruct PreH1 as [Hinv [[Hlookup Htarget] [Hselected [Hidle Hpriority]]]].
  assert (Hsg : valid_stable_glob_vars sg) by
    (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile in Hinv; tauto).
  pose proof (task_priority_y_in_range__fields_bitmap sg _ Hsg Hpriority) as Hy.
  pose proof (Ucos2Verify.lib.sched.bitmap_single_bit_in_range 8
    (tcb_y_of_prio (curPrio target)) Hy) as Hbits.
  fold (tcb_bit_y_of_prio (curPrio target)) in Hbits.
  pose proof (task_public_storage_split_field sg (TskState acquired) tid target
    (TCBCommonField TCBBitY) Htarget (tcb_configured_common_field_in _ _ _)) as Hsplit.
  change (task_public_storage sg (TskState acquired) |--
    (tcb_field_address (task_slot_addr sg tid) TCBBitY) # UChar |->
      tcb_bit_y_of_prio (curPrio target) **
    task_public_storage_without_field sg (TskState acquired) tid target
      (TCBCommonField TCBBitY)) in Hsplit.
  sep_apply_l_atomic Hsplit; entailer!.
Qed.

Lemma proof_of_OSTaskSuspend_which_implies_wit_14 : OSTaskSuspend_which_implies_wit_14.
Proof.
  right; intros; subst ptcb.
  destruct PreH1 as [_ [[_ Htarget] _]].
  exact (task_public_storage_merge_field sg (TskState acquired) tid target
    (TCBCommonField TCBBitY) Htarget (tcb_configured_common_field_in _ _ _)).
Qed.

Lemma proof_of_OSTaskSuspend_which_implies_wit_15 : OSTaskSuspend_which_implies_wit_15.
Proof.
  right; intros; subst ptcb.
  destruct PreH1 as [_ [[_ Htarget] _]].
  pose proof (Ucos2Verify.lib.task_status.encode_task_status_in_range (stat target)) as Hstatus.
  change (0 <= encode_task_status (stat target) < 256) in Hstatus.
  pose proof (task_public_storage_split_field sg (TskState acquired) tid target
    (TCBCommonField TCBStat) Htarget (tcb_configured_common_field_in _ _ _)) as Hsplit.
  change (task_public_storage sg (TskState acquired) |--
    (tcb_field_address (task_slot_addr sg tid) TCBStat) # UChar |->
      encode_task_status (stat target) **
    task_public_storage_without_field sg (TskState acquired) tid target
      (TCBCommonField TCBStat)) in Hsplit.
  sep_apply_l_atomic Hsplit; entailer!.
Qed.

Lemma proof_of_OSTaskSuspend_which_implies_wit_16 : OSTaskSuspend_which_implies_wit_16.
Proof.
  pre_process.
  apply task_suspend_caller_source_scheduler_pre; assumption.
Qed.

