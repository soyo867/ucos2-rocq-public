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
From Ucos2Verify.VC.code.task Require Import task_create_ext_continuation_goal.
From Ucos2Verify.VC.code.task Require Import task_create_ext_continuation_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.task.spec.task_create_ext_continuation_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.


Require Import Ucos2Verify.VC.code.task.spec.task_create_ext_continuation_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OSTaskCreateExt_entail_wit_1 : OSTaskCreateExt_entail_wit_1.
Proof.
unfold OSTaskCreateExt_entail_wit_1; left; intros.
  prop_apply (store_uchar_range (&("prio")) prio_pre).
  prop_apply (store_uint_range (&("stk_size")) stk_size_pre).
  Intros.
  change (0 <= prio_pre <= 255) in H; entailer!.
Qed.

Lemma proof_of_OSTaskCreateExt_entail_wit_2 : OSTaskCreateExt_entail_wit_2.
Proof.
left; intros.
  sep_apply_l_atomic (task_create_ext_continuation_save_phase_safe_entry environment_boot_phase_spec critical_boot_phase_spec saved_local_boot_phase_spec sg_boot_phase_spec region_boot_phase_spec args_boot_phase_spec
    task_return_boot_phase_spec after_lower_boot_phase_spec after_upper_boot_phase_spec (LitMap_boot_phase_spec "?") call_boot_phase_spec mask_boot_phase_spec retval initial_boot_phase_spec X_boot_phase_spec
    ltac:(lia) PreH11 PreH1 PreH13).
  Intros returned acquired.
  assert (Hbinding : task_create_default_name_binding (LitMap_boot_phase_spec "?") acquired).
  { eapply task_create_default_name_binding_transport; [|eassumption]; tauto. }
  Exists returned acquired; entailer!.
Qed.

Lemma proof_of_OSTaskCreateExt_return_wit_1 : OSTaskCreateExt_return_wit_1.
Proof.
left; intros.
  match goal with
  | Hsafe : task_create_ext_continuation_safe ?released (task_create_ext_continuation_restore_return_program _ _ _ ?actual 40) X_boot_phase_spec
    |- context [task_tcb_init_modular_restore_output _ _ _ _ ?actual ?saved ?released] =>
    pose proof (task_create_ext_continuation_restore_phase_safe_return environment_boot_phase_spec critical_boot_phase_spec saved_local_boot_phase_spec sg_boot_phase_spec region_boot_phase_spec args_boot_phase_spec task_return_boot_phase_spec
      lower_boot_phase_spec old_frame_boot_phase_spec upper_boot_phase_spec prefix_boot_phase_spec middle_boot_phase_spec suffix_boot_phase_spec call_boot_phase_spec actual mask_boot_phase_spec saved released initial_boot_phase_spec 40 X_boot_phase_spec
      ltac:(eassumption) ltac:(lia) ltac:(assumption) ltac:(assumption) ltac:(auto) Hsafe) as Hreturn;
    unfold task_create_stack_old_image in *;
    cbn [Z.eq_dec] in Hreturn;
    sep_apply_r_atomic Hreturn
  end; entailer!.
Qed.

Lemma proof_of_OSTaskCreateExt_return_wit_2 : OSTaskCreateExt_return_wit_2.
Proof.
left; intros; subst retval.
  sep_apply_l_atomic (task_create_ext_continuation_schedule_buffer_return environment_boot_phase_spec critical_boot_phase_spec saved_local_boot_phase_spec sg_boot_phase_spec call_boot_phase_spec mask_boot_phase_spec X_boot_phase_spec
    region_boot_phase_spec args_boot_phase_spec task_return_boot_phase_spec lower_boot_phase_spec old_frame_boot_phase_spec upper_boot_phase_spec prefix_boot_phase_spec middle_boot_phase_spec suffix_boot_phase_spec ltac:(lia)).
  sep_apply_r_atomic (task_create_ext_continuation_running_api_post environment_boot_phase_spec critical_boot_phase_spec saved_local_boot_phase_spec sg_boot_phase_spec region_boot_phase_spec args_boot_phase_spec
    task_return_boot_phase_spec lower_boot_phase_spec old_frame_boot_phase_spec upper_boot_phase_spec prefix_boot_phase_spec middle_boot_phase_spec suffix_boot_phase_spec call_boot_phase_spec mask_boot_phase_spec initial_boot_phase_spec 0 X_boot_phase_spec ltac:(eassumption)); entailer!.
Qed.

Lemma proof_of_OSTaskCreateExt_return_wit_3 : OSTaskCreateExt_return_wit_3.
Proof.
left; intros; subst retval.
  assert (Hstopped : task_create_stack_running current <> 1).
  { match goal with H : unsigned_last_nbits (task_create_stack_running current) 32 <> 1 |- _ =>
      rewrite unsigned_last_nbits_eq in H;
      [exact H|unfold task_create_stack_running; destruct current.(SchedState).(isRunning); cbn; lia]
    end. }
  assert (Hsafe : task_create_ext_continuation_safe current (StateRelMonad.ret (returned, 0)) X_boot_phase_spec).
  { eapply task_create_ext_continuation_tcb_stopped_safe; eassumption. }
  assert (Hphase : initial_boot_phase_spec.(TimerState).(timerInitPhase) = current.(TimerState).(timerInitPhase)).
  { match goal with H : task_create_ext_phase_frame initial_boot_phase_spec current |- _ => exact (proj2 H) end. }
  unfold task_create_ext_continuation_boot_phase_post; Exists returned current.
  destruct (Z.eq_dec 0 0); [|contradiction].
  unfold task_tcb_init_continuation_save_input, task_create_continuation_input, task_create_continuation_without_running,
    critical_region_outside, task_create_stack_running, task_tcb_init_continuation_capsules.
  match goal with H : task_create_stack_global_addresses sg_boot_phase_spec _ _ _ |- _ =>
    rewrite (proj2 (proj2 H))
  end; entailer!.
Qed.

Lemma proof_of_OSTaskCreateExt_return_wit_4 : OSTaskCreateExt_return_wit_4.
Proof.
left; intros; subst retval after_lower_boot_phase_spec after_upper_boot_phase_spec.
  match goal with
  | Hsafe : task_create_ext_continuation_safe ?released (task_create_ext_continuation_restore_return_program _ _ _ ?actual 66) X_boot_phase_spec
    |- context [task_tcb_init_modular_restore_output _ _ _ _ ?actual ?saved ?released] =>
    pose proof (task_create_ext_continuation_restore_phase_safe_return environment_boot_phase_spec critical_boot_phase_spec saved_local_boot_phase_spec sg_boot_phase_spec region_boot_phase_spec args_boot_phase_spec task_return_boot_phase_spec
      lower_boot_phase_spec old_frame_boot_phase_spec upper_boot_phase_spec prefix_boot_phase_spec middle_boot_phase_spec suffix_boot_phase_spec call_boot_phase_spec actual mask_boot_phase_spec saved released initial_boot_phase_spec 66 X_boot_phase_spec
      ltac:(eassumption) ltac:(lia) ltac:(assumption) ltac:(assumption) ltac:(auto) Hsafe) as Hreturn;
    unfold task_create_stack_old_image in *;
    cbn [Z.eq_dec] in Hreturn;
    sep_apply_r_atomic Hreturn
  end; entailer!.
Qed.

Lemma proof_of_OSTaskCreateExt_return_wit_5 : OSTaskCreateExt_return_wit_5.
Proof.
left; intros.
  match goal with
  | Hsafe : task_create_ext_continuation_safe ?released (task_create_ext_continuation_restore_return_program _ _ _ ?actual 60) X_boot_phase_spec
    |- context [task_tcb_init_modular_restore_output _ _ _ _ ?actual ?saved ?released] =>
    pose proof (task_create_ext_continuation_restore_phase_safe_return environment_boot_phase_spec critical_boot_phase_spec saved_local_boot_phase_spec sg_boot_phase_spec region_boot_phase_spec args_boot_phase_spec task_return_boot_phase_spec
      lower_boot_phase_spec old_frame_boot_phase_spec upper_boot_phase_spec prefix_boot_phase_spec middle_boot_phase_spec suffix_boot_phase_spec call_boot_phase_spec actual mask_boot_phase_spec saved released initial_boot_phase_spec 60 X_boot_phase_spec
      ltac:(eassumption) ltac:(lia) ltac:(assumption) ltac:(assumption) ltac:(auto) Hsafe) as Hreturn;
    unfold task_create_stack_old_image in *;
    cbn [Z.eq_dec] in Hreturn;
    sep_apply_r_atomic Hreturn
  end; entailer!.
Qed.

Lemma proof_of_OSTaskCreateExt_return_wit_6 : OSTaskCreateExt_return_wit_6.
Proof.
left; intros.
  pose proof PreH12 as Hargs.
  destruct Hargs as [_ [_ [_ [Hpriority _]]]].
  assert (Hsafe : task_create_ext_continuation_safe initial_boot_phase_spec (StateRelMonad.ret (call_boot_phase_spec, 42)) X_boot_phase_spec).
  { eapply task_create_ext_continuation_early_safe_return; [|exact PreH20].
    rewrite Hpriority, unsigned_last_nbits_eq by (change (0 <= prio_pre < 4294967296); lia); lia. }
  unfold task_create_continuation_pre, task_create_continuation_input; Intros.
  unfold task_create_ext_continuation_boot_phase_post; Exists call_boot_phase_spec initial_boot_phase_spec.
  unfold task_create_continuation_input, task_tcb_init_stack_same_call,
    task_create_stack_old_image; entailer!.
Qed.

Lemma proof_of_OSTaskCreateExt_partial_solve_wit_5_pure : OSTaskCreateExt_partial_solve_wit_5_pure.
Proof.
left; intros.
  sep_apply_l_atomic (store_uchar_range (&( "OSIntNesting" )) (task_create_stack_nesting acquired)); Intros.
  assert (Hrange : 0 <= task_create_stack_nesting acquired <= 255)
    by (change (0 <= task_create_stack_nesting acquired <= Byte.max_unsigned); assumption).
  rewrite unsigned_last_nbits_eq in PreH1 by (change (0 <= task_create_stack_nesting acquired < 4294967296); lia).
  entailer!; lia.
Qed.

Lemma proof_of_OSTaskCreateExt_partial_solve_wit_7_pure : OSTaskCreateExt_partial_solve_wit_7_pure.
Proof.
unfold OSTaskCreateExt_partial_solve_wit_7_pure; left; intros.
  prop_apply (store_uchar_range (&("OSIntNesting")) (task_create_stack_nesting acquired)).
  Intros.
  change (0 <= task_create_stack_nesting acquired <= 255) in H.
  rewrite unsigned_last_nbits_eq in PreH1 by (cbn; lia).
  entailer!.
Qed.

Lemma proof_of_OSTaskCreateExt_partial_solve_wit_17_pure : OSTaskCreateExt_partial_solve_wit_17_pure.
Proof.
unfold OSTaskCreateExt_partial_solve_wit_17_pure; left; intros.
  sep_apply_l_atomic (store_uchar_range (&("err")) retval).
  Intros.
  assert (Hrange : 0 <= retval <= 255).
  { change (0 <= retval <= Byte.max_unsigned); tauto. }
  rewrite unsigned_last_nbits_eq in PreH1 by (cbn; lia).
  pre_process; entailer!; lia.
Qed.

Lemma proof_of_OSTaskCreateExt_partial_solve_wit_18_pure : OSTaskCreateExt_partial_solve_wit_18_pure.
Proof.
unfold OSTaskCreateExt_partial_solve_wit_18_pure; left; intros.
  unfold task_create_stack_running in *.
  destruct (SchedStateDef.isRunning (SchedState current));
    pre_process; entailer!; int_auto.
Qed.

Lemma proof_of_OSTaskCreateExt_partial_solve_wit_21_pure : OSTaskCreateExt_partial_solve_wit_21_pure.
Proof.
left; intros.
  assert (retval <> 0).
  { intro Hzero; subst retval; vm_compute in PreH1; tauto. }
  entailer!.
Qed.

Lemma proof_of_OSTaskCreateExt_which_implies_wit_1 : OSTaskCreateExt_which_implies_wit_1.
Proof.
left; intros.
  sep_apply_l_atomic (task_create_name_api_pre_open environment_boot_phase_spec critical_boot_phase_spec saved_local_boot_phase_spec sg_boot_phase_spec region_boot_phase_spec args_boot_phase_spec
    task_return_boot_phase_spec lower_boot_phase_spec old_frame_boot_phase_spec upper_boot_phase_spec call_boot_phase_spec mask_boot_phase_spec initial_boot_phase_spec LitMap_boot_phase_spec literals_boot_phase_spec).
  Intros; entailer!; tauto.
Qed.

Lemma proof_of_OSTaskCreateExt_which_implies_wit_2 : OSTaskCreateExt_which_implies_wit_2.
Proof.
unfold OSTaskCreateExt_which_implies_wit_2; left; intros.
  unfold task_create_continuation_pre, task_tcb_init_continuation_save_input.
  Intros.
  pose proof PreH1 as Harguments.
  destruct PreH1 as [Hentry [Hargument [Htop [Hpriority [Hextension Hranges]]]]].
  unfold task_create_options; rewrite Hextension.
  unfold task_create_stack_old_image; entailer!.
Qed.

Lemma proof_of_OSTaskCreateExt_which_implies_wit_3 : OSTaskCreateExt_which_implies_wit_3.
Proof.
unfold OSTaskCreateExt_which_implies_wit_3; left; intros.
  unfold task_tcb_init_continuation_restore_input; Intros.
  Exists current_call_2 acquired_2.
  rewrite UCOS2_inv_split_interrupt.
  unfold task_create_stack_without_nesting, task_create_stack_nesting,
    task_tcb_init_stack_context, interrupt_inv, store_int_state,
    interrupt_inv_no_int_nesting.
  rewrite (proj1 PreH1); entailer!.
Qed.

Lemma proof_of_OSTaskCreateExt_which_implies_wit_4 : OSTaskCreateExt_which_implies_wit_4.
Proof.
unfold OSTaskCreateExt_which_implies_wit_4; left; intros.
  assert (Hsafe : task_create_ext_continuation_safe acquired_2
    (task_create_ext_continuation_restore_return_program environment_boot_phase_spec critical_boot_phase_spec sg_boot_phase_spec current_call_2 60) X_boot_phase_spec).
  { eapply task_create_ext_continuation_acquired_isr_safe; [lia|eassumption]. }
  Exists current_call_2 acquired_2.
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_stack_context,
    task_create_stack_without_nesting; Intros.
  rewrite UCOS2_inv_split_interrupt.
  unfold task_create_stack_nesting, interrupt_inv, store_int_state,
    interrupt_inv_no_int_nesting.
  rewrite (proj1 PreH1); entailer!.
Qed.

Lemma proof_of_OSTaskCreateExt_which_implies_wit_5 : OSTaskCreateExt_which_implies_wit_5.
Proof.
unfold OSTaskCreateExt_which_implies_wit_5; left; intros.
  prop_apply (store_uchar_range (&("OSIntNesting")) (task_create_stack_nesting acquired_2)).
  Intros.
  assert (Hnesting : task_create_stack_nesting acquired_2 = 0) by lia.
  Exists current_call_2 acquired_2.
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_stack_context,
    task_create_stack_without_nesting; Intros.
  rewrite UCOS2_inv_split_interrupt.
  unfold task_create_stack_nesting, interrupt_inv, store_int_state,
    interrupt_inv_no_int_nesting.
  rewrite (proj1 PreH1); entailer!.
Qed.

Lemma proof_of_OSTaskCreateExt_which_implies_wit_6 : OSTaskCreateExt_which_implies_wit_6.
Proof.
unfold OSTaskCreateExt_which_implies_wit_6; left; intros.
  subst prio.
  unfold task_tcb_init_continuation_restore_input; Intros.
  sep_apply_l_atomic (UCOS2_inv_split_priority_cell sg_boot_phase_spec acquired_2 (createPriority args_boot_phase_spec)
    ltac:(lia)).
  Exists current_call_2 acquired_2.
  unfold task_create_stack_priority, task_create_stack_without_priority,
    task_tcb_init_stack_context.
  rewrite (proj1 (proj2 PreH1)); entailer!.
Qed.

Lemma proof_of_OSTaskCreateExt_which_implies_wit_7 : OSTaskCreateExt_which_implies_wit_7.
Proof.
unfold OSTaskCreateExt_which_implies_wit_7; left; intros.
  assert (Hsafe : task_create_ext_continuation_safe (task_create_stack_reserved args_boot_phase_spec call_boot_phase_spec acquired_2)
    (task_create_ext_continuation_reserved_program environment_boot_phase_spec critical_boot_phase_spec sg_boot_phase_spec region_boot_phase_spec args_boot_phase_spec task_return_boot_phase_spec
      after_lower_boot_phase_spec after_upper_boot_phase_spec (LitMap_boot_phase_spec "?") current_call_2 mask_boot_phase_spec) X_boot_phase_spec).
  { eapply task_create_ext_continuation_acquired_free_safe; [lia|exact PreH15|eassumption]. }
  pose proof (proj1 PreH4) as Hvalid.
  assert (Hlowest : osLowestPrio sg_boot_phase_spec = 63).
  { pose proof (proj1 (proj1 Hvalid)) as Hstable.
    unfold valid_stable_glob_vars in Hstable; tauto. }
  assert (Hpriority : task_priority_in_range sg_boot_phase_spec (createPriority args_boot_phase_spec)).
  { unfold task_priority_in_range; rewrite Hlowest; lia. }
  pose proof (task_create_stack_priority_zero_is_free sg_boot_phase_spec args_boot_phase_spec acquired_2 Hvalid Hpriority PreH15) as Hfree.
  unfold task_create_stack_without_priority; Intros.
  destruct PreH1 as [Hnest [Htable Hrunning]].
  rewrite <- Htable, PreH12.
  sep_apply_l_atomic (task_create_continuation_reservation_resources environment_boot_phase_spec saved_local_boot_phase_spec sg_boot_phase_spec args_boot_phase_spec
    (LitMap_boot_phase_spec "?") call_boot_phase_spec acquired_2 PreH4 Hpriority Hfree).
  Intros.
  pose proof (task_create_runtime_flow_spec.task_create_reserve_preserves_runtime_call_input
    args_boot_phase_spec call_boot_phase_spec acquired_2 current_call_2 PreH7) as Hruntime.
  assert (Hsource : task_tcb_init_stack_source_preserved call_boot_phase_spec initial_boot_phase_spec
    (task_create_stack_reserved args_boot_phase_spec call_boot_phase_spec acquired_2)).
  { intros Hinitial; apply task_create_stack_reserve_preserves_call_source; apply PreH5; exact Hinitial. }
  assert (Hcoverage : task_stack_live_coverage
    (TskState (task_create_stack_reserved args_boot_phase_spec call_boot_phase_spec acquired_2))
    (task_stack_call_active_key current_call_2)).
  { exact PreH9. }
  assert (Hbinding : task_create_default_name_binding (LitMap_boot_phase_spec "?")
    (task_create_stack_reserved args_boot_phase_spec call_boot_phase_spec acquired_2)) by exact PreH6.
  assert (Hphase : task_create_ext_phase_frame initial_boot_phase_spec (task_create_stack_reserved args_boot_phase_spec call_boot_phase_spec acquired_2))
    by exact PreH17.
  Exists acquired_2 current_call_2.
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_stack_context.
  entailer!; try tauto.
Qed.

Lemma proof_of_OSTaskCreateExt_which_implies_wit_8 : OSTaskCreateExt_which_implies_wit_8.
Proof.
unfold OSTaskCreateExt_which_implies_wit_8; left; intros.
  pose proof (task_create_ext_arguments_options _ _ _ _ _ _ _ _ _ _ PreH1)
    as [Hoptions [Hbottom Hsize]].
  assert (Hvalid : UCOS2_state_inv sg_boot_phase_spec (task_create_stack_reserved args_boot_phase_spec call_boot_phase_spec acquired)) by exact (proj1 PreH9).
  sep_apply_l_atomic (task_create_ext_continuation_restore_phase_safe_observation environment_boot_phase_spec critical_boot_phase_spec saved_local_boot_phase_spec sg_boot_phase_spec
    current_call cpu_sr (task_create_stack_reserved args_boot_phase_spec call_boot_phase_spec acquired) _ X_boot_phase_spec ltac:(eassumption)).
  Intros stack_call checkpoint.
  assert (Hsame : task_tcb_init_stack_same_call stack_call current_call) by tauto.
  assert (Hreturned : task_tcb_init_stack_same_call stack_call call_boot_phase_spec).
  { unfold task_tcb_init_stack_same_call in *; intuition congruence. }
  assert (Hhistory : task_tcb_init_call_preserved sg_boot_phase_spec (os_sched_call_invocation current_call)
    (task_create_stack_reserved args_boot_phase_spec call_boot_phase_spec acquired) checkpoint) by tauto.
  assert (Hbinding : task_create_default_name_binding (LitMap_boot_phase_spec "?") checkpoint).
  { eapply task_create_default_name_binding_transport; [|exact PreH11].
    exact (proj2 (proj2 (proj2 (Hhistory Hvalid)))). }
  assert (Hentry : task_tcb_init_entry sg_boot_phase_spec (task_tcb_init_stack_call_args args_boot_phase_spec (LitMap_boot_phase_spec "?"))
    (os_sched_call_invocation call_boot_phase_spec) (os_sched_call_origin call_boot_phase_spec) checkpoint).
  { eapply task_tcb_init_call_history_spec.task_tcb_init_call_preserves_entry; [exact PreH9|].
    destruct PreH7 as [Hinv Hrest]; rewrite <- Hinv; exact Hhistory. }
  assert (Htail : task_tcb_init_stack_source_preserved current_call
    (task_create_stack_reserved args_boot_phase_spec call_boot_phase_spec acquired) checkpoint) by tauto.
  pose proof (task_create_runtime_flow_spec.task_create_runtime_call_input_after_return sg_boot_phase_spec args_boot_phase_spec
    current_call (task_create_stack_reserved args_boot_phase_spec call_boot_phase_spec acquired) stack_call checkpoint PreH12
    ltac:(tauto) ltac:(tauto) Htail) as Hruntime.
  assert (Hsource : task_tcb_init_stack_source_preserved call_boot_phase_spec initial_boot_phase_spec checkpoint).
  { eapply task_tcb_init_stack_source_preserved_trans; [exact PreH10|].
    exact (task_create_stack_same_call_source_preserved current_call call_boot_phase_spec
      (task_create_stack_reserved args_boot_phase_spec call_boot_phase_spec acquired) checkpoint PreH7 Htail). }
  pose proof (task_create_runtime_nesting_after_return sg_boot_phase_spec (task_create_stack_reserved args_boot_phase_spec call_boot_phase_spec acquired)
    checkpoint ltac:(tauto) PreH13) as Hzero.
  assert (Hlength : Zlength (task_create_stack_old_image lower_boot_phase_spec old_frame_boot_phase_spec upper_boot_phase_spec) = stackRegionWords region_boot_phase_spec).
  { destruct PreH14 as [[_ [_ Hwords]] [Hframe _]].
    unfold task_create_stack_old_image; rewrite !Zlength_app; cbn in Hwords; lia. }
  assert (Hregion : valid_task_stack_region region_boot_phase_spec) by exact (proj1 (proj1 (proj1 PreH14))).
  sep_apply_l_atomic (task_create_ext_clear_prepare region_boot_phase_spec args_boot_phase_spec
    (task_create_stack_old_image lower_boot_phase_spec old_frame_boot_phase_spec upper_boot_phase_spec) prefix_boot_phase_spec middle_boot_phase_spec suffix_boot_phase_spec Hregion Hlength PreH2).
  rewrite Hoptions, Hbottom, Hsize.
  pose proof (proj2 PreH8) as Hmask.
  rewrite Hmask.
  assert (Hphase : task_create_ext_phase_frame initial_boot_phase_spec checkpoint).
  { eapply task_create_ext_phase_frame_trans; [exact PreH16|].
    eapply (task_create_ext_phase_frame_control sg_boot_phase_spec); tauto. }
  Exists checkpoint stack_call.
  pose proof PreH1 as Hranges; unfold task_create_ext_arguments in Hranges.
  unfold task_tcb_init_stack_same_call in *.
  entailer!; try tauto; try lia.
Qed.

Lemma proof_of_OSTaskCreateExt_which_implies_wit_9 : OSTaskCreateExt_which_implies_wit_9.
Proof.
unfold OSTaskCreateExt_which_implies_wit_9; left; intros.
  pose proof (task_create_ext_arguments_options _ _ _ _ _ _ _ _ _ _ PreH8)
    as [Hoptions [Hbottom Hsize]].
  replace (task_stk_clr_post pbos stk_size opt middle_boot_phase_spec) with
    (task_stk_clr_post (task_create_ext_bottom args_boot_phase_spec) (task_create_ext_size args_boot_phase_spec)
      (task_create_options args_boot_phase_spec) middle_boot_phase_spec) by (rewrite Hoptions, Hbottom, Hsize; reflexivity).
  unfold task_create_stack_old_image in *.
  sep_apply_l_atomic (task_create_ext_clear_init_input environment_boot_phase_spec critical_boot_phase_spec saved_local_boot_phase_spec sg_boot_phase_spec region_boot_phase_spec args_boot_phase_spec
    task_return_boot_phase_spec lower_boot_phase_spec old_frame_boot_phase_spec upper_boot_phase_spec prefix_boot_phase_spec middle_boot_phase_spec suffix_boot_phase_spec stack_call_2 mask_boot_phase_spec checkpoint_2 PreH13 PreH9).
  Intros.
  Exists checkpoint_2 stack_call_2.
  subst after_lower_boot_phase_spec after_frame_boot_phase_spec after_upper_boot_phase_spec task_return_boot_phase_spec; entailer!.
Qed.

Lemma proof_of_OSTaskCreateExt_which_implies_wit_10 : OSTaskCreateExt_which_implies_wit_10.
Proof.
unfold OSTaskCreateExt_which_implies_wit_10; left; intros.
  assert (Hentry : task_tcb_init_entry sg_boot_phase_spec (task_tcb_init_stack_call_args args_boot_phase_spec (LitMap_boot_phase_spec "?"))
    (os_sched_call_invocation stack_call) (os_sched_call_origin stack_call) checkpoint).
  { destruct PreH3 as [Hinv [Horigin Hstack]]; rewrite Hinv, Horigin; exact PreH4. }
  rewrite <- PreH2.
  sep_apply_l_atomic (task_create_ext_continuation_init_phase_safe_tcb_pre environment_boot_phase_spec critical_boot_phase_spec saved_local_boot_phase_spec sg_boot_phase_spec region_boot_phase_spec args_boot_phase_spec
    task_return_boot_phase_spec after_lower_boot_phase_spec after_upper_boot_phase_spec (LitMap_boot_phase_spec "?") stack_call mask_boot_phase_spec checkpoint psp X_boot_phase_spec
    (proj1 PreH9) Hentry PreH7 PreH8 ltac:(eassumption)).
  Intros tcb_call tcb_initial.
  assert (Hbinding : task_create_default_name_binding (LitMap_boot_phase_spec "?") tcb_initial).
  { eapply task_create_default_name_binding_transport; [|exact PreH6]; tauto. }
  assert (Hvalid : UCOS2_state_inv sg_boot_phase_spec tcb_initial).
  { assert (Hentry_current : task_tcb_init_entry sg_boot_phase_spec (task_tcb_init_stack_call_args args_boot_phase_spec (LitMap_boot_phase_spec "?"))
      stack_call.(os_sched_call_invocation) stack_call.(os_sched_call_origin) tcb_initial) by tauto.
    exact (proj1 Hentry_current). }
  assert (Hsame : task_tcb_init_stack_same_call tcb_call stack_call) by tauto.
  assert (Hreturned : task_tcb_init_stack_same_call tcb_call call_boot_phase_spec).
  { unfold task_tcb_init_stack_same_call in *; intuition congruence. }
  assert (Hsp : psp = task_stack_init_sp TaskStackNoVFP (createStackTop args_boot_phase_spec)) by tauto.
  assert (Htail : task_tcb_init_stack_source_preserved stack_call checkpoint tcb_initial) by tauto.
  assert (Hsource : task_tcb_init_stack_source_preserved call_boot_phase_spec initial_boot_phase_spec tcb_initial).
  { eapply task_tcb_init_stack_source_preserved_trans; [exact PreH5|].
    exact (task_create_stack_same_call_source_preserved stack_call call_boot_phase_spec
      checkpoint tcb_initial PreH3 Htail). }
  assert (Htop : createStackTop args_boot_phase_spec = ptos) by exact (proj1 (proj2 (proj2 PreH10))).
  pose proof (task_create_ext_tcb_arguments args_boot_phase_spec task p_arg ptos prio id pbos stk_size pext opt psp
    (LitMap_boot_phase_spec "?") PreH10 ltac:(rewrite <- Htop; exact Hsp)) as Harguments.
  destruct PreH3 as [Hinv [Horigin Hstack]].
  rewrite Hinv, Horigin in *.
  assert (Hphase : task_create_ext_phase_frame initial_boot_phase_spec tcb_initial).
  { eapply task_create_ext_phase_frame_trans; [eassumption|]; tauto. }
  Exists tcb_initial tcb_call.
  unfold task_tcb_init_stack_same_call in *; entailer!; tauto.
Qed.

Lemma proof_of_OSTaskCreateExt_which_implies_wit_11 : OSTaskCreateExt_which_implies_wit_11.
Proof.
left; intros.
  sep_apply_l_atomic (task_create_ext_phase_tcb_result_codes environment_boot_phase_spec critical_boot_phase_spec saved_local_boot_phase_spec sg_boot_phase_spec region_boot_phase_spec args_boot_phase_spec
    (&( "OS_TaskReturn" )) after_lower_boot_phase_spec after_upper_boot_phase_spec (LitMap_boot_phase_spec "?") call_boot_phase_spec.(os_sched_call_invocation)
    call_boot_phase_spec.(os_sched_call_origin) mask_boot_phase_spec tcb_initial tcb_call err).
  Intros; assert (err = 0) by lia; subst err.
  pose proof PreH5 as [Hinvocation [Horigin Hstack]].
  rewrite <- Hinvocation, <- Horigin.
  subst task_return_boot_phase_spec.
  sep_apply_l_atomic (task_create_ext_continuation_tcb_phase_safe_success environment_boot_phase_spec critical_boot_phase_spec saved_local_boot_phase_spec sg_boot_phase_spec region_boot_phase_spec args_boot_phase_spec
    (&( "OS_TaskReturn" )) after_lower_boot_phase_spec after_upper_boot_phase_spec (LitMap_boot_phase_spec "?") tcb_call mask_boot_phase_spec tcb_initial X_boot_phase_spec PreH10 PreH11 ltac:(eassumption)).
  Intros returned current.
  assert (Hbinding : task_create_default_name_binding (LitMap_boot_phase_spec "?") current).
  { eapply task_create_default_name_binding_transport; [|exact PreH8]; tauto. }
  assert (Hsource : task_tcb_init_stack_source_preserved call_boot_phase_spec initial_boot_phase_spec current).
  { eapply task_tcb_init_stack_source_preserved_trans; [exact PreH7|].
    eapply task_create_stack_same_call_source_preserved; [exact PreH5|]; tauto. }
  assert (Hphase : task_create_ext_phase_frame initial_boot_phase_spec current).
  { eapply task_create_ext_phase_frame_trans; [eassumption|]; tauto. }
  Exists current returned.
  unfold task_tcb_init_continuation_save_input, task_create_continuation_input; Intros.
  unfold task_create_continuation_without_running, critical_region_outside,
    task_create_stack_running, task_tcb_init_continuation_capsules, task_tcb_init_stack_same_call,
    kernel_sched_ready_inv in *.
  rewrite (proj2 (proj2 PreH1)); entailer!; intuition congruence.
Qed.

Lemma proof_of_OSTaskCreateExt_which_implies_wit_12 : OSTaskCreateExt_which_implies_wit_12.
Proof.
unfold OSTaskCreateExt_which_implies_wit_12; left; intros.
  assert (Hsafe : task_create_ext_continuation_safe current_2
    (task_create_ext_continuation_schedule_program environment_boot_phase_spec critical_boot_phase_spec sg_boot_phase_spec returned_2 mask_boot_phase_spec) X_boot_phase_spec).
  { eapply task_create_ext_continuation_tcb_running_safe; eassumption. }
  assert (Hinitial_running : task_create_ext_initial_running initial_boot_phase_spec).
  { eapply task_create_ext_phase_frame_running; eassumption. }
  destruct PreH1 as [Hnest [Htable Hrunning]]; rewrite <- Hrunning.
  sep_apply_l_atomic (task_create_modular_running_sched_pre environment_boot_phase_spec critical_boot_phase_spec saved_local_boot_phase_spec sg_boot_phase_spec args_boot_phase_spec
    returned_2 mask_boot_phase_spec current_2 PreH12 PreH5 PreH10 PreH8 PreH9 PreH13 (proj2 PreH11)).
  Exists current_2 returned_2; entailer!.
Qed.

Lemma proof_of_OSTaskCreateExt_which_implies_wit_13 : OSTaskCreateExt_which_implies_wit_13.
Proof.
left; intros; unfold task_create_ext_continuation_schedule_post; Exists returned current; entailer!.
Qed.

Lemma proof_of_OSTaskCreateExt_which_implies_wit_14 : OSTaskCreateExt_which_implies_wit_14.
Proof.
left; intros; subst task_return_boot_phase_spec.
  sep_apply_l_atomic (task_create_ext_phase_tcb_result_codes environment_boot_phase_spec critical_boot_phase_spec saved_local_boot_phase_spec sg_boot_phase_spec region_boot_phase_spec args_boot_phase_spec
    (&( "OS_TaskReturn" )) after_lower_boot_phase_spec after_upper_boot_phase_spec (LitMap_boot_phase_spec "?") call_boot_phase_spec.(os_sched_call_invocation)
    call_boot_phase_spec.(os_sched_call_origin) mask_boot_phase_spec tcb_initial_2 tcb_call err).
  Intros; assert (err = 66) by tauto; subst err.
  pose proof PreH2 as [Hinvocation [Horigin Hstack]].
  rewrite <- Hinvocation, <- Horigin.
  sep_apply_l_atomic (task_create_ext_continuation_tcb_phase_safe_no_free environment_boot_phase_spec critical_boot_phase_spec saved_local_boot_phase_spec sg_boot_phase_spec region_boot_phase_spec args_boot_phase_spec
    (&( "OS_TaskReturn" )) after_lower_boot_phase_spec after_upper_boot_phase_spec (LitMap_boot_phase_spec "?") tcb_call mask_boot_phase_spec tcb_initial_2 X_boot_phase_spec ltac:(eassumption)).
  Intros released returned current.
  assert (Hphase : task_create_ext_phase_frame initial_boot_phase_spec current).
  { eapply task_create_ext_phase_frame_trans; [eassumption|]; tauto. }
  Exists tcb_initial_2 released current returned.
  unfold task_create_stack_no_free_history, task_tcb_init_stack_same_call,
    task_tcb_init_stack_return_preserved, task_tcb_init_stack_source_preserved,
    kernel_call_task_source, task_execution_current in *.
  rewrite Hinvocation, Horigin, Hstack in *; entailer!; intuition congruence.
Qed.

Lemma proof_of_OSTaskCreateExt_which_implies_wit_15 : OSTaskCreateExt_which_implies_wit_15.
Proof.
left; intros; subst prio.
  unfold task_create_stack_no_free_history; Intros.
  assert (Hentry : task_tcb_init_entry sg_boot_phase_spec (task_tcb_init_stack_call_args args_boot_phase_spec (LitMap_boot_phase_spec "?"))
    call_boot_phase_spec.(os_sched_call_invocation) call_boot_phase_spec.(os_sched_call_origin) tcb_initial_2) by tauto.
  assert (Hresult : task_tcb_init_call_result sg_boot_phase_spec (task_tcb_init_stack_call_args args_boot_phase_spec (LitMap_boot_phase_spec "?"))
    call_boot_phase_spec.(os_sched_call_invocation) call_boot_phase_spec.(os_sched_call_origin) tcb_initial_2 66 released_2) by tauto.
  assert (Hcheckpoint : UCOS2_state_inv sg_boot_phase_spec checkpoint) by tauto.
  assert (Hpreserved : task_tcb_init_stack_return_preserved call_boot_phase_spec released_2 checkpoint) by tauto.
  sep_apply_l_atomic (task_create_ext_continuation_save_phase_safe_no_free environment_boot_phase_spec critical_boot_phase_spec saved_local_boot_phase_spec sg_boot_phase_spec
    (task_tcb_init_stack_call_args args_boot_phase_spec (LitMap_boot_phase_spec "?")) call_boot_phase_spec checkpoint_call mask_boot_phase_spec cpu_sr
    tcb_initial_2 released_2 checkpoint X_boot_phase_spec PreH4 Hresult Hcheckpoint Hpreserved args_boot_phase_spec ltac:(eassumption)).
  Intros returned acquired.
  assert (Hphase : task_create_ext_phase_frame initial_boot_phase_spec acquired).
  { eapply task_create_ext_phase_frame_trans; [eassumption|]; tauto. }
  Exists tcb_initial_2 released_2 acquired returned.
  assert (Hvalid : UCOS2_state_inv sg_boot_phase_spec acquired) by tauto.
  assert (Hprio : (task_tcb_init_stack_call_args args_boot_phase_spec (LitMap_boot_phase_spec "?")).(initPrio) = args_boot_phase_spec.(createPriority)).
  { unfold task_tcb_init_stack_call_args, task_create_tcb_args; destruct args_boot_phase_spec.(createExtension); reflexivity. }
  pose proof (proj1 (task_tcb_init_entry_priority_in_range _ _ _ _ _ Hentry)) as Hrange.
  rewrite Hprio in Hrange.
  pose proof (UCOS2_inv_split_priority_cell sg_boot_phase_spec acquired args_boot_phase_spec.(createPriority) Hrange) as Hsplit.
  assert (Hfold : UCOS2_raw_rep sg_boot_phase_spec acquired |-- UCOS2_inv sg_boot_phase_spec acquired)
    by (unfold UCOS2_inv; entailer!).
  sep_apply_l_atomic Hfold.
  sep_apply_l_atomic Hsplit.
  unfold task_create_stack_without_priority, task_create_stack_priority,
    task_tcb_init_stack_same_call in *.
  rewrite (proj1 (proj2 PreH1)); entailer!; intuition congruence.
Qed.

Lemma proof_of_OSTaskCreateExt_which_implies_wit_16 : OSTaskCreateExt_which_implies_wit_16.
Proof.
left; intros.
  assert (Hsafe : task_create_ext_continuation_safe (task_create_stack_rolled_back args_boot_phase_spec acquired_2)
    (task_create_ext_continuation_restore_return_program environment_boot_phase_spec critical_boot_phase_spec sg_boot_phase_spec current_call_2 66) X_boot_phase_spec).
  { eapply task_create_ext_continuation_update_safe_step; eassumption. }
  unfold task_create_stack_no_free_history, task_create_stack_without_priority; Intros.
  assert (Hentry : task_tcb_init_entry sg_boot_phase_spec (task_tcb_init_stack_call_args args_boot_phase_spec (LitMap_boot_phase_spec "?"))
    (os_sched_call_invocation call_boot_phase_spec) (os_sched_call_origin call_boot_phase_spec) tcb_initial) by tauto.
  assert (Hresult : task_tcb_init_call_result sg_boot_phase_spec (task_tcb_init_stack_call_args args_boot_phase_spec (LitMap_boot_phase_spec "?"))
    (os_sched_call_invocation call_boot_phase_spec) (os_sched_call_origin call_boot_phase_spec) tcb_initial 66 released) by tauto.
  assert (Hvalid : UCOS2_state_inv sg_boot_phase_spec acquired_2) by tauto.
  assert (Hprevious : task_tcb_init_stack_return_preserved call_boot_phase_spec released acquired_2) by tauto.
  destruct Hprevious as [Hframe [Hactive Hsource]].
  pose proof (proj1 (task_create_tcb_args_common_fields args_boot_phase_spec
    (task_stack_init_sp TaskStackNoVFP (createStackTop args_boot_phase_spec)) (LitMap_boot_phase_spec "?"))) as Hpriority.
  change (initPrio (task_tcb_init_stack_call_args args_boot_phase_spec (LitMap_boot_phase_spec "?")) = createPriority args_boot_phase_spec) in Hpriority.
  subst prio.
  destruct PreH1 as [_ [Htable _]].
  rewrite <- Htable.
  pose proof (task_create_continuation_no_free_rollback_resources environment_boot_phase_spec critical_boot_phase_spec saved_local_boot_phase_spec sg_boot_phase_spec
    (task_tcb_init_stack_call_args args_boot_phase_spec (LitMap_boot_phase_spec "?")) (os_sched_call_invocation call_boot_phase_spec)
    (os_sched_call_origin call_boot_phase_spec) tcb_initial released acquired_2 Hentry Hresult Hvalid Hframe Hactive) as Hrollback.
  rewrite Hpriority in Hrollback.
  sep_apply_l_atomic Hrollback; Intros.
  assert (Hphase : task_create_ext_phase_frame initial_boot_phase_spec (task_create_stack_rolled_back args_boot_phase_spec acquired_2)).
  { change (task_create_ext_phase_frame initial_boot_phase_spec acquired_2); assumption. }
  Exists acquired_2 current_call_2.
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_stack_context,
    task_create_stack_rolled_back.
  assert (Hcoverage : task_stack_live_coverage
    (task_rollback_reservation (TskState acquired_2) (createPriority args_boot_phase_spec))
    (task_stack_call_active_key current_call_2)).
  { eapply task_stack_live_coverage_used_map_frame;
      [|reflexivity|exact PreH4].
    intros slot node Hnode; exists node; split; [exact Hnode|reflexivity]. }
  entailer!.
Qed.

Lemma proof_of_OSTaskCreateExt_which_implies_wit_17 : OSTaskCreateExt_which_implies_wit_17.
Proof.
unfold OSTaskCreateExt_which_implies_wit_17; left; intros.
  assert (Hsafe : task_create_ext_continuation_safe acquired_2
    (task_create_ext_continuation_restore_return_program environment_boot_phase_spec critical_boot_phase_spec sg_boot_phase_spec current_call_2 40) X_boot_phase_spec).
  { eapply task_create_ext_continuation_acquired_occupied_safe; [lia|eassumption|eassumption]. }
  unfold task_create_stack_without_priority; Intros.
  unfold task_create_stack_priority.
  rewrite <- PreH10.
  pose proof (Ucos2Verify.lib.array_abstraction.store_prio_tbl_merge_cell
    sg_boot_phase_spec (prioTbl (TskState acquired_2)) prio ltac:(lia))
    as Hmerge.
  rewrite (proj1 (proj2 PreH1)) in Hmerge.
  sep_apply Hmerge.
  Exists current_call_2 acquired_2.
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_stack_context,
    UCOS2_inv.
  rewrite UCOS2_raw_rep_priority_table_equiv; entailer!.
Qed.

Lemma proof_of_OSTaskCreateExt_derive_api_spec_by_boot_phase_spec : OSTaskCreateExt_derive_api_spec_by_boot_phase_spec.
Proof.
unfold OSTaskCreateExt_derive_api_spec_by_boot_phase_spec; intros.
  Exists environment_api_spec saved_local_api_spec critical_api_spec sg_api_spec args_api_spec
    region_api_spec task_return_api_spec lower_api_spec old_frame_api_spec upper_api_spec
    prefix_api_spec middle_api_spec suffix_api_spec after_lower_api_spec after_frame_api_spec
    after_upper_api_spec call_api_spec mask_api_spec initial_api_spec.
  Exists LitMap_api_spec literals_api_spec X_api_spec.
  entailer!.
  apply_sepcon_adjoint; elim_emp.
  Intros result.
  sep_apply_l_atomic (task_create_ext_continuation_boot_phase_post_forget environment_api_spec critical_api_spec
    saved_local_api_spec sg_api_spec region_api_spec args_api_spec task_return_api_spec
    lower_api_spec old_frame_api_spec upper_api_spec prefix_api_spec middle_api_spec suffix_api_spec
    call_api_spec mask_api_spec initial_api_spec result X_api_spec).
  Exists result; entailer!.
Qed.
