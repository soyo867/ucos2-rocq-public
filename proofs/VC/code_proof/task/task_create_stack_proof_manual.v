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
From Ucos2Verify.VC.code.task Require Import task_create_stack_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_calls_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.array_abstraction Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_name_api_spec.
Local Open Scope sac.

Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_modular_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_runtime_consumer_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_runtime_flow_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_modular_init_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_call_protocol_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_modular_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_runtime_consumer_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_runtime_flow_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_modular_init_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Lemma proof_of_OSTaskCreate_entail_wit_1 : OSTaskCreate_entail_wit_1.
Proof.
  left; intros.
  match goal with
  | Hentry : task_create_stack_entry sg args (LitMap "?") call initial,
    Hsafe : task_create_safe initial (task_create_program _ _ _ _ _ _ _ _ _ _ _) X |- _ =>
    sep_apply_l_atomic (task_create_save_safe_entry environment critical saved_local sg region args
      task_return lower upper (LitMap "?") call mask retval initial X ltac:(lia) Hentry ltac:(assumption) Hsafe)
  end.
  Intros returned acquired.
  assert (Hbinding : task_create_default_name_binding (LitMap "?") acquired).
  { eapply task_create_default_name_binding_transport; [|eassumption]; tauto. }
  Exists returned acquired; entailer!; tauto.
Qed.

Lemma proof_of_OSTaskCreate_return_wit_1 : OSTaskCreate_return_wit_1.
Proof.
  left; intros.
  match goal with
  | Hsafe : task_create_safe ?released (task_create_restore_return_program _ _ _ ?actual 40) X
    |- context [task_tcb_init_modular_restore_output _ _ _ _ ?actual ?saved ?released] =>
    pose proof (task_create_restore_safe_return environment critical saved_local sg region args task_return
      lower old_frame upper call actual mask saved released 40 false X
      ltac:(assumption) ltac:(assumption) ltac:(auto) Hsafe) as Hreturn;
    unfold task_create_stack_failure_buffer, task_create_stack_old_image in Hreturn;
    sep_apply_l_atomic Hreturn
  end.
  entailer!.
Qed.

Lemma proof_of_OSTaskCreate_return_wit_3 : OSTaskCreate_return_wit_3.
Proof.
  left; intros; subst retval.
  assert (Hstopped : task_create_stack_running current <> 1).
  { match goal with H : unsigned_last_nbits (task_create_stack_running current) 32 <> 1 |- _ =>
      rewrite unsigned_last_nbits_eq in H;
      [exact H|unfold task_create_stack_running; destruct current.(SchedState).(isRunning); cbn; lia]
    end. }
  assert (Hsafe : task_create_safe current (StateRelMonad.ret 0) X).
  { eapply task_create_tcb_stopped_safe; eassumption. }
  unfold task_create_api_post; Exists returned current.
  destruct (Z.eq_dec 0 0); [|contradiction].
  unfold task_tcb_init_continuation_save_input, task_create_continuation_input, task_create_continuation_without_running,
    critical_region_outside, task_create_stack_running, task_tcb_init_continuation_capsules.
  match goal with H : task_create_stack_global_addresses sg _ _ _ |- _ =>
    rewrite (proj2 (proj2 H))
  end; entailer!.
Qed.

Lemma proof_of_OSTaskCreate_return_wit_4 : OSTaskCreate_return_wit_4.
Proof.
  left; intros; subst retval.
  pose proof (task_create_restore_safe_return environment critical saved_local sg region args task_return
    lower old_frame upper call current_call_7 mask retval_3 (task_create_stack_rolled_back args acquired_7)
    66 true X PreH1 PreH2 ltac:(auto) PreH3) as Hreturn.
  unfold task_create_stack_failure_buffer, task_create_stack_old_image in Hreturn.
  sep_apply_r_atomic Hreturn; entailer!.
Qed.

Lemma proof_of_OSTaskCreate_return_wit_5 : OSTaskCreate_return_wit_5.
Proof.
  left; intros.
  match goal with
  | Hsafe : task_create_safe ?released (task_create_restore_return_program _ _ _ ?actual 60) X
    |- context [task_tcb_init_modular_restore_output _ _ _ _ ?actual ?saved ?released] =>
    pose proof (task_create_restore_safe_return environment critical saved_local sg region args task_return
      lower old_frame upper call actual mask saved released 60 false X
      ltac:(assumption) ltac:(assumption) ltac:(auto) Hsafe) as Hreturn;
    unfold task_create_stack_failure_buffer, task_create_stack_old_image in Hreturn;
    sep_apply_l_atomic Hreturn
  end.
  entailer!.
Qed.

Lemma proof_of_OSTaskCreate_return_wit_6 : OSTaskCreate_return_wit_6.
Proof.
  left; intros; unfold task_create_continuation_pre; Intros.
  assert (Hvalid : UCOS2_state_inv sg initial) by
    (unfold task_create_stack_entry in *; tauto).
  assert (Hsafe : task_create_safe initial (StateRelMonad.ret 42) X).
  { eapply task_create_early_safe_return; [|exact PreH11].
    unfold task_create_stack_arguments in PreH6; rewrite (proj2 (proj2 (proj2 (proj2 PreH6)))); lia. }
  unfold task_create_api_post; Exists call initial.
  destruct (Z.eq_dec 42 0); [lia|]; Exists false.
  unfold task_create_stack_failure_buffer, task_tcb_init_stack_same_call.
  entailer!.
Qed.

Lemma proof_of_OSTaskCreate_partial_solve_wit_2_pure : OSTaskCreate_partial_solve_wit_2_pure.
Proof.
  left; intros; sep_apply_l_atomic (store_uchar_range (&( "prio" )) prio_pre); Intros.
  assert (Hrange : 0 <= prio_pre <= 255) by (change (0 <= prio_pre <= Byte.max_unsigned); assumption).
  rewrite unsigned_last_nbits_eq in PreH1 by (change (0 <= prio_pre < 4294967296); lia).
  entailer!; lia.
Qed.

Lemma proof_of_OSTaskCreate_partial_solve_wit_7_pure : OSTaskCreate_partial_solve_wit_7_pure.
Proof.
  left; intros.
  sep_apply_l_atomic (store_uchar_range (&( "OSIntNesting" )) (task_create_stack_nesting acquired)); Intros.
  assert (Hrange : 0 <= task_create_stack_nesting acquired <= 255)
    by (change (0 <= task_create_stack_nesting acquired <= Byte.max_unsigned); assumption).
  rewrite unsigned_last_nbits_eq in PreH1 by (change (0 <= task_create_stack_nesting acquired < 4294967296); lia).
  entailer!.
Qed.
Lemma proof_of_OSTaskCreate_partial_solve_wit_15_pure : OSTaskCreate_partial_solve_wit_15_pure.
Proof.
  left; intros; sep_apply_l_atomic (store_uchar_range (&( "err" )) retval); Intros.
  assert (Hrange : 0 <= retval <= 255) by (change (0 <= retval <= Byte.max_unsigned); assumption).
  rewrite unsigned_last_nbits_eq in PreH1 by (change (0 <= retval < 4294967296); lia).
  entailer!; lia.
Qed.

Lemma proof_of_OSTaskCreate_partial_solve_wit_16_pure : OSTaskCreate_partial_solve_wit_16_pure.
Proof.
  left; intros.
  assert (Hrange : 0 <= task_create_stack_running current < 4294967296).
  { unfold task_create_stack_running; destruct current.(SchedState).(isRunning); simpl; lia. }
  match goal with
  | H : unsigned_last_nbits (task_create_stack_running current) 32 = 1 |- _ =>
      rewrite unsigned_last_nbits_eq in H by exact Hrange
  end.
  entailer!.
Qed.

Lemma proof_of_OSTaskCreate_partial_solve_wit_19_pure : OSTaskCreate_partial_solve_wit_19_pure.
Proof.
  left; intros; entailer!.
  intro Hequal; subst retval; cbv in PreH1; contradiction.
Qed.

Lemma proof_of_OSTaskCreate_which_implies_wit_2 : OSTaskCreate_which_implies_wit_2.
Proof.
  left; intros; unfold task_create_continuation_pre, task_create_stack_old_image; Intros.
  destruct PreH1 as [Hbasic [Htask [Hargument [Htop Hpriority]]]].
  assert (Hoptions : task_create_options args = 0).
  { unfold task_create_options; rewrite Hbasic; reflexivity. }
  unfold task_create_stack_arguments; entailer!; tauto.
Qed.

Lemma proof_of_OSTaskCreate_which_implies_wit_3 : OSTaskCreate_which_implies_wit_3.
Proof.
  left; intros; Exists current_call_2 acquired_2.
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_stack_context, task_tcb_init_continuation_capsules.
  rewrite task_create_stack_inv_split_nesting, (proj1 PreH1); entailer!.
Qed.

Lemma proof_of_OSTaskCreate_which_implies_wit_4 : OSTaskCreate_which_implies_wit_4.
Proof.
  left; intros.
  assert (Hsafe : task_create_safe acquired_2 (task_create_restore_return_program environment critical sg current_call_2 60) X).
  { eapply task_create_acquired_isr_safe; eassumption. }
  Exists current_call_2 acquired_2.
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_stack_context, task_tcb_init_continuation_capsules.
  rewrite task_create_stack_inv_split_nesting, (proj1 PreH1); entailer!.
Qed.

Lemma proof_of_OSTaskCreate_which_implies_wit_5 : OSTaskCreate_which_implies_wit_5.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range (&( "OSIntNesting" )) (task_create_stack_nesting acquired_2)); Intros_p Hrange.
  assert (Hzero : task_create_stack_nesting acquired_2 = 0) by lia.
  Exists current_call_2 acquired_2.
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_stack_context, task_tcb_init_continuation_capsules.
  rewrite task_create_stack_inv_split_nesting, (proj1 PreH1); entailer!.
Qed.

Lemma proof_of_OSTaskCreate_which_implies_wit_6 : OSTaskCreate_which_implies_wit_6.
Proof.
  left; intros; subst prio; Exists current_call_2 acquired_2.
  unfold task_tcb_init_continuation_restore_input; Intros.
  sep_apply_l_atomic (UCOS2_inv_split_priority_cell sg acquired_2 args.(createPriority) ltac:(lia)).
  unfold task_create_stack_without_priority, task_create_stack_priority,
    task_tcb_init_stack_context, task_tcb_init_continuation_capsules.
  rewrite (proj1 (proj2 PreH1)); entailer!.
Qed.

Lemma proof_of_OSTaskCreate_which_implies_wit_7 : OSTaskCreate_which_implies_wit_7.
Proof.
  left; intros; subst prio.
  assert (Hsafe : task_create_safe (task_create_stack_reserved args call acquired_2)
    (task_create_reserved_program environment critical sg region args task_return lower upper (LitMap "?") current_call_2 mask) X).
  { eapply task_create_acquired_free_safe; [lia|exact PreH15|eassumption]. }
  pose proof (proj1 PreH4) as Hvalid.
  assert (Hlowest : sg.(osLowestPrio) = 63).
  { pose proof (proj1 (proj1 Hvalid)) as Hstable; unfold valid_stable_glob_vars in Hstable; tauto. }
  assert (Hpriority : task_priority_in_range sg args.(createPriority)).
  { unfold task_priority_in_range; rewrite Hlowest; lia. }
  pose proof (task_create_stack_priority_zero_is_free sg args acquired_2 Hvalid Hpriority PreH15) as Hfree.
  Exists acquired_2 current_call_2.
  unfold task_create_stack_without_priority; Intros.
  rewrite <- (proj1 (proj2 PreH1)).
  sep_apply_l_atomic (task_create_continuation_reservation_resources environment saved_local sg args (LitMap "?")
    call acquired_2 PreH4 Hpriority Hfree).
  Intros.
  assert (Hsource : task_tcb_init_stack_source_preserved call initial
    (task_create_stack_reserved args call acquired_2)).
  { intros Hordinary; apply task_create_stack_reserve_preserves_call_source.
    apply PreH5; exact Hordinary. }
  pose proof (task_create_reserve_preserves_runtime_call_input args call acquired_2 current_call_2 PreH7) as Hruntime.
  assert (Hbinding : task_create_default_name_binding (LitMap "?")
    (task_create_stack_reserved args call acquired_2)) by exact PreH6.
  unfold task_create_stack_reserved, task_tcb_init_continuation_restore_input,
    task_tcb_init_stack_context; entailer!; tauto.
Qed.

Lemma proof_of_OSTaskCreate_which_implies_wit_8 : OSTaskCreate_which_implies_wit_8.
Proof.
  left; intros.
  sep_apply_l_atomic (task_create_restore_safe_observation environment critical saved_local sg
    current_call cpu_sr (task_create_stack_reserved args call acquired) _ X ltac:(eassumption)).
  Intros returned checkpoint.
  assert (Hobserved : task_tcb_init_call_preserved sg current_call.(os_sched_call_invocation)
    (task_create_stack_reserved args call acquired) checkpoint) by tauto.
  assert (Hinterval : task_tcb_init_call_preserved sg call.(os_sched_call_invocation)
    (task_create_stack_reserved args call acquired) checkpoint).
  { rewrite (proj1 PreH2) in Hobserved; exact Hobserved. }
  assert (Hbinding : task_create_default_name_binding (LitMap "?") checkpoint).
  { eapply task_create_default_name_binding_transport; [|exact PreH6].
    exact (proj2 (proj2 (proj2 (Hinterval (proj1 PreH4))))). }
  pose proof (task_tcb_init_call_preserves_entry sg (task_tcb_init_stack_call_args args (LitMap "?"))
    call.(os_sched_call_invocation) call.(os_sched_call_origin)
    (task_create_stack_reserved args call acquired) checkpoint PreH4 Hinterval) as Hentry.
  assert (Hafter : task_tcb_init_stack_source_preserved current_call
    (task_create_stack_reserved args call acquired) checkpoint) by (pose proof (proj1 PreH4); tauto).
  assert (Hsource : task_tcb_init_stack_source_preserved call initial checkpoint).
  { eapply task_tcb_init_stack_source_preserved_trans; [exact PreH5|].
    exact (task_create_stack_same_call_source_preserved current_call call _ _ PreH2 Hafter). }
  assert (Hnormal : kernel_call_normal_return current_call (task_create_stack_reserved args call acquired)
    returned checkpoint) by tauto.
  assert (Hcontrol : kernel_call_control_rely sg (task_create_stack_reserved args call acquired) checkpoint) by tauto.
  pose proof (task_create_runtime_call_input_after_return sg args current_call
    (task_create_stack_reserved args call acquired) returned checkpoint PreH7 Hcontrol Hnormal Hafter) as Hruntime.
  pose proof (task_create_runtime_nesting_after_return sg _ _ Hcontrol PreH8) as Hzero.
  assert (Hsame : task_tcb_init_stack_same_call returned call).
  { destruct PreH2 as [Hi [Ho Hstack]]. destruct (proj1 Hnormal) as [Hi' [Ho' Hstack']].
    unfold task_tcb_init_stack_same_call; repeat split; congruence. }
  pose proof PreH9 as [Hlayout [Hlength [Htask [Hargument Hreturn]]]].
  unfold task_create_stack_old_image.
  sep_apply_l_atomic (task_create_stack_storage_init_pre TaskStackNoVFP region args task_return
    lower old_frame upper Hlayout Hlength Htask Hargument Hreturn).
  Exists checkpoint returned.
  unfold task_create_continuation_init_input; rewrite <- PreH1, (proj2 PreH3); entailer!; tauto.
Qed.

Lemma proof_of_OSTaskCreate_which_implies_wit_9 : OSTaskCreate_which_implies_wit_9.
Proof.
  left; intros; rewrite <- PreH2.
  pose proof PreH3 as [Hinvocation [Horigin Hstack]].
  assert (Hentry : task_tcb_init_entry sg (task_tcb_init_stack_call_args args (LitMap "?"))
    stack_call.(os_sched_call_invocation) stack_call.(os_sched_call_origin) checkpoint).
  { rewrite Hinvocation, Horigin; exact PreH4. }
  sep_apply_l_atomic (task_create_init_safe_tcb_pre environment critical saved_local sg region args
    task_return lower upper (LitMap "?") stack_call mask checkpoint psp X (proj1 PreH9) Hentry PreH7 PreH8 ltac:(eassumption)).
  Intros returned current.
  assert (Hbinding : task_create_default_name_binding (LitMap "?") current).
  { eapply task_create_default_name_binding_transport; [|exact PreH6]; tauto. }
  assert (Hvalid : UCOS2_state_inv sg current).
  { assert (Hentry_current : task_tcb_init_entry sg (task_tcb_init_stack_call_args args (LitMap "?"))
      stack_call.(os_sched_call_invocation) stack_call.(os_sched_call_origin) current) by tauto.
    exact (proj1 Hentry_current). }
  Exists current returned.
  assert (Hsource : task_tcb_init_stack_source_preserved call initial current).
  { eapply task_tcb_init_stack_source_preserved_trans; [exact PreH5|].
    eapply task_create_stack_same_call_source_preserved; [exact PreH3|]; tauto. }
  pose proof PreH10 as [Hbasic [Htask [Hargument [Htop Hpriority]]]].
  unfold task_tcb_init_stack_same_call in *; rewrite Hinvocation, Horigin in *.
  assert (Harguments : task_tcb_init_arguments (task_tcb_init_stack_call_args args (LitMap "?"))
    prio psp 0 0 0 0 0 (LitMap "?")).
  { unfold task_tcb_init_arguments, task_tcb_init_stack_call_args, task_create_tcb_args.
    rewrite Hbasic; cbn; intuition congruence. }
  entailer!; intuition congruence.
Qed.

Lemma proof_of_OSTaskCreate_which_implies_wit_10 : OSTaskCreate_which_implies_wit_10.
Proof.
  left; intros.
  sep_apply_l_atomic (task_create_name_tcb_result_codes environment critical saved_local sg region args
    (&( "OS_TaskReturn" )) lower upper (LitMap "?") call.(os_sched_call_invocation)
    call.(os_sched_call_origin) mask tcb_initial tcb_call err).
  Intros; assert (err = 0) by lia; subst err.
  pose proof PreH5 as [Hinvocation [Horigin Hstack]].
  rewrite <- Hinvocation, <- Horigin.
  subst task_return.
  sep_apply_l_atomic (task_create_tcb_safe_success environment critical saved_local sg region args
    (&( "OS_TaskReturn" )) lower upper (LitMap "?") tcb_call mask tcb_initial X PreH10 PreH11 ltac:(eassumption)).
  Intros returned current.
  assert (Hsource : task_tcb_init_stack_source_preserved call initial current).
  { eapply task_tcb_init_stack_source_preserved_trans; [exact PreH7|].
    eapply task_create_stack_same_call_source_preserved; [exact PreH5|]; tauto. }
  assert (Hbinding : task_create_default_name_binding (LitMap "?") current).
  { eapply task_create_default_name_binding_transport; [|exact PreH8]; tauto. }
  Exists current returned.
  unfold task_tcb_init_continuation_save_input, task_create_continuation_input; Intros.
  unfold task_create_continuation_without_running, critical_region_outside,
    task_create_stack_running, task_tcb_init_continuation_capsules, task_tcb_init_stack_same_call,
    kernel_sched_ready_inv in *.
  rewrite (proj2 (proj2 PreH1)); entailer!; intuition congruence.
Qed.

Lemma proof_of_OSTaskCreate_which_implies_wit_11 : OSTaskCreate_which_implies_wit_11.
Proof.
  left; intros.
  assert (Hsafe : task_create_safe current_2 (task_create_schedule_program environment critical sg returned_2 mask) X).
  { eapply task_create_tcb_running_safe; eassumption. }
  Exists current_2 returned_2.
  destruct PreH1 as [Hnesting [Hpriority Hrunning]].
  rewrite <- Hrunning.
  sep_apply_l_atomic (task_create_modular_running_sched_pre environment critical saved_local sg args returned_2 mask current_2
    PreH12 PreH5 PreH10 PreH8 PreH9 PreH13 (proj2 PreH11)).
  entailer!.
Qed.

Lemma proof_of_OSTaskCreate_which_implies_wit_12 : OSTaskCreate_which_implies_wit_12.
Proof.
  left; intros; unfold task_create_schedule_post; Exists returned current; entailer!.
Qed.

Lemma proof_of_OSTaskCreate_which_implies_wit_13 : OSTaskCreate_which_implies_wit_13.
Proof.
  left; intros; subst task_return.
  sep_apply_l_atomic (task_create_name_tcb_result_codes environment critical saved_local sg region args
    (&( "OS_TaskReturn" )) lower upper (LitMap "?") call.(os_sched_call_invocation)
    call.(os_sched_call_origin) mask tcb_initial_2 tcb_call err).
  Intros; assert (err = 66) by tauto; subst err.
  pose proof PreH2 as [Hinvocation [Horigin Hstack]].
  rewrite <- Hinvocation, <- Horigin.
  sep_apply_l_atomic (task_create_tcb_safe_no_free environment critical saved_local sg region args
    (&( "OS_TaskReturn" )) lower upper (LitMap "?") tcb_call mask tcb_initial_2 X ltac:(eassumption)).
  Intros released returned current; Exists tcb_initial_2 released current returned.
  unfold task_create_stack_no_free_history, task_tcb_init_stack_same_call,
    task_tcb_init_stack_return_preserved, task_tcb_init_stack_source_preserved,
    kernel_call_task_source, task_execution_current in *.
  rewrite Hinvocation, Horigin, Hstack in *; entailer!; intuition congruence.
Qed.

Lemma proof_of_OSTaskCreate_which_implies_wit_14 : OSTaskCreate_which_implies_wit_14.
Proof.
  left; intros; subst prio.
  unfold task_create_stack_no_free_history; Intros.
  assert (Hentry : task_tcb_init_entry sg (task_tcb_init_stack_call_args args (LitMap "?"))
    call.(os_sched_call_invocation) call.(os_sched_call_origin) tcb_initial_2) by tauto.
  assert (Hresult : task_tcb_init_call_result sg (task_tcb_init_stack_call_args args (LitMap "?"))
    call.(os_sched_call_invocation) call.(os_sched_call_origin) tcb_initial_2 66 released_2) by tauto.
  assert (Hcheckpoint : UCOS2_state_inv sg checkpoint) by tauto.
  assert (Hpreserved : task_tcb_init_stack_return_preserved call released_2 checkpoint) by tauto.
  sep_apply_l_atomic (task_create_save_safe_no_free environment critical saved_local sg
    (task_tcb_init_stack_call_args args (LitMap "?")) call checkpoint_call mask cpu_sr
    tcb_initial_2 released_2 checkpoint X PreH4 Hresult Hcheckpoint Hpreserved args ltac:(eassumption)).
  Intros returned acquired; Exists tcb_initial_2 released_2 acquired returned.
  assert (Hvalid : UCOS2_state_inv sg acquired) by tauto.
  assert (Hprio : (task_tcb_init_stack_call_args args (LitMap "?")).(initPrio) = args.(createPriority)).
  { unfold task_tcb_init_stack_call_args, task_create_tcb_args; destruct args.(createExtension); reflexivity. }
  pose proof (proj1 (task_tcb_init_entry_priority_in_range _ _ _ _ _ Hentry)) as Hrange.
  rewrite Hprio in Hrange.
  pose proof (UCOS2_inv_split_priority_cell sg acquired args.(createPriority) Hrange) as Hsplit.
  assert (Hfold : UCOS2_raw_rep sg acquired |-- UCOS2_inv sg acquired)
    by (unfold UCOS2_inv; entailer!).
  sep_apply_l_atomic Hfold.
  sep_apply_l_atomic Hsplit.
  unfold task_create_stack_without_priority, task_create_stack_priority,
    task_tcb_init_stack_same_call in *.
  rewrite (proj1 (proj2 PreH1)); entailer!; intuition congruence.
Qed.

Lemma proof_of_OSTaskCreate_which_implies_wit_15 : OSTaskCreate_which_implies_wit_15.
Proof.
  left; intros; subst prio.
  assert (Hsafe : task_create_safe (task_create_stack_rolled_back args acquired_2)
    (task_create_restore_return_program environment critical sg current_call_2 66) X).
  { eapply task_create_update_safe_step; eassumption. }
  Exists acquired_2 current_call_2.
  unfold task_create_stack_no_free_history, task_create_stack_without_priority; Intros.
  assert (Hentry : task_tcb_init_entry sg (task_tcb_init_stack_call_args args (LitMap "?"))
    call.(os_sched_call_invocation) call.(os_sched_call_origin) tcb_initial) by tauto.
  assert (Hresult : task_tcb_init_call_result sg (task_tcb_init_stack_call_args args (LitMap "?"))
    call.(os_sched_call_invocation) call.(os_sched_call_origin) tcb_initial 66 released) by tauto.
  assert (Hvalid : UCOS2_state_inv sg acquired_2) by tauto.
  assert (Hpreserved : task_tcb_init_stack_return_preserved call released acquired_2) by tauto.
  assert (Hprio : (task_tcb_init_stack_call_args args (LitMap "?")).(initPrio) = args.(createPriority)).
  { unfold task_tcb_init_stack_call_args, task_create_tcb_args; destruct args.(createExtension); reflexivity. }
  pose proof (task_create_continuation_no_free_rollback_resources environment critical saved_local sg
    (task_tcb_init_stack_call_args args (LitMap "?")) call.(os_sched_call_invocation)
    call.(os_sched_call_origin) tcb_initial released acquired_2 Hentry Hresult Hvalid
    (proj1 Hpreserved) (proj1 (proj2 Hpreserved))) as Hrollback.
  rewrite Hprio in Hrollback.
  rewrite <- (proj1 (proj2 PreH1)); sep_apply_l_atomic Hrollback; Intros.
  unfold task_create_stack_rolled_back, task_tcb_init_continuation_restore_input,
    task_tcb_init_stack_context; entailer!.
Qed.

Lemma proof_of_OSTaskCreate_which_implies_wit_16 : OSTaskCreate_which_implies_wit_16.
Proof.
  left; intros; subst prio.
  assert (Hsafe : task_create_safe acquired_2 (task_create_restore_return_program environment critical sg current_call_2 40) X).
  { eapply task_create_acquired_occupied_safe; eassumption. }
  Exists current_call_2 acquired_2.
  unfold task_create_stack_without_priority, task_create_stack_priority; Intros.
  rewrite <- (proj1 (proj2 PreH1)).
  sep_apply_l_atomic (store_prio_tbl_merge_cell sg acquired_2.(TskState).(prioTbl)
    args.(createPriority) ltac:(lia)).
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_stack_context,
    task_tcb_init_continuation_capsules, UCOS2_inv.
  rewrite UCOS2_raw_rep_priority_table_equiv; entailer!;
    rewrite (proj1 (proj2 PreH1)); assumption.
Qed.


Lemma proof_of_OSTaskCreate_return_wit_2 : OSTaskCreate_return_wit_2.
Proof.
  left; intros; subst retval.
  sep_apply_l_atomic (task_create_schedule_safe_return environment critical saved_local sg call mask X
    region args task_return lower old_frame upper); entailer!.
Qed.

Lemma proof_of_OSTaskCreate_partial_solve_wit_5_pure : OSTaskCreate_partial_solve_wit_5_pure.
Proof.
  left; intros.
  sep_apply_l_atomic (store_uchar_range (&( "OSIntNesting" )) (task_create_stack_nesting acquired)); Intros.
  assert (Hrange : 0 <= task_create_stack_nesting acquired <= 255)
    by (change (0 <= task_create_stack_nesting acquired <= Byte.max_unsigned); assumption).
  rewrite unsigned_last_nbits_eq in PreH1 by (change (0 <= task_create_stack_nesting acquired < 4294967296); lia).
  entailer!; lia.
Qed.


Lemma proof_of_OSTaskCreate_which_implies_wit_1 : OSTaskCreate_which_implies_wit_1.
Proof.
  left; intros.
  sep_apply_l_atomic (task_create_name_api_pre_open environment critical saved_local sg region args
    task_return lower old_frame upper call mask initial LitMap literals).
  Intros; entailer!; tauto.
Qed.
