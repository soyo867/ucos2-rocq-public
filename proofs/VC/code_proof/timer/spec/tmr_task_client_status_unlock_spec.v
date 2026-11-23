Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_call_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_callback_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_unlock_fields_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_unlock_signal_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_call_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_fields_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_task_scheduler_adapter_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.sched.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Import SchedulerPhaseCandidate.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual Save/checkpoint/Restore prefix preserves the original six
    caller observations, including Idle and the caller's non-Idle priority.
    This statement permits a suspended caller throughout the prefix. *)
Lemma tmr_task_unlock_prefix_preserves_entry : forall external environment critical sg original mask
  before acquired restored unlocked,
  tmr_task_registered_source_coverage external critical -> UCOS2_state_inv sg before ->
  tmr_task_unlock_entry sg original before ->
  os_sched_unlock_fields_restored_facts environment critical sg original mask before acquired restored unlocked ->
  tmr_task_unlock_entry sg restored unlocked.
Proof.
  intros external environment critical sg original mask before acquired restored unlocked
    Hcoverage Hvalid Hentry Hfacts.
  destruct (tmr_task_unlock_entry_invariants sg original before Hvalid Hentry)
    as [Hcurrent_inv [Hidle_inv [Hclear_inv Hready]]].
  destruct (tmr_task_registered_source_unlock_clients external critical original Hcoverage)
    as [Hcurrent_clients [Hidle_clients Hclear_clients]].
  pose proof (os_sched_unlock_fields_prefix_registered_current environment critical sg original mask
    before acquired restored unlocked Hcurrent_clients Hfacts Hvalid (proj2 Hcurrent_inv)) as Hcurrent.
  destruct (os_sched_unlock_fields_prefix_idle_non_idle environment critical sg original mask
    before acquired restored unlocked Hidle_clients Hfacts Hvalid
    (proj1 (proj2 (proj2 Hidle_inv))) (proj2 (proj2 (proj2 Hidle_inv)))) as [Hidle Hnonidle].
  pose proof (os_sched_unlock_fields_prefix_registered_clear environment critical sg original mask
    before acquired restored unlocked Hclear_clients Hfacts Hclear_inv) as Hclear.
  destruct Hentry as [Hsource [Havailable [Hrunning Hrest]]].
  destruct Hfacts as [[Hprefix [Hnormal [Hsource_return [Hcontrol Hrestored]]]] Hsources].
  split; [apply Hsource_return; exact Hsource|].
  split; [exact (proj2 Hnormal Havailable)|].
  split; [rewrite (proj1 Hcontrol); exact Hrunning|].
  split; [exact Hcurrent|]. split; [exact Hidle|].
  destruct Hnonidle as [node [Hnode [Hgeneration Hpriority]]].
  intros actual Hactual; assert (actual = node) by congruence; subst actual.
  split; [exact Hpriority|apply Hclear; exact Hnode].
Qed.

(** After a native return, use its recorded checkpoint and the same
    actual normal/source/control facts. No discarded Restore packet is
    reconstructed from the spatial owner's shape. *)
Lemma tmr_task_unlock_checkpoint_preserves_entry : forall external environment critical sg original mask
  before acquired returned current,
  tmr_task_registered_source_coverage external critical -> UCOS2_state_inv sg before ->
  tmr_task_unlock_entry sg original before ->
  os_sched_fields_checkpoint_sources (os_sched_unlock_checkpoint true)
    environment critical sg original mask before acquired returned current ->
  kernel_call_normal_return original before returned current ->
  (kernel_call_task_source original before -> kernel_call_task_source returned current) ->
  os_sched_unlock_continuation_control before current ->
  tmr_task_unlock_entry sg returned current.
Proof.
  intros external environment critical sg original mask before acquired returned current
    Hcoverage Hvalid Hentry Hsources Hnormal Hsource_return Hcontrol.
  destruct (tmr_task_unlock_entry_invariants sg original before Hvalid Hentry)
    as [Hcurrent_inv [Hidle_inv [Hclear_inv Hready]]].
  destruct (tmr_task_registered_source_unlock_clients external critical original Hcoverage)
    as [Hcurrent_clients [Hidle_clients Hclear_clients]].
  pose proof (os_sched_fields_checkpoint_current_consistency (os_sched_unlock_checkpoint true)
    environment critical sg original mask before acquired returned current Hcurrent_clients Hsources
    (os_sched_unlock_checkpoint_preserves_validity sg true acquired) eq_refl eq_refl
    Hvalid (proj2 Hcurrent_inv)) as Hcurrent.
  destruct (os_sched_fields_checkpoint_idle_non_idle (os_sched_unlock_checkpoint true)
    environment critical sg original mask before acquired returned current Hidle_clients Hsources
    (os_sched_unlock_checkpoint_preserves_validity sg true acquired) eq_refl eq_refl Hidle_inv)
    as [Hidle Hnonidle].
  destruct (os_sched_fields_checkpoint_registered_clear (os_sched_unlock_checkpoint true)
    environment critical sg original mask before acquired returned current Hclear_clients Hsources
    (os_sched_unlock_checkpoint_preserves_validity sg true acquired) eq_refl Hclear_inv)
    as [node [Hnode [Hclear Hflag]]].
  destruct Hnonidle as [actual [Hactual [Hgeneration Hpriority]]].
  assert (actual = node) by congruence; subst actual.
  destruct Hentry as [Hsource [Havailable [Hrunning Hrest]]].
  split; [apply Hsource_return; exact Hsource|].
  split; [exact (proj2 Hnormal Havailable)|].
  split; [rewrite (proj1 Hcontrol); exact Hrunning|].
  split; [exact Hcurrent|]. split; [exact Hidle|].
  intros observed Hobserved; assert (observed = node) by congruence; subst observed.
  exact (conj Hpriority (conj Hclear Hflag)).
Qed.

(** Retain which real return path produced the state. In particular the
    native spatial owner alone does not imply that scheduling was skipped. *)
Definition tmr_task_unlock_return_branch environment critical sg original mask before returned current : Prop :=
  (before.(SchedState).(isRunning) = false /\ returned = original /\ current = before) \/
  (exists acquired,
    os_sched_fields_checkpoint_sources (os_sched_unlock_checkpoint true)
      environment critical sg original mask before acquired returned current /\
    os_sched_unlock_requests acquired = false) \/
  (exists acquired restored unlocked,
    os_sched_fields_checkpoint_sources (os_sched_unlock_checkpoint true)
      environment critical sg original mask before acquired restored unlocked /\
    os_sched_unlock_requests acquired = true /\
    os_sched_task_call_history (task_sw_hook_call_environment environment) critical
      sg restored mask unlocked returned current /\
    os_sched_task_current_ready returned current /\
    flag_active_fresh_registration restored returned current).

Definition tmr_task_unlock_fields_status_post environment critical local sg original mask before X : Assertion :=
  EX returned current,
    coq_prop (((os_sched_unlock_continuation_return_facts environment critical sg original mask before X returned current /\
      os_sched_unlock_fields_return_sources environment critical sg original mask before returned current) /\
      tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current) /\
      tmr_task_caller_wait_status_clear returned current /\
      tmr_task_unlock_return_branch environment critical sg original mask before returned current) &&
    os_sched_unlock_fields_return_world environment local sg returned mask current.

Lemma tmr_task_unlock_fields_status_post_implies_signal : forall environment critical local sg original mask before X,
  tmr_task_unlock_fields_status_post environment critical local sg original mask before X |--
  tmr_task_unlock_fields_signal_post environment critical local sg original mask before X.
Proof.
  intros environment critical local sg original mask before X heap
    [returned [current [[Hsignal [Hstatus Hbranch]] Howned]]].
  exists returned, current; split; assumption.
Qed.

Lemma tmr_task_unlock_fields_no_schedule_status_return :
  forall external environment critical local sg original mask before acquired X,
  tmr_task_registered_source_coverage external critical -> UCOS2_state_inv sg before ->
  kernel_call_task_source original before -> tmr_task_caller_wait_status_clear original before ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) before ->
  os_sched_unlock_requests acquired = false ->
  os_sched_unlock_continuation_safe environment critical sg original mask before X ->
  os_sched_unlock_fields_restored_post environment critical local sg original mask before acquired |--
  tmr_task_unlock_fields_status_post environment critical local sg original mask before X.
Proof.
  intros external environment critical local sg original mask before acquired X
    Hcoverage Hvalid_before Hsource_before Hclear Hlife Hrequest Hsafe heap
    [restored [unlocked [[[Hprefix [Hnormal [Hsource [Hcontrol [Hrestore_control [Hvalid Hready]]]]]] Hsources] Howned]]].
  pose proof (tmr_task_unlock_fields_prefix_preserves_signal_lifetime environment critical sg original mask
    before acquired restored unlocked Hvalid_before Hlife Hsources) as Hsignal.
  pose proof (tmr_task_unlock_prefix_wait_status external environment critical sg original mask
    before acquired restored unlocked Hcoverage Hvalid_before Hsource_before Hclear Hsources) as Hstatus.
  assert (Hhistory : os_sched_unlock_continuation_history environment critical sg original mask before restored unlocked).
  { unfold os_sched_unlock_continuation_history; rewrite (proj1 Hprefix).
    exists acquired, restored, unlocked; split; [exact Hprefix|].
    unfold os_sched_unlock_tail_program; rewrite Hrequest; split; reflexivity. }
  exists restored, unlocked; split; [|left; exact Howned].
  split.
  - split.
    + split; [|unfold os_sched_unlock_fields_return_sources; rewrite (proj1 Hprefix);
        exists acquired, restored, unlocked; split; [exact Hsources|];
        unfold os_sched_unlock_tail_program; rewrite Hrequest; split; reflexivity].
      unfold os_sched_unlock_continuation_return_facts.
      split; [exact Hhistory|]. split; [exact Hnormal|]. split; [exact Hsource|].
      split; [exact Hcontrol|]. eapply os_sched_unlock_continuation_safeexec_return; eassumption.
    + exact Hsignal.
  - split; [exact Hstatus|]. right; left; exists acquired; split; assumption.
Qed.

Lemma tmr_task_unlock_fields_not_running_status_return :
  forall environment critical local sg original mask before X,
  tmr_task_caller_wait_status_clear original before ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) before ->
  os_sched_unlock_running before <> 1 ->
  os_sched_unlock_continuation_safe environment critical sg original mask before X ->
  sg.(g_OSRunning) # UChar |-> os_sched_unlock_running before **
    os_sched_fields_observation_frame environment local sg original mask before |--
  tmr_task_unlock_fields_status_post environment critical local sg original mask before X.
Proof.
  intros environment critical local sg original mask before X Hclear Hlife Hnotrunning Hsafe.
  assert (Hrun : before.(SchedState).(isRunning) = false).
  { unfold os_sched_unlock_running in Hnotrunning; destruct before.(SchedState).(isRunning);
      [contradiction|reflexivity]. }
  assert (Hhistory : os_sched_unlock_continuation_history environment critical sg original mask before original before).
  { unfold os_sched_unlock_continuation_history; rewrite Hrun; split; reflexivity. }
  pose proof (os_sched_unlock_continuation_safeexec_return environment critical sg original mask
    before original before X Hhistory Hsafe) as Hcontinue.
  pose proof (kernel_call_normal_return_refl original before) as Hnormal.
  pose proof (os_sched_unlock_continuation_control_not_running before Hrun) as Hcontrol.
  assert (Hsources : os_sched_unlock_fields_return_sources environment critical sg original mask before original before).
  { unfold os_sched_unlock_fields_return_sources; rewrite Hrun; split; reflexivity. }
  assert (Hbranch : tmr_task_unlock_return_branch environment critical sg original mask before original before).
  { left; split; [exact Hrun|split; reflexivity]. }
  lazymatch goal with |- _ |-- ?post =>
    change ((sg.(g_OSRunning) # UChar |-> os_sched_lock_running before **
      os_sched_fields_observation_frame environment local sg original mask before) |-- post)
  end.
  sep_apply_l_atomic (proj2 (os_sched_fields_split_running environment local sg original mask before)).
  unfold tmr_task_unlock_fields_status_post; Exists original before.
  unfold os_sched_unlock_continuation_return_facts, os_sched_unlock_fields_return_world.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  Left; entailer!.
Qed.

(** Readiness comes from this actual C Scheduler return, while arbitrary
    callbacks remain free to suspend the caller. The fresh observation,
    same returned/current pair, actual next_local and continuation survive. *)
Lemma tmr_task_unlock_fields_scheduled_status_return : forall environment critical local sg original mask
  before acquired restored unlocked X,
  os_sched_unlock_requests acquired = true ->
  os_sched_unlock_fields_restored_facts environment critical sg original mask before acquired restored unlocked ->
  os_sched_unlock_continuation_safe environment critical sg original mask before X ->
  tmr_task_sched_history_signal_post (task_sw_hook_call_environment environment) critical
    (PendPhaseCandidate.flag_pend_fresh_observation restored) sg restored mask unlocked |--
  tmr_task_unlock_fields_status_post environment critical local sg original mask before X.
Proof.
  intros environment critical local sg original mask before acquired restored unlocked X Hrequest
    [[Hprefix [Hnormal_prefix [Hsource_prefix [Hcontrol_prefix [Hrestore_control [Hvalid Hready_prefix]]]]]] Hsources] Hsafe.
  unfold tmr_task_sched_history_signal_post,
    PendPhaseCandidate.flag_pend_fresh_observation; Intros returned current next_local.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  assert (Hsched : os_sched_task_call_history (task_sw_hook_call_environment environment)
    critical sg restored mask unlocked returned current) by tauto.
  assert (Hnormal_sched : kernel_call_normal_return restored unlocked returned current) by tauto.
  assert (Hsource_sched : kernel_call_task_source restored unlocked -> kernel_call_task_source returned current) by tauto.
  assert (Hcontrol_sched : kernel_call_control_rely sg unlocked current) by tauto.
  assert (Hsignal : tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current) by tauto.
  assert (Hstatus : tmr_task_caller_wait_status_clear returned current).
  { apply tmr_task_caller_wait_status_clear_from_ready; tauto. }
  assert (Hbranch : tmr_task_unlock_return_branch environment critical sg original mask before returned current).
  { right; right; exists acquired, restored, unlocked; tauto. }
  assert (Hhistory : os_sched_unlock_continuation_history environment critical sg original mask before returned current).
  { unfold os_sched_unlock_continuation_history; rewrite (proj1 Hprefix).
    exists acquired, restored, unlocked; split; [exact Hprefix|].
    unfold os_sched_unlock_tail_program; rewrite Hrequest.
    apply os_sched_task_program_iff; exact Hsched. }
  assert (Hnormal : kernel_call_normal_return original before returned current)
    by (eapply kernel_call_normal_return_trans; eassumption).
  assert (Hsource : kernel_call_task_source original before -> kernel_call_task_source returned current) by auto.
  assert (Hcontrol : os_sched_unlock_continuation_control before current)
    by (eapply os_sched_unlock_continuation_control_sched; eassumption).
  pose proof (os_sched_unlock_continuation_safeexec_return environment critical sg original mask
    before returned current X Hhistory Hsafe) as Hcontinue.
  assert (Hreturn_sources : os_sched_unlock_fields_return_sources environment critical sg original mask before returned current).
  { unfold os_sched_unlock_fields_return_sources; rewrite (proj1 Hprefix).
    exists acquired, restored, unlocked; split; [exact Hsources|].
    unfold os_sched_unlock_tail_program; rewrite Hrequest.
    apply os_sched_task_program_iff; exact Hsched. }
  rewrite (os_sched_unlock_configured_closed_world_eq environment kernel_program_fields_inv
    next_local sg (task_stack_call_active_key returned) returned mask current).
  unfold tmr_task_unlock_fields_status_post; Exists returned current.
  unfold os_sched_unlock_continuation_return_facts, os_sched_unlock_fields_return_world.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  Right; Exists restored next_local.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  unfold os_sched_fields_closed; entailer!.
Qed.
