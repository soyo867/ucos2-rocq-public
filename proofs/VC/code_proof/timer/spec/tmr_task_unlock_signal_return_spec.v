Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_call_lifetime_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_fields_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_continuation_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_lock_fields_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.sched.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The false scheduling branch opens its actual Restore result once.
    Its recorded Save/checkpoint/Restore source transports the original
    lifetime fact to that same returned descriptor and current state.
    The original local heap and arbitrary continuation X are retained. *)
Lemma tmr_task_unlock_fields_no_schedule_signal_return :
  forall environment critical local sg original mask before acquired X,
  UCOS2_state_inv sg before ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) before ->
  os_sched_unlock_requests acquired = false ->
  os_sched_unlock_continuation_safe environment critical sg original mask before X ->
  os_sched_unlock_fields_restored_post environment critical local sg original mask before acquired |--
  tmr_task_unlock_fields_signal_post environment critical local sg original mask before X.
Proof.
  intros environment critical local sg original mask before acquired X Hvalid_before Hlife Hrequest Hsafe heap
    [restored [unlocked [[[Hprefix [Hnormal [Hsource [Hcontrol [Hrestore_control [Hvalid Hready]]]]]] Hsources] Howned]]].
  pose proof (tmr_task_unlock_fields_prefix_preserves_signal_lifetime environment critical sg original mask
    before acquired restored unlocked Hvalid_before Hlife Hsources) as Hsignal.
  assert (Hhistory : os_sched_unlock_continuation_history environment critical sg original mask before restored unlocked).
  { unfold os_sched_unlock_continuation_history; rewrite (proj1 Hprefix).
    exists acquired, restored, unlocked; split; [exact Hprefix|].
    unfold os_sched_unlock_tail_program; rewrite Hrequest; split; reflexivity. }
  exists restored, unlocked; split.
  - split.
    + split; [|unfold os_sched_unlock_fields_return_sources; rewrite (proj1 Hprefix);
        exists acquired, restored, unlocked; split; [exact Hsources|];
        unfold os_sched_unlock_tail_program; rewrite Hrequest; split; reflexivity].
      unfold os_sched_unlock_continuation_return_facts.
      split; [exact Hhistory|]. split; [exact Hnormal|]. split; [exact Hsource|].
      split; [exact Hcontrol|]. eapply os_sched_unlock_continuation_safeexec_return; eassumption.
    + exact Hsignal.
  - left; exact Howned.
Qed.

(** When the literal OSRunning test is false, the original state and call
    are the actual return. Recombine the original running-field owner and
    frame before packaging that same world, lifetime and continuation X. *)
Lemma tmr_task_unlock_fields_not_running_signal_return :
  forall environment critical local sg original mask before X,
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) before ->
  os_sched_unlock_running before <> 1 ->
  os_sched_unlock_continuation_safe environment critical sg original mask before X ->
  sg.(g_OSRunning) # UChar |-> os_sched_unlock_running before **
    os_sched_fields_observation_frame environment local sg original mask before |--
  tmr_task_unlock_fields_signal_post environment critical local sg original mask before X.
Proof.
  intros environment critical local sg original mask before X Hlife Hnotrunning Hsafe.
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
  lazymatch goal with |- _ |-- ?post =>
    change ((sg.(g_OSRunning) # UChar |-> os_sched_lock_running before **
      os_sched_fields_observation_frame environment local sg original mask before) |-- post)
  end.
  sep_apply_l_atomic (proj2 (os_sched_fields_split_running environment local sg original mask before)).
  unfold tmr_task_unlock_fields_signal_post; Exists original before.
  unfold os_sched_unlock_continuation_return_facts, os_sched_unlock_fields_return_world.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  Left; entailer!.
Qed.
