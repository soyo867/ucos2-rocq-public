Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_signal_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_phase_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_callee_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_lock_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_fields_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_continuation_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Import SchedulerPhaseCandidate SchedulerCalleePhaseComponent PrimitiveComponent FlagPendSchedulerResources.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The original history facts, lifetime and closed owner share one actual
    returned/current/next_local tuple. Forgetting lifetime gives the
    existing C-consumable history post with no resource change. *)
Definition tmr_task_sched_history_signal_post environment critical active sg original mask before : Assertion :=
  EX returned current next_local,
    coq_prop ((os_sched_task_call_history environment critical sg original mask before returned current /\
      task_tcb_init_stack_same_call returned original /\
      (kernel_call_task_source original before -> kernel_call_task_source returned current) /\
      os_sched_task_current_ready returned current /\
      kernel_call_normal_return original before returned current /\ kernel_call_control_rely sg before current) /\
      tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current) &&
    (kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_fields_inv
      next_local sg (task_stack_call_active_key returned) returned mask current ** active returned current).

Lemma tmr_task_sched_history_signal_post_implies_ordinary :
  forall environment critical active sg original mask before,
  tmr_task_sched_history_signal_post environment critical active sg original mask before |--
  os_sched_task_history_return_post environment critical active sg original mask before.
Proof.
  intros environment critical active sg original mask before heap
    [returned [current [next_local [[Hfacts Hlife] Howned]]]].
  exists returned, current, next_local; exact (conj Hfacts Howned).
Qed.

(** All three original observation packets are retained. The Restore
    packet is indexed by the SAME returned/current as Hrestore. Lifetime,
    the history's Save/Restore edges, and the final heap owner are derived
    from the actual executions, never selected from an ordinary post. *)
Lemma tmr_task_scoped_restore_history_signal_post :
  forall environment critical sg original scheduled resumed returned mask saved before entry released current
    save_local saved_local active first_heap save_stop acquired_heap
    restore_local next_local released_heap restore_stop final_heap,
  SelectedEnvironmentPhaseEffects.os_sched_continuation_c_save_execution environment critical
    save_local saved_local active sg original mask before first_heap saved save_stop scheduled entry acquired_heap ->
  os_sched_task_save_observation environment critical sg original mask saved before scheduled entry ->
  os_sched_task_body_observation environment critical sg scheduled entry resumed released ->
  tmr_task_signal_lifetime critical sg resumed.(os_sched_call_invocation) released ->
  SelectedEnvironmentPhaseEffects.os_sched_continuation_c_restore_execution environment critical
    restore_local next_local active sg resumed saved entry released released_heap restore_stop returned current final_heap ->
  os_sched_task_restore_observation environment critical sg resumed released returned current ->
  tmr_task_sched_history_signal_post environment critical active sg original mask before final_heap.
Proof.
  intros until final_heap; intros Hsave Hsave_observation Hbody Hlife Hrestore Hrestore_observation.
  destruct (SelectedEnvironmentPhaseProperties.os_sched_continuation_c_restore_execution_resources
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrestore) as [Hinput [Hendpoints Houtput]].
  pose proof (proj1 (flag_pend_caller_restore_input_state_inv environment critical restore_local active sg
    (FlagPendTaskCaller resumed) resumed saved entry released released_heap Hinput)) as Hvalid.
  pose proof (os_sched_task_observations_compose environment critical sg original scheduled resumed returned
    mask saved before entry released current Hsave_observation Hbody Hrestore_observation Hvalid)
    as [_ Hfacts].
  destruct (tmr_task_sched_scoped_return_signal environment critical sg original scheduled resumed returned
    mask saved before entry released current save_local saved_local active first_heap save_stop acquired_heap
    restore_local next_local released_heap restore_stop final_heap Hsave Hbody Hlife Hrestore)
    as [Hhistory [Hsignal Hcontinue]].
  assert (Hmask : armv7a_irq_fiq_mask saved = mask).
  { destruct Hsave_observation as [_ [_ [Hsaved _]]]; exact (proj2 Hsaved). }
  pose proof (proj1 (flag_pend_task_save_input_closed_equiv environment critical next_local active sg
    returned (armv7a_irq_fiq_mask saved) current) final_heap Houtput) as Hclosed.
  rewrite Hmask in Hclosed.
  exists returned, current, next_local; split; [|exact Hclosed].
  exact (conj (conj Hhistory Hfacts) Hsignal).
Qed.

(** Eliminate the body post only once. Its actual local, descriptor,
    released state and heap are the input indices of the actual Restore.
    No arbitrary old history-post unpack is rebound to these witnesses. *)
Lemma tmr_task_sched_body_signal_post_history_return :
  forall environment critical sg original scheduled mask saved before entry
    save_local saved_local active first_heap save_stop acquired_heap body_heap,
  SelectedEnvironmentPhaseEffects.os_sched_continuation_c_save_execution environment critical
    save_local saved_local active sg original mask before first_heap saved save_stop scheduled entry acquired_heap ->
  os_sched_task_save_observation environment critical sg original mask saved before scheduled entry ->
  tmr_task_sched_body_signal_post environment critical active sg scheduled saved entry entry body_heap ->
  exists resumed released next_local,
    os_sched_task_body_observation environment critical sg scheduled entry resumed released /\
    tmr_task_signal_lifetime critical sg resumed.(os_sched_call_invocation) released /\
    (kernel_continuation_call_masked environment.(task_stack_call_continuations) kernel_program_fields_inv
      next_local critical sg (task_stack_call_active_key resumed) resumed saved entry released **
      active resumed released) body_heap /\
    (forall restored_local restore_stop returned current final_heap,
      SelectedEnvironmentPhaseEffects.os_sched_continuation_c_restore_execution environment critical
        next_local restored_local active sg resumed saved entry released body_heap restore_stop returned current final_heap ->
      os_sched_task_restore_observation environment critical sg resumed released returned current ->
      tmr_task_sched_history_signal_post environment critical active sg original mask before final_heap).
Proof.
  intros until body_heap; intros Hsave Hsave_observation
    [resumed [released [next_local [[Hbody Hlife] Howned]]]].
  exists resumed, released, next_local; split; [exact Hbody|].
  split; [exact Hlife|]. split; [exact Howned|].
  intros restored_local restore_stop returned current final_heap Hrestore Hrestore_observation.
  eapply tmr_task_scoped_restore_history_signal_post; eassumption.
Qed.

Lemma tmr_task_sched_history_signal_post_safeexec :
  forall environment critical active sg original mask before
    (X : OsSchedCallContext -> UCOS2_Verify_State -> Prop),
  safeExec (fun state => state = before) (os_sched_task_program environment critical sg original mask) X ->
  tmr_task_sched_history_signal_post environment critical active sg original mask before |--
  EX returned current next_local,
    coq_prop (tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current /\
      safeExec (fun state => state = current) (StateRelMonad.ret returned) X) &&
    (kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_fields_inv
      next_local sg (task_stack_call_active_key returned) returned mask current ** active returned current).
Proof.
  intros environment critical active sg original mask before X Hsafe heap
    [returned [current [next_local [[Hfacts Hlife] Howned]]]].
  exists returned, current, next_local; split; [|exact Howned].
  split; [exact Hlife|]. eapply os_sched_task_history_return_safeexec; [exact (proj1 Hfacts)|exact Hsafe].
Qed.

Definition tmr_task_unlock_fields_signal_post environment critical local sg original mask before X : Assertion :=
  EX returned current,
    coq_prop ((os_sched_unlock_continuation_return_facts environment critical sg original mask before X returned current /\
      os_sched_unlock_fields_return_sources environment critical sg original mask before returned current) /\
      tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current) &&
    os_sched_unlock_fields_return_world environment local sg returned mask current.

Lemma tmr_task_unlock_fields_signal_post_implies_ordinary :
  forall environment critical local sg original mask before X,
  tmr_task_unlock_fields_signal_post environment critical local sg original mask before X |--
  os_sched_unlock_fields_post environment critical local sg original mask before X.
Proof.
  intros environment critical local sg original mask before X heap
    [returned [current [[Hfacts Hlife] Howned]]].
  exists returned, current; exact (conj Hfacts Howned).
Qed.

(** The scheduled branch retains lifetime at the same EX construction as
    the existing fields return. The original fresh-registration active
    owner, actual next_local, source packet and arbitrary X are unchanged. *)
Lemma tmr_task_unlock_fields_scheduled_signal_return : forall environment critical local sg original mask
  before acquired restored unlocked X,
  os_sched_unlock_requests acquired = true ->
  os_sched_unlock_fields_restored_facts environment critical sg original mask before acquired restored unlocked ->
  os_sched_unlock_continuation_safe environment critical sg original mask before X ->
  tmr_task_sched_history_signal_post (task_sw_hook_call_environment environment) critical
    (PendPhaseCandidate.flag_pend_fresh_observation restored) sg restored mask unlocked |--
  tmr_task_unlock_fields_signal_post environment critical local sg original mask before X.
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
  unfold tmr_task_unlock_fields_signal_post; Exists returned current.
  unfold os_sched_unlock_continuation_return_facts, os_sched_unlock_fields_return_world.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  Right; Exists restored next_local.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  unfold os_sched_fields_closed; entailer!.
Qed.
