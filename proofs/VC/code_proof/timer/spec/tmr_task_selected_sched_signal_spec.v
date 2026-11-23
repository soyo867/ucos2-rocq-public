Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_protocol_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_call_lifetime_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_phase_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_phase_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_callee_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_return_facts_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_call_value_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_endpoint_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_wake_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_fields_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_lock_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_wrapper_completion_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_returned_c_segment_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_completion_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selected_completion_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_fields_prefix_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_acquired_return_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_next_completion_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.
Import UCOS2_C_Rules TaskStateDef SchedStateDef EventStateDef ListNotations.
Import SelectedCProgram SelectedCSource SelectedIRQWrapperSegment SelectedIRQWrapperSource.
Import SelectedReturnedCProgram SelectedReturnedCSource OSIntExitReturnedC SelectedIRQWrapperCompletion.
Import OSIntExitCCallCompletion ReturnedIRQCallSource SelectedEnvironmentCProgram SelectedEnvironmentCSource SelectedEnvironmentScopedSource.
Import SchedulerCalleePhaseComponent SchedulerPhaseCandidate FlagPendSchedulerResources.
Import PrimitiveComponent TerminalCallValue.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The wrapper, returned and complete-IRQ unions are the actual source
    languages used by scoped Save/Restore. Each result follows the same
    proof-indexed execution; none reselects a trace from its endpoints. *)
Lemma tmr_task_wrapper_c_step_source_preserves_live_sem :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (step : kernel_program_wrapper_c_step environment critical sg observer origin
      state before input stopped current after output),
  kernel_program_wrapper_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output step -> tmr_task_live_sem_identity state current.
Proof.
  intros until step; intro Hsource; destruct Hsource.
  - eapply tmr_task_selected_c_step_source_preserves_live_sem; exact H.
  - destruct step; apply tmr_task_event_state_eq_preserves_live_sem; reflexivity.
Qed.

Lemma tmr_task_returned_c_step_source_preserves_live_sem :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (step : kernel_program_returned_c_step environment critical sg observer origin
      state before input stopped current after output),
  kernel_program_returned_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output step -> tmr_task_live_sem_identity state current.
Proof.
  intros until step; intro Hsource; destruct Hsource.
  - eapply tmr_task_wrapper_c_step_source_preserves_live_sem; exact H.
  - destruct step; destruct observed.(SchedState).(isRunning);
      apply tmr_task_event_state_eq_preserves_live_sem; reflexivity.
Qed.

Lemma tmr_task_returned_c_sequence_source_preserves_live_sem :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
      state before input stopped current after output),
  kernel_program_returned_c_sequence_source environment critical sg observer origin event_observer
    state before input stopped current after output run -> tmr_task_live_sem_identity state current.
Proof.
  intros until run; intro Hsource.
  eapply (kernel_c_sequence_source_relation
    (kernel_program_returned_c_step environment critical sg observer origin)
    (kernel_program_returned_c_step_source environment critical sg observer origin event_observer)
    tmr_task_live_sem_identity).
  - apply tmr_task_live_sem_identity_refl.
  - apply tmr_task_live_sem_identity_trans.
  - intros; eapply tmr_task_returned_c_step_source_preserves_live_sem; eassumption.
  - exact Hsource.
Qed.

Lemma tmr_task_irq_c_call_source_preserves_live_sem :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (step : os_int_exit_first_level_c_step environment critical sg observer origin
      state before input stopped current after output),
  os_int_exit_first_level_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output step -> tmr_task_live_sem_identity state current.
Proof.
  intros until step; intro Hsource; destruct Hsource.
  eapply tmr_task_live_sem_identity_trans.
  - apply tmr_task_event_state_eq_preserves_live_sem.
    exact (proj1 (proj2 (OSIntExitCCallCompletion.os_int_exit_first_level_entry_source_frames
      _ _ _ _ _ _ _ _ _ _ _ _ Hentry))).
  - eapply tmr_task_live_sem_identity_trans.
    + eapply tmr_task_returned_c_sequence_source_preserves_live_sem; exact H.
    + eapply tmr_task_live_sem_identity_trans.
      * eapply tmr_task_returned_c_sequence_source_preserves_live_sem; exact H0.
      * destruct observed.(SchedState).(isRunning);
          apply tmr_task_event_state_eq_preserves_live_sem; reflexivity.
Qed.

Lemma tmr_task_environment_c_step_source_preserves_live_sem :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (step : kernel_program_environment_c_step environment critical sg observer origin
      state before input stopped current after output),
  kernel_program_environment_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output step -> tmr_task_live_sem_identity state current.
Proof.
  intros until step; intro Hsource; destruct Hsource.
  - eapply tmr_task_returned_c_step_source_preserves_live_sem; exact H.
  - eapply tmr_task_irq_c_call_source_preserves_live_sem; exact H.
  - eapply tmr_task_wake_source_preserves_live_sem.
    exact (proj2 (FlagTaskRdyNextCompletion.flag_task_rdy_next_c_segment_source
      _ _ _ _ _ _ _ _ _ step)).
Qed.

Lemma tmr_task_environment_c_sequence_source_preserves_live_sem :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer origin)
      state before input stopped current after output),
  kernel_program_environment_c_sequence_source environment critical sg observer origin event_observer
    state before input stopped current after output run -> tmr_task_live_sem_identity state current.
Proof.
  intros until run; intro Hsource.
  eapply (kernel_c_sequence_source_relation
    (kernel_program_environment_c_step environment critical sg observer origin)
    (kernel_program_environment_c_step_source environment critical sg observer origin event_observer)
    tmr_task_live_sem_identity).
  - apply tmr_task_live_sem_identity_refl.
  - apply tmr_task_live_sem_identity_trans.
  - intros; eapply tmr_task_environment_c_step_source_preserves_live_sem; eassumption.
  - exact Hsource.
Qed.

Lemma tmr_task_scoped_c_source_preserves_live_sem :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (actual : kernel_call_scoped_c_execution environment critical sg observer origin
      state before input stopped current after output),
  kernel_call_scoped_c_execution_source environment critical sg observer origin event_observer
    state before input stopped current after output actual -> tmr_task_live_sem_identity state current.
Proof.
  intros until actual; intro Hsource; destruct Hsource.
  eapply tmr_task_environment_c_sequence_source_preserves_live_sem; exact H.
Qed.

Lemma tmr_task_scoped_c_source_preserves_signal_lifetime :
  forall environment critical sg observer origin event_observer invocation state before input stopped current after output
    (actual : kernel_call_scoped_c_execution environment critical sg observer origin
      state before input stopped current after output),
  kernel_call_scoped_c_execution_source environment critical sg observer origin event_observer
    state before input stopped current after output actual ->
  tmr_task_signal_lifetime critical sg invocation state ->
  tmr_task_signal_lifetime critical sg invocation current.
Proof.
  intros until actual; intros Hsource Hlife.
  eapply tmr_task_live_sem_identity_preserves_lifetime; [exact Hlife| |].
  - eapply tmr_task_signal_public_trace_value.
    exact (proj2 (proj2 (proj2 (kernel_call_scoped_c_execution_source_frames
      _ _ _ _ _ _ _ _ _ _ _ _ _ actual Hsource)))).
  - eapply tmr_task_scoped_c_source_preserves_live_sem; exact Hsource.
Qed.

(** The real scoped execution already owns its endpoint observation and
    same-call fact. The local ABI suffix does not alter the C state. *)
Lemma tmr_task_scoped_save_preserves_signal_lifetime :
  forall environment critical local next_local active sg original mask before first_heap
    saved stopped returned current last_heap,
  SelectedEnvironmentPhaseEffects.os_sched_continuation_c_save_execution environment critical
    local next_local active sg original mask before first_heap saved stopped returned current last_heap ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) before ->
  tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current.
Proof.
  intros until last_heap; intros Hactual Hlife.
  destruct (SelectedEnvironmentPhaseEffects.os_sched_continuation_c_save_execution_sequence_source
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual) as [Hsaved [actual Hsource]].
  pose proof (SelectedEnvironmentPhaseEffects.os_sched_continuation_c_save_execution_endpoints
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual) as [_ [_ [_ [Hnormal Hcontrol]]]].
  eapply tmr_task_signal_lifetime_same_call; [exact (proj1 Hnormal)|].
  eapply tmr_task_scoped_c_source_preserves_signal_lifetime; eassumption.
Qed.

Lemma tmr_task_scoped_restore_preserves_signal_lifetime :
  forall environment critical local next_local active sg original saved acquired before first_heap
    stopped returned current last_heap,
  SelectedEnvironmentPhaseEffects.os_sched_continuation_c_restore_execution environment critical
    local next_local active sg original saved acquired before first_heap stopped returned current last_heap ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) before ->
  tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current.
Proof.
  intros until last_heap; intros Hactual Hlife.
  destruct (SelectedEnvironmentPhaseEffects.os_sched_continuation_c_restore_execution_sequence_source
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual) as [actual Hsource].
  pose proof (SelectedEnvironmentPhaseEffects.os_sched_continuation_c_restore_execution_endpoints
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual) as [_ [_ [_ [Hnormal Hcontrol]]]].
  eapply tmr_task_signal_lifetime_same_call; [exact (proj1 Hnormal)|].
  eapply tmr_task_scoped_c_source_preserves_signal_lifetime; eassumption.
Qed.

Lemma tmr_task_selected_c_sequence_preserves_signal_lifetime :
  forall environment critical sg observer origin event_observer invocation state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      state before input stopped current after output),
  kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    state before input stopped current after output run ->
  tmr_task_signal_lifetime critical sg invocation state ->
  tmr_task_signal_lifetime critical sg invocation current.
Proof.
  intros until run; intros Hsource Hlife.
  eapply tmr_task_live_sem_identity_preserves_lifetime; [exact Hlife| |].
  - eapply tmr_task_signal_public_trace_value.
    exact (proj2 (proj2 (proj2 (kernel_program_selected_c_sequence_source_frames
      _ _ _ _ _ _ _ _ _ _ _ _ _ run Hsource)))).
  - eapply tmr_task_selected_c_sequence_source_preserves_live_sem; exact Hsource.
Qed.

Lemma tmr_task_hook_switch_preserves_signal_lifetime :
  forall environment critical sg invocation entry original installed,
  os_sched_switch_source (task_sw_hook_call_environment environment).(task_stack_call_external)
    sg entry original installed ->
  tmr_task_signal_lifetime critical sg invocation entry ->
  tmr_task_signal_lifetime critical sg invocation installed.
Proof.
  intros environment critical sg invocation entry original installed Hswitch Hlife.
  destruct Hswitch as [Hrequest [sp [saved [hooked [incoming [resumed
    [Hsave [Hhook [Hdestination Hinstalled]]]]]]]]].
  change (hooked = os_sched_save_current_sp (os_sched_prefix_state entry)
    original.(os_sched_call_stack).(stackLeaseSlot) sp) in Hhook.
  rewrite Hinstalled, Hhook.
  eapply tmr_task_live_sem_identity_preserves_lifetime; [exact Hlife|reflexivity|].
  apply tmr_task_event_state_eq_preserves_live_sem; reflexivity.
Qed.

(** The lifetime fact belongs to the actual returned descriptor and state
    chosen at the producer's EX construction. It is carried with the
    original body observation and its exact masked resource owner. *)
Definition tmr_task_sched_body_signal_post environment critical active sg original saved acquired entry : Assertion :=
  EX returned current next_local,
    coq_prop (os_sched_task_body_observation environment critical sg original entry returned current /\
      tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current) &&
    (kernel_continuation_call_masked environment.(task_stack_call_continuations) kernel_program_fields_inv
      next_local critical sg (task_stack_call_active_key returned) returned saved acquired current **
      active returned current).

Definition tmr_task_sched_switch_signal_output environment critical local active sg original saved acquired entry
  before_heap : Assertion :=
  fun after_heap =>
    os_sched_task_switch_pre environment critical local active sg original saved acquired entry before_heap /\
    tmr_task_sched_body_signal_post environment critical active sg original saved acquired entry after_heap.

Lemma tmr_task_sched_body_signal_post_ordinary : forall environment critical active sg original saved acquired entry,
  tmr_task_sched_body_signal_post environment critical active sg original saved acquired entry |--
  os_sched_task_body_post environment critical active sg original saved acquired entry.
Proof.
  intros environment critical active sg original saved acquired entry heap
    [returned [current [local [[Hbody Hlife] Howned]]]].
  exists returned, current, local; exact (conj Hbody Howned).
Qed.

Lemma tmr_task_sched_switch_signal_output_ordinary :
  forall environment critical local active sg original saved acquired entry first_heap,
  tmr_task_sched_switch_signal_output environment critical local active sg original saved acquired entry first_heap |--
  os_sched_task_switch_output environment critical local active sg original saved acquired entry first_heap.
Proof.
  intros environment critical local active sg original saved acquired entry first_heap last_heap [Hpre Hpost].
  split; [exact Hpre|].
  exact (tmr_task_sched_body_signal_post_ordinary environment critical active sg original saved acquired entry last_heap Hpost).
Qed.
Lemma tmr_task_selected_c_prefix_signal_output :
  forall environment critical
    (task_abi : Armv7aTaskContextABI (task_sw_hook_call_environment environment).(task_stack_call_external)
      (task_sw_hook_call_environment environment).(task_stack_call_platform)
      (task_sw_hook_call_environment environment).(task_stack_call_port)
      (task_sw_hook_call_environment environment).(task_stack_call_continuations))
    sg entry first_installed initial_local active initial_heap last_entry context saved_sp outgoing hooked resumed
    original saved acquired receipt other frame first_heap input stopped before_heap output installed sp actual,
  let configured := task_sw_hook_call_environment environment in
  let call := {| InstallComponent.task_install_fields_context := context;
                 InstallComponent.task_install_fields_outgoing := outgoing;
                 InstallComponent.task_install_fields_incoming := original.(os_sched_call_stack);
                 InstallComponent.task_install_fields_resumed := resumed;
                 InstallComponent.task_install_fields_entry := hooked |} in
  let local := kernel_sched_saved_local_resource_at configured.(task_stack_call_platform) critical sg
    hooked.(TskState) original saved acquired receipt other in
  let rest := armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame in
  forall (prefix : kernel_c_sequence (kernel_program_selected_c_step configured critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      first_installed first_heap input stopped hooked before_heap output)
    (complete : InstallComponent.task_install_c_segment configured local sg rest call before_heap installed sp actual),
  os_sched_task_switch_pre configured critical initial_local active sg original saved acquired entry initial_heap ->
  os_sched_switch_source configured.(task_stack_call_external) sg entry original first_installed ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) entry ->
  os_sched_requests_switch last_entry = true ->
  configured.(task_stack_call_external).(os_sched_arch_save_source) context saved_sp outgoing ->
  kernel_client_step configured.(task_stack_call_external).(os_sched_hook_action) sg
    (os_sched_save_current_sp (os_sched_prefix_state last_entry) context.(os_sched_call_stack).(stackLeaseSlot) saved_sp) hooked ->
  os_sched_destination_binding configured.(task_stack_call_external)
    context outgoing hooked original.(os_sched_call_stack) resumed ->
  kernel_program_selected_c_sequence_source configured critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix ->
  output |-- InstallComponent.task_install_fields_entry_owner configured local sg call ** rest ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (forall returned, task_tcb_init_stack_same_call returned original ->
    kernel_call_task_source returned (InstallComponent.task_install_fields_current call) ->
    os_sched_task_current_ready returned (InstallComponent.task_install_fields_current call) ->
    receipt ** frame |-- active returned (InstallComponent.task_install_fields_current call)) ->
  exists selected, forall restored,
  armv7a_task_restore_transition task_abi context selected installed restored ->
  let current := InstallComponent.task_install_fields_current call in
  let returned := kernel_selected_call selected current in
  exists (run : kernel_c_sequence (kernel_program_selected_c_step configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)) first_installed first_heap input
    (orb stopped false) current restored (tmr_task_sched_body_signal_post configured critical active sg original saved acquired entry)),
  kernel_program_selected_c_sequence_source configured critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ run /\
  tmr_task_sched_switch_signal_output configured critical initial_local active sg original saved acquired entry initial_heap restored /\
  (forall X, safeExec (fun state => state = entry) (os_sched_task_body_program configured critical sg original) X ->
    safeExec (fun state => state = current) (StateRelMonad.ret returned) X).
Proof.
  intros environment critical task_abi sg entry first_installed initial_local active initial_heap last_entry context saved_sp
    outgoing hooked resumed original saved acquired receipt other frame first_heap input stopped before_heap output installed sp actual
    configured call local rest prefix complete Hinitial Hfirst Hlife Hswitch Hsave Hhook Hdestination Hprefix Hbridge Hcoverage Hreceipt.
  destruct (SelectedCompletionComposition.task_selected_completion_environment_sequence configured critical task_abi sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None frame call original saved acquired receipt other
    before_heap installed sp actual complete eq_refl Hcoverage) as [selected Hterminal].
  exists selected; intros restored Hrestore current returned.
  destruct (Hterminal restored Hrestore) as [last [Hlast [Htask Hsame]]].
  change (kernel_call_task_source returned current) in Htask.
  change (task_tcb_init_stack_same_call returned original) in Hsame.
  destruct (kernel_program_selected_c_sequence_resources configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ last)
    as [Hlast_input [Hendpoint Howned]].
  pose proof (proj1 (flag_pend_caller_restore_input_state_inv configured critical other
    (fun _ _ => receipt ** frame) sg (FlagPendTaskCaller returned) returned saved acquired current restored Howned)) as Hvalid.
  pose proof complete as [Hstate Hcompletion].
  destruct Hstate as [Hsaved [Hdestination' [Hhigh Hcurrent]]].
  assert (Hready : os_sched_task_current_ready returned current).
  { eapply SchedulerReturnFacts.os_sched_install_current_ready; try eassumption.
    exact (proj2 (proj2 Hsame)). }
  assert (Hbody : os_sched_task_body_source configured critical sg entry original returned current).
  { unfold current, InstallComponent.task_install_fields_current, call.
    eapply OsSchedTaskBodyTaskLastInstall with (first_installed := first_installed)
      (resumed := resumed) (before_heap := before_heap); try eassumption.
    - eapply os_sched_task_c_sequence_prefix; exact Hprefix.
    - reflexivity. }
  assert (Hnormal : kernel_call_normal_return original entry returned current).
  { split; [exact Hsame|]. intro Havailable.
    unfold kernel_call_stack_available; rewrite (proj1 Htask).
    unfold current, InstallComponent.task_install_fields_current, call.
    change (task_stack_take
      (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks) context.(os_sched_call_stack) outgoing)
      original.(os_sched_call_stack) (task_stack_key returned.(os_sched_call_stack)) = None).
    rewrite (proj2 (proj2 Hsame)); apply task_stack_take_lookup. }
  assert (Hcontrol : kernel_call_control_rely sg entry current).
  { unfold current, call.
    eapply SelectedControlComposition.task_last_call_selected_sequence_control with
      (first_installed := first_installed) (last_entry := last_entry) (saved_sp := saved_sp)
      (observer := original.(os_sched_call_invocation)) (origin := original.(os_sched_call_origin)); eassumption. }
  assert (Hobservations : os_sched_task_body_observation configured critical sg original entry returned current).
  { exact (conj Hbody (conj Hready (conj Hnormal (conj Hcontrol (fun _ => Htask))))). }
  assert (Hsignal : tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current).
  { eapply tmr_task_signal_lifetime_same_call; [exact Hsame|].
    eapply tmr_task_selected_c_sequence_preserves_signal_lifetime; [exact Hlast|].
    eapply tmr_task_selected_c_sequence_preserves_signal_lifetime; [exact Hprefix|].
    eapply tmr_task_hook_switch_preserves_signal_lifetime; [exact Hfirst|exact Hlife]. }
  assert (Hclose :
    coq_prop (flag_pend_call_endpoint_observations configured sg (FlagPendTaskCaller original) original hooked returned current) &&
    flag_pend_caller_restore_input configured critical other (fun _ _ => receipt ** frame) sg
      (FlagPendTaskCaller returned) returned saved acquired current |--
    tmr_task_sched_body_signal_post configured critical active sg original saved acquired entry).
  { intros heap [Hinner Howner].
    exists returned, current, other; split; [exact (conj Hobservations Hsignal)|].
    pose proof (proj1 (flag_pend_task_restore_input_masked_equiv configured critical other
      (fun _ _ => receipt ** frame) sg returned saved acquired current) heap Howner) as Hmasked.
    match type of Hmasked with ?P heap => match goal with |- ?Q heap => assert (Hresource : P |-- Q) end end.
    { sep_apply_l_atomic (Hreceipt returned Hsame Htask Hready); entailer!. }
    exact (Hresource heap Hmasked). }
  pose (tail := KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hlast_input (fun heap Howner => Howner) last Hclose).
  pose (run := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ prefix Hbridge tail).
  exists run; split.
  - apply KernelCSourceThen; [exact Hprefix|]. apply KernelCSourceAdapt; exact Hlast.
  - split.
    + split; [exact Hinitial|]. exact (proj2 (kernel_program_selected_c_sequence_resources configured critical sg
        original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ run)).
    + intros X Hsafe; eapply os_sched_task_body_return_safeexec; eassumption.
Qed.

Lemma tmr_task_irq_acquired_c_prefix_signal_output :
  forall environment critical sg entry first_installed initial_local active initial_heap handler irq_entry transfer
    original saved acquired receipt other frame first_heap input stopped before_heap output
    prepared hooked_heap installed selected after source prefix hook install restore,
  let configured := task_sw_hook_call_environment environment in
  forall (earlier : kernel_c_sequence (kernel_program_selected_c_step configured critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      first_installed first_heap input stopped irq_entry before_heap output),
  IRQAcquiredReturn.kernel_irq_acquired_c_completion environment critical sg handler irq_entry transfer original saved acquired
    receipt other frame before_heap prepared hooked_heap installed selected after source prefix hook install restore ->
  os_sched_task_switch_pre configured critical initial_local active sg original saved acquired entry initial_heap ->
  os_sched_switch_source configured.(task_stack_call_external) sg entry original first_installed ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) entry ->
  kernel_program_selected_c_sequence_source configured critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ earlier ->
  output |-- IRQCPrefix.os_int_exit_prefix_fields_owner configured critical sg handler irq_entry
    original saved acquired receipt other frame ->
  (forall returned, task_tcb_init_stack_same_call returned original ->
    kernel_call_task_source returned (os_int_exit_installed_state transfer) ->
    os_sched_task_current_ready returned (os_int_exit_installed_state transfer) ->
    IRQSelectedCompletion.irq_selected_suffix_receipt handler receipt frame |--
      active returned (os_int_exit_installed_state transfer)) ->
  let current := os_int_exit_installed_state transfer in
  let returned := kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack) transfer.(os_int_exit_incoming_fragments) in
  exists (run : kernel_c_sequence (kernel_program_selected_c_step configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)) first_installed first_heap input
    (orb stopped false) current after (tmr_task_sched_body_signal_post configured critical active sg original saved acquired entry)),
  kernel_program_selected_c_sequence_source configured critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ run /\
  tmr_task_sched_switch_signal_output configured critical initial_local active sg original saved acquired entry initial_heap after /\
  (forall X, safeExec (fun state => state = entry) (os_sched_task_body_program configured critical sg original) X ->
    safeExec (fun state => state = current) (StateRelMonad.ret returned) X).
Proof.
  intros environment critical sg entry first_installed initial_local active initial_heap handler irq_entry transfer original saved
    acquired receipt other frame first_heap input stopped before_heap output prepared hooked_heap installed selected after
    source prefix hook install restore configured earlier complete Hinitial Hfirst Hlife Hearlier Hbridge Hreceipt current returned.
  destruct (SelectedCompletionComposition.irq_acquired_completion_environment_sequence environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None handler irq_entry transfer original saved acquired
    receipt other frame before_heap prepared hooked_heap installed selected after source prefix hook install restore complete)
    as [last [Hlast [Htask [Hsame [Hready [Hidle [Hnonidle [Hnormal [Hrunning Henabled]]]]]]]]].
  assert (Hbody : os_sched_task_body_source configured critical sg entry original returned current).
  { eapply OsSchedTaskBodyIRQLastInstall with (first_installed := first_installed)
      (handler := handler) (irq_entry := irq_entry); try eassumption.
    - right; exists before_heap; eapply os_sched_task_c_sequence_prefix; exact Hearlier.
    - reflexivity.
    - exact (proj2 (proj2 Hsame)). }
  assert (Hfirst_running : first_installed.(SchedState).(isRunning) = entry.(SchedState).(isRunning)).
  { destruct Hfirst as [Hswitch [old_sp [outgoing [hooked [incoming [resumed [Hsave [Hhook [Hdest Hinstalled]]]]]]]]].
    change (hooked = os_sched_save_current_sp (os_sched_prefix_state entry)
      original.(os_sched_call_stack).(stackLeaseSlot) old_sp) in Hhook.
    rewrite Hinstalled, Hhook; exact (proj2 (proj2 (proj2 (os_sched_ready_checkpoint_frame entry)))). }
  assert (Hentry_enabled : os_sched_selection_enabled entry = true).
  { exact (proj1 (proj1 (os_sched_requests_switch_iff entry) (proj1 Hfirst))). }
  pose proof (SelectedControlComposition.kernel_program_selected_c_sequence_running configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ earlier) as Hprefix_running.
  assert (Hcontrol : kernel_call_control_rely sg entry current).
  { apply SelectedEndpointObservations.kernel_call_enabled_control_rely; [exact Hentry_enabled|exact Henabled|].
    change ((os_int_exit_installed_state transfer).(SchedState).(isRunning) = entry.(SchedState).(isRunning)).
    etransitivity; [exact Hrunning|].
    etransitivity; [exact Hprefix_running|exact Hfirst_running]. }
  assert (Hobservations : os_sched_task_body_observation configured critical sg original entry returned current).
  { exact (conj Hbody (conj Hready (conj (Hnormal entry) (conj Hcontrol (fun _ => Htask))))). }
  assert (Hsignal : tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current).
  { eapply tmr_task_signal_lifetime_same_call; [exact Hsame|].
    eapply tmr_task_selected_c_sequence_preserves_signal_lifetime; [exact Hlast|].
    eapply tmr_task_selected_c_sequence_preserves_signal_lifetime; [exact Hearlier|].
    eapply tmr_task_hook_switch_preserves_signal_lifetime; [exact Hfirst|exact Hlife]. }
  assert (Hclose : IRQSelectedCompletion.irq_selected_suffix_output configured critical sg handler transfer
    original saved acquired receipt other frame |-- tmr_task_sched_body_signal_post configured critical active sg original saved acquired entry).
  { intros heap Howner; exists returned, current, other; split; [exact (conj Hobservations Hsignal)|].
    pose proof (proj1 (flag_pend_task_restore_input_masked_equiv configured critical other
      (fun _ _ => IRQSelectedCompletion.irq_selected_suffix_receipt handler receipt frame)
      sg returned saved acquired current) heap Howner) as Hmasked.
    match type of Hmasked with ?P heap => match goal with |- ?Q heap => assert (Hresource : P |-- Q) end end.
    { sep_apply_l_atomic (Hreceipt returned Hsame Htask Hready); entailer!. }
    exact (Hresource heap Hmasked). }
  pose proof (proj1 (kernel_program_selected_c_sequence_resources configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ last)) as Hlast_input.
  pose (tail := KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hlast_input (fun heap Howner => Howner) last Hclose).
  pose (run := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ earlier Hbridge tail).
  exists run; split.
  - apply KernelCSourceThen; [exact Hearlier|]. apply KernelCSourceAdapt; exact Hlast.
  - split.
    + split; [exact Hinitial|]. exact (proj2 (kernel_program_selected_c_sequence_resources configured critical sg
        original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ run)).
    + intros X Hsafe; eapply os_sched_task_body_return_safeexec; eassumption.
Qed.

(** The no-switch constructor has a literal endpoint. Its ordinary post
    can therefore be strengthened without selecting another execution. *)
Lemma tmr_task_sched_nonswitch_body_signal_post : forall environment critical active sg original saved acquired entry,
  os_sched_requests_switch entry = false ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) entry ->
  os_sched_task_body_post environment critical active sg original saved acquired entry |--
  tmr_task_sched_body_signal_post environment critical active sg original saved acquired entry.
Proof.
  intros environment critical active sg original saved acquired entry Hrequest Hlife heap
    [returned [current [local [Hobservations Howned]]]].
  assert (Hendpoint : returned = original /\ current = os_sched_prefix_state entry).
  { destruct (proj1 Hobservations); [split; reflexivity| | |]; exfalso;
      match goal with Hfirst : os_sched_switch_source _ _ _ _ _ |- _ =>
        pose proof (proj1 Hfirst); congruence
      end. }
  destruct Hendpoint as [-> ->].
  exists original, (os_sched_prefix_state entry), local; split; [|exact Howned].
  split; [exact Hobservations|exact Hlife].
Qed.

(** The middle lifetime premise is the actual owned output of one of the
    producers above. The next lemma eliminates that post once and binds
    these facts to the same returned/current/heap tuple used by Restore. *)
Lemma tmr_task_sched_scoped_return_signal :
  forall environment critical sg original scheduled resumed returned mask saved before entry released current
    save_local saved_local active first_heap save_stop acquired_heap
    restore_local next_local released_heap restore_stop final_heap,
  SelectedEnvironmentPhaseEffects.os_sched_continuation_c_save_execution environment critical
    save_local saved_local active sg original mask before first_heap saved save_stop scheduled entry acquired_heap ->
  os_sched_task_body_observation environment critical sg scheduled entry resumed released ->
  tmr_task_signal_lifetime critical sg resumed.(os_sched_call_invocation) released ->
  SelectedEnvironmentPhaseEffects.os_sched_continuation_c_restore_execution environment critical
    restore_local next_local active sg resumed saved entry released released_heap restore_stop returned current final_heap ->
  os_sched_task_call_history environment critical sg original mask before returned current /\
  tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current /\
  (forall X : OsSchedCallContext -> UCOS2_Verify_State -> Prop,
    safeExec (fun state => state = before) (os_sched_task_program environment critical sg original mask) X ->
    safeExec (fun state => state = current) (StateRelMonad.ret returned) X).
Proof.
  intros until final_heap; intros Hsave Hbody Hlife Hrestore.
  assert (Hhistory : os_sched_task_call_history environment critical sg original mask before returned current).
  { exists scheduled, entry, resumed, released, saved; split.
    - eapply ContinuationPhaseEffects.os_sched_continuation_c_save_execution_implies_phase; exact Hsave.
    - split; [exact (proj1 Hbody)|].
      eapply ContinuationPhaseEffects.os_sched_continuation_c_restore_execution_implies_phase; exact Hrestore. }
  split; [exact Hhistory|]. split.
  - eapply tmr_task_scoped_restore_preserves_signal_lifetime; [exact Hrestore|exact Hlife].
  - intros X Hsafe; eapply os_sched_task_history_return_safeexec; eassumption.
Qed.

Lemma tmr_task_sched_body_signal_post_scoped_return :
  forall environment critical sg original scheduled mask saved before entry
    save_local saved_local active first_heap save_stop acquired_heap body_heap,
  SelectedEnvironmentPhaseEffects.os_sched_continuation_c_save_execution environment critical
    save_local saved_local active sg original mask before first_heap saved save_stop scheduled entry acquired_heap ->
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
      os_sched_task_call_history environment critical sg original mask before returned current /\
      tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current /\
      (forall X : OsSchedCallContext -> UCOS2_Verify_State -> Prop,
        safeExec (fun state => state = before) (os_sched_task_program environment critical sg original mask) X ->
        safeExec (fun state => state = current) (StateRelMonad.ret returned) X)).
Proof.
  intros until body_heap; intros Hsave
    [resumed [released [next_local [[Hbody Hlife] Howned]]]].
  exists resumed, released, next_local; split; [exact Hbody|].
  split; [exact Hlife|]. split; [exact Howned|].
  intros restored_local restore_stop returned current final_heap Hrestore.
  eapply tmr_task_sched_scoped_return_signal; eassumption.
Qed.

(** The protected Unlock prefix supplies the input lifetime for the
    Scheduler Save. No premise here describes a future body or Pend. *)
Lemma tmr_task_unlock_scoped_save_preserves_signal_lifetime :
  forall environment critical sg original mask before acquired restored unlocked
    save_local saved_local active first_heap saved save_stop scheduled entry acquired_heap,
  UCOS2_state_inv sg before ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) before ->
  os_sched_fields_checkpoint_sources (os_sched_unlock_checkpoint true)
    environment critical sg original mask before acquired restored unlocked ->
  SelectedEnvironmentPhaseEffects.os_sched_continuation_c_save_execution
    (task_sw_hook_call_environment environment) critical save_local saved_local active sg
    restored mask unlocked first_heap saved save_stop scheduled entry acquired_heap ->
  tmr_task_signal_lifetime critical sg scheduled.(os_sched_call_invocation) entry.
Proof.
  intros until acquired_heap; intros Hvalid Hlife Hprefix Hsave.
  eapply tmr_task_scoped_save_preserves_signal_lifetime; [exact Hsave|].
  eapply tmr_task_unlock_fields_prefix_preserves_signal_lifetime; eassumption.
Qed.

(** At the scheduled Unlock return, unpack the strengthened body post
    once. Its returned descriptor, current state, next local and SAME heap
    are the input indices of the actual Restore. This consumer preserves
    the original fields source packet and arbitrary continuation X. It
    asserts no source selection for an erased generic Scheduler history. *)
Lemma tmr_task_unlock_body_signal_post_scheduled_return :
  forall environment critical sg original mask before acquired restored unlocked
    scheduled saved entry save_local saved_local active first_heap save_stop acquired_heap body_heap,
  let configured := task_sw_hook_call_environment environment in
  os_sched_unlock_continuation_prefix environment critical sg original mask before acquired restored unlocked ->
  os_sched_fields_checkpoint_sources (os_sched_unlock_checkpoint true)
    environment critical sg original mask before acquired restored unlocked ->
  os_sched_unlock_requests acquired = true ->
  SelectedEnvironmentPhaseEffects.os_sched_continuation_c_save_execution configured critical
    save_local saved_local active sg restored mask unlocked first_heap saved save_stop scheduled entry acquired_heap ->
  tmr_task_sched_body_signal_post configured critical active sg scheduled saved entry entry body_heap ->
  exists resumed released next_local,
    os_sched_task_body_observation configured critical sg scheduled entry resumed released /\
    tmr_task_signal_lifetime critical sg resumed.(os_sched_call_invocation) released /\
    (kernel_continuation_call_masked configured.(task_stack_call_continuations) kernel_program_fields_inv
      next_local critical sg (task_stack_call_active_key resumed) resumed saved entry released **
      active resumed released) body_heap /\
    (forall restored_local restore_stop returned current final_heap,
      SelectedEnvironmentPhaseEffects.os_sched_continuation_c_restore_execution configured critical
        next_local restored_local active sg resumed saved entry released body_heap restore_stop returned current final_heap ->
      os_sched_unlock_fields_return_sources environment critical sg original mask before returned current /\
      os_sched_unlock_continuation_history environment critical sg original mask before returned current /\
      tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current /\
      (forall X : OsSchedCallContext -> UCOS2_Verify_State -> Prop,
        os_sched_unlock_continuation_safe environment critical sg original mask before X ->
        safeExec (fun state => state = current) (StateRelMonad.ret returned) X)).
Proof.
  intros until body_heap; intros configured Hprefix Hsources Hrequest Hsave Hpost.
  destruct (tmr_task_sched_body_signal_post_scoped_return configured critical sg restored scheduled
    mask saved unlocked entry save_local saved_local active first_heap save_stop acquired_heap body_heap
    Hsave Hpost) as [resumed [released [next_local [Hbody [Hlife [Howned Hreturn]]]]]].
  exists resumed, released, next_local; split; [exact Hbody|].
  split; [exact Hlife|]. split; [exact Howned|].
  intros restored_local restore_stop returned current final_heap Hrestore.
  destruct (Hreturn restored_local restore_stop returned current final_heap Hrestore)
    as [Hhistory [Hsignal Hsafe_sched]].
  assert (Htail : os_sched_unlock_tail_program environment critical sg mask
    (os_sched_unlock_requests acquired) restored unlocked returned current).
  { unfold os_sched_unlock_tail_program; rewrite Hrequest.
    apply os_sched_task_program_iff; exact Hhistory. }
  assert (Hfull : os_sched_unlock_continuation_history environment critical sg original mask before returned current).
  { unfold os_sched_unlock_continuation_history; rewrite (proj1 Hprefix).
    exists acquired, restored, unlocked; split; [exact Hprefix|exact Htail]. }
  split.
  - unfold os_sched_unlock_fields_return_sources; rewrite (proj1 Hprefix).
    exists acquired, restored, unlocked; split; [exact Hsources|exact Htail].
  - split; [exact Hfull|]. split; [exact Hsignal|].
    intros X Hsafe; eapply os_sched_unlock_continuation_safeexec_return; eassumption.
Qed.
