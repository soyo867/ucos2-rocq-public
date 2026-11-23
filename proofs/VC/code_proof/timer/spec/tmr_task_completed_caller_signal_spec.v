Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_signal_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_module_completion_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_phase_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_callee_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_boot_primitive_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_sched_phase_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.interrupt_call_c_primitive_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.interrupt.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Import PrimitiveComponent SchedulerPhaseCandidate SchedulerCalleePhaseComponent.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** All constructors of the existing completed source are considered. The
    View case has an InterruptCaller index; no Task execution is discarded. *)
Lemma tmr_task_module_completed_source_preserves_signal_lifetime :
  forall environment critical sg event,
  ModuleCompletionSource.flag_pend_selected_event_source environment critical sg event ->
  event.(flag_pend_event_caller) = FlagPendTaskCaller event.(flag_pend_event_original) ->
  tmr_task_signal_lifetime critical sg event.(flag_pend_event_original).(os_sched_call_invocation)
    event.(flag_pend_event_before) ->
  tmr_task_signal_lifetime critical sg event.(flag_pend_event_returned).(os_sched_call_invocation)
    event.(flag_pend_event_current).
Proof.
  intros environment critical sg event Hactual; destruct Hactual; cbn; intros Hcaller Hlife.
  - eapply tmr_task_scoped_save_preserves_signal_lifetime; eassumption.
  - eapply tmr_task_scoped_restore_preserves_signal_lifetime; eassumption.
  - destruct H; exact Hlife.
  - destruct H; discriminate Hcaller.
Qed.

(** Boot is excluded only by this call's existing Task-source observation.
    Consequence retains the original operation, caller, states and heaps. *)
Lemma tmr_task_completed_event_source_preserves_signal_lifetime :
  forall environment critical sg event,
  SelectedEventSources.flag_pend_selected_event_source environment critical sg event ->
  event.(flag_pend_event_caller) = FlagPendTaskCaller event.(flag_pend_event_original) ->
  kernel_call_task_source event.(flag_pend_event_original) event.(flag_pend_event_before) ->
  tmr_task_signal_lifetime critical sg event.(flag_pend_event_original).(os_sched_call_invocation)
    event.(flag_pend_event_before) ->
  tmr_task_signal_lifetime critical sg event.(flag_pend_event_returned).(os_sched_call_invocation)
    event.(flag_pend_event_current).
Proof.
  intros environment critical sg event Hactual; induction Hactual; cbn; intros Hcaller Htask Hlife.
  - eapply tmr_task_module_completed_source_preserves_signal_lifetime; eassumption.
  - pose proof (proj1 (FlagPendBootPrimitive.flag_pend_boot_save_completion_post
      _ _ _ _ _ _ _ _ _ _ _ _ _ H)) as Hboot.
    destruct Htask as [Horigin _]; rewrite Hboot in Horigin; discriminate.
  - pose proof (proj1 (FlagPendBootPrimitive.flag_pend_boot_restore_completion_post
      _ _ _ _ _ _ _ _ _ _ _ _ _ H)) as Hboot.
    destruct Htask as [Horigin _]; rewrite Hboot in Horigin; discriminate.
  - eapply IHHactual; eassumption.
Qed.

Lemma tmr_task_completed_caller_source_preserves_signal_lifetime :
  forall operation environment critical sg original before input first_heap
    returned_caller returned current last_heap output,
  CompletedCallerSource.flag_pend_selected_completed_source operation environment critical sg
    (FlagPendTaskCaller original) original before input first_heap returned_caller returned current last_heap output ->
  kernel_call_task_source original before ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) before ->
  tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current.
Proof.
  intros until output; intros Hactual Htask Hlife.
  exact (tmr_task_completed_event_source_preserves_signal_lifetime environment critical sg _
    Hactual eq_refl Htask Hlife).
Qed.

Lemma tmr_task_completed_save_event_preserves_signal_lifetime :
  forall environment critical local active sg original mask saved before
    returned_caller returned current next_local first_heap last_heap,
  CompletedCallerEvents.flag_pend_selected_caller_save_event environment critical local active sg
    (FlagPendTaskCaller original) original mask saved before
    returned_caller returned current next_local first_heap last_heap ->
  kernel_call_task_source original before ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) before ->
  tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current.
Proof.
  intros until last_heap; intros [_ [_ [_ [_ Hactual]]]] Htask Hlife.
  eapply tmr_task_completed_caller_source_preserves_signal_lifetime; eassumption.
Qed.

Lemma tmr_task_completed_restore_event_preserves_signal_lifetime :
  forall environment critical local active sg original saved acquired before
    returned_caller returned current next_local first_heap last_heap,
  CompletedCallerEvents.flag_pend_selected_caller_restore_event environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before
    returned_caller returned current next_local first_heap last_heap ->
  kernel_call_task_source original before ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) before ->
  tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current.
Proof.
  intros until last_heap; intros [_ [_ [_ Hactual]]] Htask Hlife.
  eapply tmr_task_completed_caller_source_preserves_signal_lifetime; eassumption.
Qed.

(** The actual caller output is opened once. Its source event and lifetime
    share the same returned descriptor, state, local family and final heap. *)
Definition tmr_task_completed_save_signal_output environment critical local active sg original mask before
  first_heap saved : Assertion :=
  fun last_heap => exists returned_caller returned current next_local,
    CompletedCallerEvents.flag_pend_selected_caller_save_event environment critical local active sg
      (FlagPendTaskCaller original) original mask saved before
      returned_caller returned current next_local first_heap last_heap /\
    tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current.

Definition tmr_task_completed_restore_signal_output environment critical local active sg original saved acquired before
  first_heap : Assertion :=
  fun last_heap => exists returned_caller returned current next_local,
    CompletedCallerEvents.flag_pend_selected_caller_restore_event environment critical local active sg
      (FlagPendTaskCaller original) original saved acquired before
      returned_caller returned current next_local first_heap last_heap /\
    tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current.

Lemma tmr_task_completed_save_output_signal :
  forall environment critical local active sg original mask before first_heap saved,
  kernel_call_task_source original before ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) before ->
  CompletedCallerEvents.flag_pend_selected_caller_save_output environment critical local active sg
    (FlagPendTaskCaller original) original mask before first_heap saved |--
  tmr_task_completed_save_signal_output environment critical local active sg original mask before first_heap saved.
Proof.
  intros until saved; intros Htask Hlife heap [returned_caller [returned [current [next_local Hevent]]]].
  exists returned_caller, returned, current, next_local; split; [exact Hevent|].
  eapply tmr_task_completed_save_event_preserves_signal_lifetime; eassumption.
Qed.

Lemma tmr_task_completed_restore_output_signal :
  forall environment critical local active sg original saved acquired before first_heap,
  kernel_call_task_source original before ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) before ->
  CompletedCallerEvents.flag_pend_selected_caller_restore_output environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before first_heap |--
  tmr_task_completed_restore_signal_output environment critical local active sg original saved acquired before first_heap.
Proof.
  intros until first_heap; intros Htask Hlife heap [returned_caller [returned [current [next_local Hevent]]]].
  exists returned_caller, returned, current, next_local; split; [exact Hevent|].
  eapply tmr_task_completed_restore_event_preserves_signal_lifetime; eassumption.
Qed.

Lemma tmr_task_active_save_output_signal :
  forall environment critical local active sg original mask before first_heap saved,
  active <> (fun _ _ => emp) -> kernel_call_task_source original before ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) before ->
  FlagPendActiveCaller.flag_pend_selected_caller_save_output environment critical local active sg
    (FlagPendTaskCaller original) original mask before first_heap saved |--
  tmr_task_completed_save_signal_output environment critical local active sg original mask before first_heap saved.
Proof.
  intros until saved; intros Hactive Htask Hlife heap Houtput.
  apply (tmr_task_completed_save_output_signal environment critical local active sg original mask before
    first_heap saved Htask Hlife).
  exact (FlagPendActiveCaller.flag_pend_save_output_nonempty environment critical local active sg
    (FlagPendTaskCaller original) original mask before first_heap saved Hactive heap Houtput).
Qed.

Lemma tmr_task_active_restore_output_signal :
  forall environment critical local active sg original saved acquired before first_heap,
  active <> (fun _ _ => emp) -> kernel_call_task_source original before ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) before ->
  FlagPendActiveCaller.flag_pend_selected_caller_restore_output environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before first_heap |--
  tmr_task_completed_restore_signal_output environment critical local active sg original saved acquired before first_heap.
Proof.
  intros until first_heap; intros Hactive Htask Hlife heap Houtput.
  apply (tmr_task_completed_restore_output_signal environment critical local active sg original saved acquired before
    first_heap Htask Hlife).
  exact (FlagPendActiveCaller.flag_pend_restore_output_nonempty environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before first_heap Hactive heap Houtput).
Qed.

(** Direct replacement for the ordinary final C consumer: the existing
    completed Restore output is opened once, and its same source supplies
    lifetime before the returned descriptor/current/local are packaged. *)
Lemma tmr_task_completed_restore_output_history_signal :
  forall environment critical local active sg original scheduled resumed
    mask saved before entry released before_heap,
  kernel_call_task_source scheduled entry ->
  os_sched_task_save_observation environment critical sg original mask saved before scheduled entry ->
  os_sched_task_body_observation environment critical sg scheduled entry resumed released ->
  UCOS2_state_inv sg released ->
  tmr_task_signal_lifetime critical sg resumed.(os_sched_call_invocation) released ->
  SelectedCallerPhaseComponent.flag_pend_selected_caller_restore_output environment critical local active sg
    (FlagPendTaskCaller resumed) resumed saved entry released before_heap |--
  tmr_task_sched_history_signal_post environment critical active sg original mask before.
Proof.
  intros environment critical local active sg original scheduled resumed mask saved before entry released before_heap
    Hscheduled Hsave Hbody Hvalid Hlife heap
    [returned_caller [returned [current [next_local Hevent]]]].
  pose proof (proj2 (proj2 (proj2 (proj2 Hbody))) Hscheduled) as Hresumed.
  pose proof (tmr_task_completed_restore_event_preserves_signal_lifetime environment critical local active sg
    resumed saved entry released returned_caller returned current next_local before_heap heap
    Hevent Hresumed Hlife) as Hsignal.
  destruct Hevent as [Hobservation [Hbefore [Hafter Hcompleted]]].
  destruct returned_caller as [next|view key]; [|contradiction].
  cbn [CompletedCallerEvents.flag_pend_caller_restore_observation] in Hobservation.
  destruct Hobservation as [_ [Hnext [Heffect [Hsame [Hpreserved Htransport]]]]]; subst next.
  destruct (CompletedCallerSource.flag_pend_selected_completed_source_endpoints
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcompleted) as [Hendpoint _].
  destruct Hendpoint as [Hready_after [Hidle [Hnonidle [Hnormal Hcontrol]]]].
  assert (Hnonboot : resumed.(os_sched_call_origin) <> BootInvocation).
  { rewrite (proj1 Hresumed); discriminate. }
  specialize (Hcontrol Hnonboot).
  assert (Hcurrent_ready : os_sched_task_current_ready returned current).
  { apply Hready_after; split; [exact Hresumed|exact (proj1 (proj2 Hbody))]. }
  assert (Hrestore : os_sched_task_restore_observation environment critical sg resumed released returned current).
  { exact (conj Heffect (conj Hsame (conj (Hpreserved Hresumed)
      (conj Htransport (conj Hcurrent_ready (conj Hnormal Hcontrol)))))). }
  pose proof (os_sched_task_observations_compose environment critical sg original scheduled resumed returned
    mask saved before entry released current Hsave Hbody Hrestore Hvalid) as Hhistory.
  assert (Hmask : armv7a_irq_fiq_mask saved = mask).
  { destruct Hsave as [_ [_ [Hsaved _]]]; exact (proj2 Hsaved). }
  pose proof (proj1 (flag_pend_task_save_input_closed_equiv environment critical next_local active sg
    returned (armv7a_irq_fiq_mask saved) current) heap Hafter) as Hclosed.
  rewrite Hmask in Hclosed.
  exists returned, current, next_local; split; [exact (conj Hhistory Hsignal)|exact Hclosed].
Qed.
