From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_scheduler_entry_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_entry_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_idle_factory_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_completed_caller_signal_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_signal_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_callee_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.interrupt.
Import UCOS2_C_Rules SchedulerPhaseCandidate SchedulerCalleePhaseComponent.
Import PrimitiveComponent FlagPendSchedulerResources.
Local Open Scope sac_scope.

(** Read both observations from the same completed Save event already used
    by the C input. The returned descriptor, state and heap are unchanged. *)
Lemma tmr_task_completed_save_event_idle_non_idle :
  forall environment critical local active sg original mask saved before
    returned_caller returned current next_local first_heap last_heap,
  SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event environment critical local active sg
    (FlagPendTaskCaller original) original mask saved before
    returned_caller returned current next_local first_heap last_heap ->
  kernel_call_task_source original before ->
  task_idle_ready sg before.(TskState) -> flag_pend_non_idle_at sg original before ->
  task_idle_ready sg current.(TskState) /\ flag_pend_non_idle_at sg returned current.
Proof.
  intros until last_heap; intros [_ [_ [_ [_ Hcompleted]]]] Htask Hidle Hnonidle.
  destruct (CompletedCallerSource.flag_pend_selected_completed_source_endpoints
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcompleted) as [Hendpoint _].
  cbn [flag_pend_call_endpoint_observations] in Hendpoint.
  destruct Hendpoint as [_ [Hidle_return [Hnonidle_return _]]].
  split; [apply Hidle_return | apply Hnonidle_return]; split; assumption.
Qed.

(** This C-facing output retains the actual source producer's complete body
    packet before it is erased. It is not derivable from the old, weaker
    source_output alone. Each original source branch must produce the packet. *)
Definition tmr_task_sched_switch_idle_output environment critical local active sg
  original saved acquired entry initial_heap : Assertion :=
  fun returned_heap =>
    os_sched_task_switch_pre environment critical local active sg original saved acquired entry initial_heap /\
    tmr_task_actual_body_idle_post environment critical active sg original saved acquired entry returned_heap.

Definition tmr_task_sched_switch_entry_output environment critical local active sg
  original saved acquired entry initial_heap : Assertion :=
  fun returned_heap =>
    os_sched_task_switch_pre environment critical local active sg original saved acquired entry initial_heap /\
    exists returned current next_local,
      ((os_sched_task_body_observation environment critical sg original entry returned current /\
        tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current) /\
       task_idle_ready sg current.(TskState) /\ flag_pend_non_idle_at sg returned current) /\
      (kernel_continuation_call_masked environment.(task_stack_call_continuations) kernel_program_fields_inv
        next_local critical sg (task_stack_call_active_key returned) returned saved acquired current **
        active returned current) returned_heap.

Lemma tmr_task_actual_body_idle_post_switch_output :
  forall environment critical local active sg original saved acquired entry initial_heap,
  os_sched_task_switch_pre environment critical local active sg original saved acquired entry initial_heap ->
  tmr_task_actual_body_idle_post environment critical active sg original saved acquired entry |--
  tmr_task_sched_switch_idle_output environment critical local active sg original saved acquired entry initial_heap.
Proof.
  intros environment critical local active sg original saved acquired entry initial_heap Hpre heap Hpost.
  exact (conj Hpre Hpost).
Qed.

Lemma tmr_task_sched_switch_idle_output_implies_source :
  forall environment critical local active sg original saved acquired entry initial_heap,
  tmr_task_sched_switch_idle_output environment critical local active sg original saved acquired entry initial_heap |--
  os_sched_task_switch_source_output environment critical local active sg original saved acquired entry initial_heap.
Proof.
  intros environment critical local active sg original saved acquired entry initial_heap heap
    [Hpre [returned [current [next_local [[body [Hreceipt [Hbody Hentry]]] Howner]]]]].
  destruct Hbody as [Hsource [Hready Hrest]].
  split; [exact Hpre|]. exists returned, current, next_local.
  exact (conj (conj Hsource Hrest) Howner).
Qed.

Lemma tmr_task_registered_switch_idle_output_entry :
  forall environment critical local active sg original saved acquired entry initial_heap,
  let configured := task_sw_hook_call_environment environment in
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) entry ->
  tmr_task_sched_switch_idle_output configured critical local active sg original saved acquired entry initial_heap |--
  tmr_task_sched_switch_entry_output configured critical local active sg original saved acquired entry initial_heap.
Proof.
  intros environment critical local active sg original saved acquired entry initial_heap configured Hcoverage Hlife
    heap [Hpre [returned [current [next_local [[body [Hreceipt [Hbody Hentry]]] Howner]]]]].
  pose proof (proj1 (tmr_task_switch_pre_event_pool configured critical local active sg original
    saved acquired entry initial_heap Hpre)) as Hpool.
  assert (Hconfigured : tmr_task_registered_source_coverage configured.(task_stack_call_external) critical).
  { apply tmr_task_registered_source_coverage_task_sw_hook; exact Hcoverage. }
  assert (Hsignal : tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current).
  { eapply tmr_task_registered_body_source_preserves_signal_lifetime;
      [exact Hconfigured | apply task_sw_hook_call_environment_source_binding |
       exact Hpool | exact Hlife | exact (proj1 Hbody)]. }
  split; [exact Hpre|]. exists returned, current, next_local.
  exact (conj (conj (conj Hbody Hsignal) Hentry) Howner).
Qed.

(** Reorganize one known body owner without opening and reselection of an
    existential body post. The C continuation keeps this returned tuple. *)
Lemma tmr_task_sched_same_body_restore_input :
  forall environment critical next_local active sg returned saved acquired current,
  os_sched_task_current_ready returned current ->
  (kernel_continuation_call_masked environment.(task_stack_call_continuations)
    kernel_program_fields_inv next_local critical sg (task_stack_call_active_key returned)
    returned saved acquired current ** active returned current) |--
  coq_prop (UCOS2_state_inv sg current) &&
    (os_sched_task_restore_input environment critical next_local active sg returned saved acquired current **
      unmap_table_rep sg).
Proof.
  intros environment critical next_local active sg returned saved acquired current Hready heap Howned.
  assert (Hopen :
    (kernel_continuation_call_masked environment.(task_stack_call_continuations)
      kernel_program_fields_inv next_local critical sg (task_stack_call_active_key returned)
      returned saved acquired current ** active returned current) |--
    coq_prop (UCOS2_state_inv sg current) &&
    ((os_sched_fields_restore_input environment critical next_local sg returned saved acquired current **
      active returned current) ** unmap_table_rep sg)).
  { sep_apply_l_atomic (proj2 (os_sched_fields_restore_input_masked_world
      environment critical next_local sg returned saved acquired current)).
    unfold os_sched_fields_restore_input, UCOS2_fields_inv; entailer!.
    all: match goal with |- ?P |-- coq_prop _ && ?Q =>
      assert (Hspatial_reorder : P |-- Q) by entailer!;
      intros actual Hresources;
      split; [exact H0|exact (Hspatial_reorder actual Hresources)]
    end.
  }
  destruct (Hopen heap Howned) as [Hvalid [body_heap [unmap_heap [Hjoin [Hresources Hunmap]]]]].
  split; [exact Hvalid|]. exists body_heap, unmap_heap; split; [exact Hjoin|].
  split; [split; [exact Hready|exact Hresources]|exact Hunmap].
Qed.

(** The final C Restore is opened once. Its endpoint facts, actual history,
    signal lifetime and closed continuation use exactly one returned tuple. *)
Lemma tmr_task_completed_restore_output_history_entry :
  forall environment critical local active sg original scheduled resumed
    mask saved before entry released before_heap,
  kernel_call_task_source scheduled entry ->
  os_sched_task_save_observation environment critical sg original mask saved before scheduled entry ->
  os_sched_task_body_observation environment critical sg scheduled entry resumed released ->
  UCOS2_state_inv sg released ->
  tmr_task_signal_lifetime critical sg resumed.(os_sched_call_invocation) released ->
  task_idle_ready sg released.(TskState) -> flag_pend_non_idle_at sg resumed released ->
  SelectedCallerPhaseComponent.flag_pend_selected_caller_restore_output environment critical local active sg
    (FlagPendTaskCaller resumed) resumed saved entry released before_heap |--
  tmr_task_sched_history_entry_post environment critical active sg original mask before.
Proof.
  intros environment critical local active sg original scheduled resumed mask saved before entry released before_heap
    Hscheduled Hsave Hbody Hvalid Hlife Hidle_before Hnonidle_before heap
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
  specialize (Hidle (conj Hresumed Hidle_before)).
  specialize (Hnonidle (conj Hresumed Hnonidle_before)).
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
  exists returned, current, next_local; split; [|exact Hclosed].
  exact (conj (conj Hhistory Hsignal) (conj Hidle Hnonidle)).
Qed.
