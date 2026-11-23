(* Report candidate: actual module completions; staged only by the parent. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_events_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.interrupt_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_module_completion_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_phase_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_phase_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_boot_primitive_spec.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module CompletedCallerEvents.
Import PrimitiveComponent SelectedProgramEvents.
Import SelectedEnvironmentPhaseEffects SelectedEnvironmentPhaseProperties CompletedCallerSource.

Definition flag_pend_caller_save_observation environment critical sg caller original returned_caller returned
  mask saved before acquired : Prop :=
  match caller, returned_caller with
  | FlagPendTaskCaller actual, FlagPendTaskCaller next =>
      actual = original /\ next = returned /\
      ContinuationPhaseEffects.os_sched_continuation_phase_save_effect environment critical sg original mask saved before returned acquired /\
      task_tcb_init_stack_same_call returned original /\
      task_tcb_init_stack_source_preserved original before acquired
  | FlagPendInterruptCaller view key, FlagPendInterruptCaller next next_key =>
      returned = original /\ next_key = key /\ sched_fields_same_view next view /\
      critical_region_interval critical sg view.(os_execution_invocation) before acquired
  | _, _ => False
  end.

Definition flag_pend_caller_restore_observation environment critical sg caller original returned_caller returned
  released current : Prop :=
  match caller, returned_caller with
  | FlagPendTaskCaller actual, FlagPendTaskCaller next =>
      actual = original /\ next = returned /\
      ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect environment critical sg original released returned current /\
      task_tcb_init_stack_same_call returned original /\
      (kernel_call_task_source original released ->
        task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released current) /\
      (UCOS2_state_inv sg released -> task_tcb_init_stack_source_preserved original released current)
  | FlagPendInterruptCaller view key, FlagPendInterruptCaller next next_key =>
      returned = original /\ next_key = key /\ sched_fields_same_view next view /\
      critical_region_interval critical sg view.(os_execution_invocation) released current
  | _, _ => False
  end.

Definition flag_pend_selected_caller_save_event environment critical local active sg caller original mask saved before
  returned_caller returned current next_local (first_heap last_heap : model) : Prop :=
  flag_pend_caller_save_observation environment critical sg caller original returned_caller returned mask saved before current /\
  interrupt_saved_value mask saved /\
  flag_pend_caller_save_input environment critical local active sg caller original mask before first_heap /\
  flag_pend_caller_restore_input environment critical next_local active sg returned_caller returned saved current current last_heap /\
  CompletedCallerSource.flag_pend_selected_completed_source FlagPendSaveSource environment critical sg caller original before
    (flag_pend_caller_save_input environment critical local active sg caller original mask before)
    first_heap returned_caller returned current last_heap
    (flag_pend_caller_restore_input environment critical next_local active sg returned_caller returned saved current current).

Definition flag_pend_selected_caller_save_output environment critical local active sg caller original mask before
  first_heap saved : Assertion :=
  fun last_heap => exists returned_caller returned current next_local,
    flag_pend_selected_caller_save_event environment critical local active sg caller original mask saved before
      returned_caller returned current next_local first_heap last_heap.

Definition flag_pend_selected_caller_restore_event environment critical local active sg caller original saved acquired before
  returned_caller returned current next_local (first_heap last_heap : model) : Prop :=
  flag_pend_caller_restore_observation environment critical sg caller original returned_caller returned before current /\
  flag_pend_caller_restore_input environment critical local active sg caller original saved acquired before first_heap /\
  flag_pend_caller_save_input environment critical next_local active sg returned_caller returned
    (armv7a_irq_fiq_mask saved) current last_heap /\
  CompletedCallerSource.flag_pend_selected_completed_source FlagPendRestoreSource environment critical sg caller original before
    (flag_pend_caller_restore_input environment critical local active sg caller original saved acquired before)
    first_heap returned_caller returned current last_heap
    (flag_pend_caller_save_input environment critical next_local active sg returned_caller returned
      (armv7a_irq_fiq_mask saved) current).

Definition flag_pend_selected_caller_restore_output environment critical local active sg caller original saved acquired before
  first_heap : Assertion :=
  fun last_heap => exists returned_caller returned current next_local,
    flag_pend_selected_caller_restore_event environment critical local active sg caller original saved acquired before
      returned_caller returned current next_local first_heap last_heap.

(** This conditional call observation uses the original registration to
    identify any origin quantified by the old call-preserved property.
    It needs no all-origin transport assumption and applies to arbitrary
    active owners once an actual terminal has produced its returned source. *)
Lemma os_sched_continuation_c_restore_execution_call_preserved :
  forall environment critical local next_local active sg original saved acquired before first_heap
    stopped returned current last_heap,
  os_sched_continuation_c_restore_execution environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap ->
  kernel_call_task_source returned current ->
  task_invocation_active before.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) before current.
Proof.
  intros until last_heap; intros Hactual Hreturned Hactive_before Hvalid_before.
  destruct (os_sched_continuation_c_restore_execution_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual)
    as [Hinput [Hendpoint Houtput]].
  destruct Hendpoint as [Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]].
  pose proof (proj1 (flag_pend_caller_save_input_state_inv environment critical next_local active sg
    (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current last_heap Houtput)) as Hvalid.
  destruct (os_sched_continuation_c_restore_execution_creation_name_timer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual)
    as [Hcreation [Hname Htimer]].
  pose proof (proj1 (task_tcb_init_stack_same_call_source_iff returned original current (proj1 Hnormal))
    Hreturned) as Hfinal.
  split; [exact Hvalid|]. split; [exact Hcreation|]. split; [|exact Hname].
  intros origin Hactive.
  destruct Hactive_before as [Hregistered Hrest].
  destruct Hfinal as [Horigin_final [Hactive_final Hcurrent_final]].
  destruct Hactive as [Hregistered_other Hrest_other].
  assert (origin = original.(os_sched_call_origin)) by congruence.
  subst origin; exact Hactive_final.
Qed.

Local Lemma normal_return_source_preserved : forall original returned before current,
  kernel_call_normal_return original before returned current ->
  kernel_call_task_source returned current ->
  task_tcb_init_stack_source_preserved original before current.
Proof.
  intros original returned before current [Hsame Havailable] Hreturned Hinitial.
  exact (proj1 (task_tcb_init_stack_same_call_source_iff returned original current Hsame) Hreturned).
Qed.

Lemma scoped_save_execution_complete_event :
  forall environment critical local next_local active sg original mask before first_heap saved stopped returned current last_heap,
  os_sched_continuation_c_save_execution environment critical local next_local active sg
    original mask before first_heap saved stopped returned current last_heap ->
  kernel_call_task_source returned current ->
  flag_pend_selected_caller_save_event environment critical local active sg
    (FlagPendTaskCaller original) original mask saved before (FlagPendTaskCaller returned) returned current next_local first_heap last_heap.
Proof.
  intros until last_heap; intros Hactual Hreturned.
  destruct (os_sched_continuation_c_save_execution_effect_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual)
    as [Heffect [Hsaved Hsource]].
  pose proof (ContinuationPhaseEffects.os_sched_scoped_phase_save_effect_implies_phase _ _ _ _ _ _ _ _ _ Heffect) as Hphase.
  destruct (os_sched_continuation_c_save_execution_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual)
    as [Hinput [Hendpoint Houtput]].
  destruct Hendpoint as [Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]].
  unfold flag_pend_selected_caller_save_event.
  refine (conj _ (conj Hsaved (conj Hinput (conj Houtput _)))).
  - cbn [flag_pend_caller_save_observation].
    refine (conj eq_refl (conj eq_refl (conj Hphase (conj (proj1 Hnormal) _)))).
    eapply normal_return_source_preserved; eassumption.
  - change (flag_pend_selected_event_source environment critical sg
      (flag_pend_task_save_completed_c_event environment critical local next_local active sg
        original mask saved before first_heap returned current last_heap)); eapply flag_pend_task_save_source_from_execution; exact Hactual.
Qed.

Lemma scoped_restore_execution_complete_event :
  forall environment critical local next_local active sg original saved acquired before first_heap stopped returned current last_heap,
  os_sched_continuation_c_restore_execution environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap ->
  kernel_call_task_source returned current ->
  flag_pend_selected_caller_restore_event environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before (FlagPendTaskCaller returned) returned current next_local first_heap last_heap.
Proof.
  intros until last_heap; intros Hactual Hreturned.
  destruct (os_sched_continuation_c_restore_execution_effect_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual)
    as [Heffect Hsource].
  pose proof (ContinuationPhaseEffects.os_sched_scoped_phase_restore_effect_implies_phase _ _ _ _ _ _ _ Heffect) as Hphase.
  destruct (os_sched_continuation_c_restore_execution_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual)
    as [Hinput [Hendpoint Houtput]].
  destruct Hendpoint as [Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]].
  unfold flag_pend_selected_caller_restore_event.
  refine (conj _ (conj Hinput (conj Houtput _))).
  - cbn [flag_pend_caller_restore_observation].
    refine (conj eq_refl (conj eq_refl (conj Hphase (conj (proj1 Hnormal) (conj _ _))))).
    + intro Horiginal; eapply os_sched_continuation_c_restore_execution_call_preserved;
        [exact Hactual|exact Hreturned|exact (proj1 (proj2 Horiginal))].
    + intros _; eapply normal_return_source_preserved; eassumption.
  - change (flag_pend_selected_event_source environment critical sg
      (flag_pend_task_restore_completed_c_event environment critical local next_local active sg
        original saved acquired before first_heap returned current last_heap)); eapply flag_pend_task_restore_source_from_execution; exact Hactual.
Qed.

Lemma scoped_save_event_output :
  forall environment critical local next_local active sg original mask before first_heap saved returned current last_heap,
  flag_pend_selected_caller_save_event environment critical local active sg
    (FlagPendTaskCaller original) original mask saved before (FlagPendTaskCaller returned) returned current next_local first_heap last_heap ->
  flag_pend_selected_caller_save_output environment critical local active sg
    (FlagPendTaskCaller original) original mask before first_heap saved last_heap.
Proof. intros; exists (FlagPendTaskCaller returned), returned, current, next_local; assumption. Qed.

Lemma scoped_restore_event_output :
  forall environment critical local next_local active sg original saved acquired before first_heap returned current last_heap,
  flag_pend_selected_caller_restore_event environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before (FlagPendTaskCaller returned) returned current next_local first_heap last_heap ->
  flag_pend_selected_caller_restore_output environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before first_heap last_heap.
Proof. intros; exists (FlagPendTaskCaller returned), returned, current, next_local; assumption. Qed.

End CompletedCallerEvents.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module CompletedUninterruptedCallerEvents.
Import PrimitiveComponent SelectedProgramEvents CompletedCallerEvents ModuleCompletionSource CompletedCallerSource.

Lemma primitive_save_observation_implies_environment :
  forall environment critical sg caller original returned_caller returned mask saved before acquired,
  PrimitiveComponent.flag_pend_caller_save_observation environment critical sg
    caller original returned_caller returned mask saved before acquired ->
  CompletedCallerEvents.flag_pend_caller_save_observation environment critical sg
    caller original returned_caller returned mask saved before acquired.
Proof.
  intros environment critical sg caller original returned_caller returned mask saved before acquired Hobs.
  destruct caller as [actual|view key], returned_caller as [next|next_view next_key];
    cbn [PrimitiveComponent.flag_pend_caller_save_observation
      CompletedCallerEvents.flag_pend_caller_save_observation] in *; try contradiction.
  - destruct Hobs as [Hactual [Hnext [Heffect [Hsame Hsource]]]].
    refine (conj Hactual (conj Hnext (conj _ (conj Hsame Hsource)))).
    apply ContinuationPhaseEffects.os_sched_continuation_save_effect_implies_phase; exact Heffect.
  - exact Hobs.
Qed.

Lemma primitive_restore_observation_implies_environment :
  forall environment critical sg caller original returned_caller returned released current,
  PrimitiveComponent.flag_pend_caller_restore_observation environment critical sg
    caller original returned_caller returned released current ->
  CompletedCallerEvents.flag_pend_caller_restore_observation environment critical sg
    caller original returned_caller returned released current.
Proof.
  intros environment critical sg caller original returned_caller returned released current Hobs.
  destruct caller as [actual|view key], returned_caller as [next|next_view next_key];
    cbn [PrimitiveComponent.flag_pend_caller_restore_observation
      CompletedCallerEvents.flag_pend_caller_restore_observation] in *; try contradiction.
  - destruct Hobs as [Hactual [Hnext [Heffect [Hsame [Hcall Hsource]]]]].
    refine (conj Hactual (conj Hnext (conj _ (conj Hsame (conj (fun _ => Hcall) Hsource))))).
    apply ContinuationPhaseEffects.os_sched_continuation_restore_effect_implies_phase; exact Heffect.
  - exact Hobs.
Qed.

Lemma flag_pend_task_uninterrupted_save_event :
  forall environment critical local active sg call mask state arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers before final_registers after,
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller call) call mask state before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before final_registers state after ->
  CompletedCallerEvents.flag_pend_selected_caller_save_event environment critical local active sg
    (FlagPendTaskCaller call) call mask final_registers.(kernel_save_r0) state
    (FlagPendTaskCaller call) call state local before after.
Proof.
  intros environment critical local active sg call mask state arch save registers before final_registers after
    Hreturn Hvalid Hmask Hinput Hactual.
  destruct (PrimitiveComponent.flag_pend_task_uninterrupted_save_c_event environment critical sg
    local active call mask state arch save registers before final_registers after
    Hreturn Hvalid Hmask Hinput Hactual) as [Hobs [Hsaved [Hpacket Hsequence]]].
  destruct (PrimitiveComponent.flag_pend_task_primitive_c_event_resources environment critical sg _ Hpacket)
    as [Hbefore [Hendpoints Houtput]].
  unfold CompletedCallerEvents.flag_pend_selected_caller_save_event.
  refine (conj _ (conj Hsaved (conj Hinput (conj Houtput _)))).
  - apply primitive_save_observation_implies_environment; exact Hobs.
  - match type of Hpacket with flag_pend_task_primitive_c_event _ _ _ ?event =>
      eapply (CompletedCallerSource.flag_pend_completed_source_from_module environment critical sg event)
    end.
    + apply ModuleCompletionSource.FlagPendModuleUninterrupted; exact Hpacket.
    + intros h Howned; exact Howned.
Qed.

Lemma flag_pend_task_uninterrupted_restore_event :
  forall environment critical local active sg call saved acquired state arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor before written middle final_cursor after,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller call) call saved acquired state before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  CompletedCallerEvents.flag_pend_selected_caller_restore_event environment critical local active sg
    (FlagPendTaskCaller call) call saved acquired state
    (FlagPendTaskCaller call) call state local before after.
Proof.
  intros environment critical local active sg call saved acquired state arch restore cursor before written middle final_cursor after
    Hr0 Hmask Hinput Hprefix Hsuffix.
  destruct (PrimitiveComponent.flag_pend_task_uninterrupted_restore_c_event environment critical sg
    local active call saved acquired state arch restore cursor before written middle final_cursor after
    Hr0 Hmask Hinput Hprefix Hsuffix) as [Hobs [Hpacket Hsequence]].
  destruct (PrimitiveComponent.flag_pend_task_primitive_c_event_resources environment critical sg _ Hpacket)
    as [Hbefore [Hendpoints Houtput]].
  unfold CompletedCallerEvents.flag_pend_selected_caller_restore_event.
  refine (conj _ (conj Hinput (conj Houtput _))).
  - apply primitive_restore_observation_implies_environment; exact Hobs.
  - match type of Hpacket with flag_pend_task_primitive_c_event _ _ _ ?event =>
      eapply (CompletedCallerSource.flag_pend_completed_source_from_module environment critical sg event)
    end.
    + apply ModuleCompletionSource.FlagPendModuleUninterrupted; exact Hpacket.
    + intros h Howned; exact Howned.
Qed.

Lemma flag_pend_task_uninterrupted_save_output :
  forall environment critical local active sg call mask state arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers before final_registers after,
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller call) call mask state before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before final_registers state after ->
  CompletedCallerEvents.flag_pend_selected_caller_save_output environment critical local active sg
    (FlagPendTaskCaller call) call mask state before final_registers.(kernel_save_r0) after.
Proof.
  intros; exists (FlagPendTaskCaller call), call, state, local.
  eapply flag_pend_task_uninterrupted_save_event; eassumption.
Qed.

Lemma flag_pend_task_uninterrupted_restore_output :
  forall environment critical local active sg call saved acquired state arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor before written middle final_cursor after,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller call) call saved acquired state before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  CompletedCallerEvents.flag_pend_selected_caller_restore_output environment critical local active sg
    (FlagPendTaskCaller call) call saved acquired state before after.
Proof.
  intros; exists (FlagPendTaskCaller call), call, state, local.
  eapply flag_pend_task_uninterrupted_restore_event; eassumption.
Qed.

End CompletedUninterruptedCallerEvents.

Module CompletedViewCallerEvents.
Import PrimitiveComponent ModuleCompletionSource.

(** Consume the original view primitive completion.  The caller constructor,
    key, task-call parameter, local owners and both heaps are unchanged. *)
Lemma flag_pend_view_save_event_from_primitive_post :
  forall environment critical local next_local active sg view key call mask saved
    before first_heap returned acquired last_heap,
  ViewPrimitiveComponent.flag_pend_view_save_primitive_post environment critical local next_local active sg
    view key call mask saved before first_heap returned acquired last_heap ->
  CompletedCallerEvents.flag_pend_selected_caller_save_event environment critical local active sg
    (FlagPendInterruptCaller view key) call mask saved before
    (FlagPendInterruptCaller returned key) call acquired next_local first_heap last_heap.
Proof.
  intros environment critical local next_local active sg view key call mask saved
    before first_heap returned acquired last_heap Hactual.
  destruct (proj1 (ViewPrimitiveComponent.flag_pend_view_save_primitive_post_old_prefix
    environment critical local next_local active sg view key call mask saved
    before first_heap returned acquired last_heap) Hactual) as [Hobs [Hsaved [Hinput Houtput]]].
  assert (Hsource : ModuleCompletionSource.flag_pend_selected_event_source environment critical sg
    (ViewPrimitiveComponent.flag_pend_view_save_completed_c_event environment critical local next_local active sg
      view key call mask saved before first_heap returned acquired last_heap)).
  { apply FlagPendModuleView.
    apply ViewPrimitiveComponent.FlagPendViewPrimitiveSave; exact Hactual. }
  unfold CompletedCallerEvents.flag_pend_selected_caller_save_event.
  refine (conj Hobs (conj Hsaved (conj Hinput (conj Houtput _)))).
  eapply (CompletedCallerSource.flag_pend_completed_source_from_module environment critical sg _ _ Hsource).
  intros h Howned; exact Howned.
Qed.

Lemma flag_pend_view_restore_event_from_primitive_post :
  forall environment critical local next_local active sg view key call saved acquired
    released first_heap returned current last_heap,
  ViewPrimitiveComponent.flag_pend_view_restore_primitive_post environment critical local next_local active sg
    view key call saved acquired released first_heap returned current last_heap ->
  CompletedCallerEvents.flag_pend_selected_caller_restore_event environment critical local active sg
    (FlagPendInterruptCaller view key) call saved acquired released
    (FlagPendInterruptCaller returned key) call current next_local first_heap last_heap.
Proof.
  intros environment critical local next_local active sg view key call saved acquired
    released first_heap returned current last_heap Hactual.
  destruct (proj1 (ViewPrimitiveComponent.flag_pend_view_restore_primitive_post_old_prefix
    environment critical local next_local active sg view key call saved acquired
    released first_heap returned current last_heap) Hactual) as [Hobs [Hinput Houtput]].
  assert (Hsource : ModuleCompletionSource.flag_pend_selected_event_source environment critical sg
    (ViewPrimitiveComponent.flag_pend_view_restore_completed_c_event environment critical local next_local active sg
      view key call saved acquired released first_heap returned current last_heap)).
  { apply FlagPendModuleView.
    apply ViewPrimitiveComponent.FlagPendViewPrimitiveRestore; exact Hactual. }
  unfold CompletedCallerEvents.flag_pend_selected_caller_restore_event.
  refine (conj Hobs (conj Hinput (conj Houtput _))).
  eapply (CompletedCallerSource.flag_pend_completed_source_from_module environment critical sg _ _ Hsource).
  intros h Howned; exact Howned.
Qed.

Lemma flag_pend_view_save_output_from_primitive_post :
  forall environment critical local next_local active sg view key call mask saved
    before first_heap returned acquired last_heap,
  ViewPrimitiveComponent.flag_pend_view_save_primitive_post environment critical local next_local active sg
    view key call mask saved before first_heap returned acquired last_heap ->
  CompletedCallerEvents.flag_pend_selected_caller_save_output environment critical local active sg
    (FlagPendInterruptCaller view key) call mask before first_heap saved last_heap.
Proof.
  intros environment critical local next_local active sg view key call mask saved
    before first_heap returned acquired last_heap Hactual.
  exists (FlagPendInterruptCaller returned key), call, acquired, next_local.
  apply flag_pend_view_save_event_from_primitive_post; exact Hactual.
Qed.

Lemma flag_pend_view_restore_output_from_primitive_post :
  forall environment critical local next_local active sg view key call saved acquired
    released first_heap returned current last_heap,
  ViewPrimitiveComponent.flag_pend_view_restore_primitive_post environment critical local next_local active sg
    view key call saved acquired released first_heap returned current last_heap ->
  CompletedCallerEvents.flag_pend_selected_caller_restore_output environment critical local active sg
    (FlagPendInterruptCaller view key) call saved acquired released first_heap last_heap.
Proof.
  intros environment critical local next_local active sg view key call saved acquired
    released first_heap returned current last_heap Hactual.
  exists (FlagPendInterruptCaller returned key), call, current, next_local.
  apply flag_pend_view_restore_event_from_primitive_post; exact Hactual.
Qed.

End CompletedViewCallerEvents.

Local Open Scope sac_scope.

Module CompletedBootCallerEvents.
Import PrimitiveComponent FlagPendBootPrimitive ContinuationPhaseEffects.
Import CompletedCallerSource CompletedCallerEvents.

Lemma flag_pend_boot_save_event_from_completion :
  forall environment critical local next_local sg original mask saved before first_heap returned current last_heap,
  flag_pend_boot_save_completion environment critical local next_local sg
    original mask saved before first_heap returned current last_heap ->
  flag_pend_selected_caller_save_event environment critical local (fun _ _ => emp) sg
    (FlagPendTaskCaller original) original mask saved before
    (FlagPendTaskCaller returned) returned current next_local first_heap last_heap.
Proof.
  intros until last_heap; intro Hactual.
  destruct (flag_pend_boot_save_completion_post _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual)
    as [Hboot [Hsame [Hnormal [Hinterval [Hsaved [Hinput Houtput]]]]]].
  unfold flag_pend_selected_caller_save_event.
  refine (conj _ (conj Hsaved (conj Hinput (conj Houtput _)))).
  - cbn [flag_pend_caller_save_observation].
    refine (conj eq_refl (conj eq_refl (conj _ (conj Hsame _)))).
    + eapply flag_pend_boot_save_completion_implies_phase; exact Hactual.
    + intros [Horigin _]; rewrite Hboot in Horigin; discriminate.
  - change (CompletedCallerSource.flag_pend_selected_event_source environment critical sg
      (CompletedCallerSource.flag_pend_task_save_completed_c_event environment critical local next_local
        (fun _ _ => emp) sg original mask saved before first_heap returned current last_heap)).
    apply FlagPendCompletedBootSave; exact Hactual.
Qed.

Lemma flag_pend_boot_restore_event_from_completion :
  forall environment critical local next_local sg original saved acquired before first_heap returned current last_heap,
  flag_pend_boot_restore_completion environment critical local next_local sg
    original saved acquired before first_heap returned current last_heap ->
  flag_pend_selected_caller_restore_event environment critical local (fun _ _ => emp) sg
    (FlagPendTaskCaller original) original saved acquired before
    (FlagPendTaskCaller returned) returned current next_local first_heap last_heap.
Proof.
  intros until last_heap; intro Hactual.
  destruct (flag_pend_boot_restore_completion_post _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual)
    as [Hboot [Hsame [Hnormal [Hinterval [Hcall [Hinput Houtput]]]]]].
  unfold flag_pend_selected_caller_restore_event.
  refine (conj _ (conj Hinput (conj Houtput _))).
  - cbn [flag_pend_caller_restore_observation].
    refine (conj eq_refl (conj eq_refl (conj _ (conj Hsame (conj (fun _ => Hcall) _))))).
    + eapply flag_pend_boot_restore_completion_implies_phase; exact Hactual.
    + intros _ [Horigin _]; rewrite Hboot in Horigin; discriminate.
  - change (CompletedCallerSource.flag_pend_selected_event_source environment critical sg
      (CompletedCallerSource.flag_pend_task_restore_completed_c_event environment critical local next_local
        (fun _ _ => emp) sg original saved acquired before first_heap returned current last_heap)).
    apply FlagPendCompletedBootRestore; exact Hactual.
Qed.

Lemma flag_pend_boot_save_output_from_completion :
  forall environment critical local next_local sg original mask saved before first_heap returned current last_heap,
  flag_pend_boot_save_completion environment critical local next_local sg
    original mask saved before first_heap returned current last_heap ->
  flag_pend_selected_caller_save_output environment critical local (fun _ _ => emp) sg
    (FlagPendTaskCaller original) original mask before first_heap saved last_heap.
Proof.
  intros; exists (FlagPendTaskCaller returned), returned, current, next_local.
  eapply flag_pend_boot_save_event_from_completion; eassumption.
Qed.

Lemma flag_pend_boot_restore_output_from_completion :
  forall environment critical local next_local sg original saved acquired before first_heap returned current last_heap,
  flag_pend_boot_restore_completion environment critical local next_local sg
    original saved acquired before first_heap returned current last_heap ->
  flag_pend_selected_caller_restore_output environment critical local (fun _ _ => emp) sg
    (FlagPendTaskCaller original) original saved acquired before first_heap last_heap.
Proof.
  intros; exists (FlagPendTaskCaller returned), returned, current, next_local.
  eapply flag_pend_boot_restore_event_from_completion; eassumption.
Qed.
End CompletedBootCallerEvents.

Local Open Scope sac_scope.

Module CompletedCallerOpen.
Import PrimitiveComponent CompletedCallerEvents.

Lemma flag_pend_selected_caller_save_output_open :
  forall environment critical local active sg caller original mask before before_heap saved,
  flag_pend_selected_caller_save_output environment critical local active sg caller original mask before before_heap saved |--
  EX returned_caller returned acquired next_local,
    coq_prop (CompletedCallerEvents.flag_pend_caller_save_observation environment critical sg
      caller original returned_caller returned mask saved before acquired /\ interrupt_saved_value mask saved /\
      flag_pend_call_protocol.flag_pend_call_endpoint_observations environment sg caller original before returned acquired) &&
    flag_pend_caller_restore_input environment critical next_local active sg
      returned_caller returned saved acquired acquired.
Proof.
  intros environment critical local active sg caller original mask before before_heap saved heap
    [returned_caller [returned [acquired [next_local [Hobs [Hsaved [Hin [Hout Hsource]]]]]]]].
  destruct (CompletedCallerSource.flag_pend_selected_completed_source_endpoints
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsource) as [Hendpoint _].
  exists returned_caller, returned, acquired, next_local; split; [|exact Hout].
  exact (conj Hobs (conj Hsaved Hendpoint)).
Qed.

Lemma flag_pend_selected_caller_restore_output_open :
  forall environment critical local active sg caller original saved acquired released before_heap,
  flag_pend_selected_caller_restore_output environment critical local active sg caller original saved acquired released before_heap |--
  EX returned_caller returned current next_local,
    coq_prop (CompletedCallerEvents.flag_pend_caller_restore_observation environment critical sg
      caller original returned_caller returned released current /\
      flag_pend_call_protocol.flag_pend_call_endpoint_observations environment sg caller original released returned current) &&
    flag_pend_caller_save_input environment critical next_local active sg
      returned_caller returned (armv7a_irq_fiq_mask saved) current.
Proof.
  intros environment critical local active sg caller original saved acquired released before_heap heap
    [returned_caller [returned [current [next_local [Hobs [Hin [Hout Hsource]]]]]]].
  destruct (CompletedCallerSource.flag_pend_selected_completed_source_endpoints
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsource) as [Hendpoint _].
  exists returned_caller, returned, current, next_local; split; [|exact Hout].
  exact (conj Hobs Hendpoint).
Qed.

End CompletedCallerOpen.

Module SelectedCallerPhaseComponent.
Include CompletedCallerEvents.
Include CompletedCallerOpen.
Definition flag_pend_selected_task_uninterrupted_save_event :=
  CompletedUninterruptedCallerEvents.flag_pend_task_uninterrupted_save_event.
Definition flag_pend_selected_task_uninterrupted_restore_event :=
  CompletedUninterruptedCallerEvents.flag_pend_task_uninterrupted_restore_event.
Definition flag_pend_selected_task_uninterrupted_save_output :=
  CompletedUninterruptedCallerEvents.flag_pend_task_uninterrupted_save_output.
Definition flag_pend_selected_task_uninterrupted_restore_output :=
  CompletedUninterruptedCallerEvents.flag_pend_task_uninterrupted_restore_output.
Definition flag_pend_selected_view_save_event_from_primitive_post :=
  CompletedViewCallerEvents.flag_pend_view_save_event_from_primitive_post.
Definition flag_pend_selected_view_restore_event_from_primitive_post :=
  CompletedViewCallerEvents.flag_pend_view_restore_event_from_primitive_post.
Definition flag_pend_selected_view_save_output_from_primitive_post :=
  CompletedViewCallerEvents.flag_pend_view_save_output_from_primitive_post.
Definition flag_pend_selected_view_restore_output_from_primitive_post :=
  CompletedViewCallerEvents.flag_pend_view_restore_output_from_primitive_post.
End SelectedCallerPhaseComponent.

Definition flag_pend_selected_owned_input environment critical boundary local sg caller call mask
  i pgrp requested mode delay perr before
  (X : Z -> Z -> UCOS2_Verify_State -> Prop) (frame : Assertion) : Assertion :=
  PendPhaseCandidate.flag_pend_owned_input environment critical boundary local sg
    (SelectedEventSources.flag_pend_selected_linked_sources environment critical sg) caller call mask
    i pgrp requested mode delay perr before X frame.
