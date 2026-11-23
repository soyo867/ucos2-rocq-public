Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_retirement_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_sched_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_acquired_fields_prefix_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_wrapper_completion_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations KernelHeapObservation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module OSIntExitReturnedC.
Import CriticalComponent PrimitiveComponent IRQAcquiredCPrefix
  SelectedIRQWrapperCompletion SelectedIRQWrapperSegment SelectedRetirementTransport.

(** The three branches are the real post-counter C tests: nested, locked,
    or equal priorities after the two selector stores.  Determinism binds
    the existing resource producer to this very physical execution. *)
Lemma os_sched_nonswitch_prefix_execution_deterministic : forall sg before first second,
  os_sched_source_nonswitch_prefix_execution sg before first ->
  os_sched_source_nonswitch_prefix_execution sg before second -> first = second.
Proof.
  intros sg before first second Hfirst Hsecond.
  destruct Hfirst as [[n [Hn [Hn0 Hrun]]] |
    [[Hn [l [Hl [Hl0 Hrun]]]] | [Hn [Hl [Hrun Hp]]]]];
  destruct Hsecond as [[n' [Hn' [Hn0' Hrun']]] |
    [[Hn' [l' [Hl' [Hl0' Hrun']]]] | [Hn' [Hl' [Hrun' Hp']]]]].
  - eapply kernel_heap_execution_deterministic; eassumption.
  - exfalso; apply Hn0; eapply uchar_load_deterministic; eassumption.
  - exfalso; apply Hn0; eapply uchar_load_deterministic; eassumption.
  - exfalso; apply Hn0'; eapply uchar_load_deterministic; eassumption.
  - eapply kernel_heap_execution_deterministic; eassumption.
  - exfalso; apply Hl0; eapply uchar_load_deterministic; eassumption.
  - exfalso; apply Hn0'; eapply uchar_load_deterministic; eassumption.
  - exfalso; apply Hl0'; eapply uchar_load_deterministic; eassumption.
  - eapply os_int_exit_selection_heap_fragment_deterministic; eassumption.
Qed.

(** The inactive branch performs neither acquire nor counter/selector writes.
    The running branch starts at the actual acquired cut.  OSRunning was
    read earlier; it is deliberately not read again at [before]. *)
Inductive os_int_exit_returned_c_prefix (sg : StableGlobVars) :
  bool -> UCOS2_Verify_State -> model -> model -> Prop :=
| OSIntExitReturnedInactive : forall entry before,
  os_int_exit_returned_c_prefix sg false entry before before
| OSIntExitReturnedRunning : forall entry before counted middle,
  os_int_exit_acquired_counter_execution sg entry before counted ->
  os_sched_source_nonswitch_prefix_execution sg counted middle ->
  os_int_exit_returned_c_prefix sg true entry before middle.

Lemma os_int_exit_returned_c_prefix_resources :
  forall sg observed entry frame before middle,
  os_int_exit_returned_c_prefix sg observed entry before middle ->
  os_int_exit_requests_switch observed entry = false ->
  (observed = true -> os_sched_selection_enabled (os_int_exit_after_nesting entry) = true ->
    entry.(SchedState).(readyList) <> []) ->
  (UCOS2_fields_inv sg entry ** unmap_table_rep sg ** frame) before ->
  (UCOS2_fields_inv sg (os_int_exit_ready_checkpoint observed entry) **
    unmap_table_rep sg ** frame) middle.
Proof.
  intros sg observed entry frame before middle Hprefix Hnoswitch Hnonempty Hinput.
  destruct Hprefix as [entry before | entry before counted middle Hcounter Hselect].
  - exact Hinput.
  - assert (Hassociate : UCOS2_fields_inv sg entry ** unmap_table_rep sg ** frame |--
      UCOS2_fields_inv sg entry ** (unmap_table_rep sg ** frame)) by entailer!.
    pose proof (os_int_exit_acquired_counter_fields_frame_preservation sg entry
      (unmap_table_rep sg ** frame) before counted (Hassociate before Hinput) Hcounter) as Hcounted0.
    assert (Hassociate_back :
      UCOS2_fields_inv sg (os_int_exit_counter_state true entry) ** (unmap_table_rep sg ** frame) |--
      UCOS2_fields_inv sg (os_int_exit_counter_state true entry) ** unmap_table_rep sg ** frame)
      by entailer!.
    pose proof (Hassociate_back counted Hcounted0) as Hcounted.
    change (os_sched_requests_switch (os_int_exit_counter_state true entry) = false) in Hnoswitch.
    destruct (os_sched_fields_nonswitch_prefix_resources sg (os_int_exit_counter_state true entry)
      frame counted Hnoswitch (Hnonempty eq_refl) Hcounted)
      as [actual_middle [Hactual Hpost]].
    assert (Hmiddle : actual_middle = middle)
      by (eapply os_sched_nonswitch_prefix_execution_deterministic; eassumption).
    subst actual_middle; exact Hpost.
Qed.

Definition os_int_exit_returned_c_input environment sg entry local suspended receipt handler
  (frame : Assertion) : Assertion :=
  UCOS2_fields_inv sg entry ** unmap_table_rep sg **
  (store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations)
      entry.(TskState) (kernel_irq_fields_local local suspended receipt))
    entry.(TskState).(parkedTaskStacks) **
   (interrupt_platform_running environment.(task_stack_call_platform)
      handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources environment.(task_stack_call_port) handler ** frame)).

(** This source packet starts at acquired [entry,before].  It retains the
    original earlier observation and FullCall Returned proof.  The caller
    composes its actual acquire prefix at that same [entry,before]; this
    packet does not invent a read_heap-to-before physical execution. *)
Record os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
  entry local suspended receipt original node handler frame before middle after : Prop := {
  os_int_exit_returned_observed_owner :
    (UCOS2_fields_inv sg observed ** observation_frame) read_heap;
  os_int_exit_returned_observed_read :
    uchar_load sg.(g_OSRunning) (if observed.(SchedState).(isRunning) then 1 else 0) read_heap;
  os_int_exit_returned_full_call :
    os_int_exit_full_call environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical sg handler observed (OsIntExitReturned entry);
  os_int_exit_returned_prefix :
    os_int_exit_returned_c_prefix sg observed.(SchedState).(isRunning) entry before middle;
  os_int_exit_returned_selection_nonempty :
    observed.(SchedState).(isRunning) = true ->
    os_sched_selection_enabled (os_int_exit_after_nesting entry) = true ->
    entry.(SchedState).(readyList) <> [];
  os_int_exit_returned_before_owned :
    os_int_exit_returned_c_input environment sg entry local suspended receipt handler frame before;
  os_int_exit_returned_binding : armv7a_continuation_binding suspended;
  os_int_exit_returned_saved_call : suspended.(armv7a_continuation_call) = Some original;
  os_int_exit_returned_current :
    entry.(SchedState).(curTaskID) = Some suspended.(armv7a_continuation_stack).(stackLeaseSlot);
  os_int_exit_returned_node :
    entry.(TskState).(inUsedTaskStates) suspended.(armv7a_continuation_stack).(stackLeaseSlot) = Some node;
  os_int_exit_returned_generation :
    node.(taskGeneration) = suspended.(armv7a_continuation_stack).(stackLeaseGeneration);
  os_int_exit_returned_parked :
    entry.(TskState).(parkedTaskStacks) (task_stack_key suspended.(armv7a_continuation_stack)) =
      Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments));
  os_int_exit_returned_stack_address :
    tcb_field_address (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) TCBStkPtr =
      task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot);
  os_int_exit_returned_coverage : task_stack_live_coverage entry.(TskState) None;
  os_int_exit_returned_restore :
    armv7a_restore_transition environment.(task_stack_call_continuations) handler suspended middle after
}.

Lemma os_int_exit_returned_c_completion_wrapper :
  forall environment critical sg observed read_heap observation_frame entry local suspended receipt
    original node handler frame before middle after,
  os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
    entry local suspended receipt original node handler frame before middle after ->
  irq_wrapper_c_completion environment sg
    (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
    local suspended receipt original node handler (unmap_table_rep sg ** frame) middle after.
Proof.
  intros until after; intro Hcompletion.
  destruct Hcompletion as [Hobserved Hread Hreturned Hprefix Hnonempty Hinput Hbinding Hcall
    Hcurrent Hnode Hgeneration Hparked Haddress Hcoverage Hrestore].
  change (os_int_exit_return_relation critical sg handler observed entry) in Hreturned.
  destruct Hreturned as [Hacquire Hnoswitch].
  pose proof (os_int_exit_returned_c_prefix_resources sg observed.(SchedState).(isRunning) entry
    _ before middle Hprefix Hnoswitch Hnonempty Hinput) as Hmiddle.
  assert (Htasks := proj1 (os_int_exit_checkpoint_frame observed.(SchedState).(isRunning) entry)).
  assert (Hcur := proj1 (os_int_exit_checkpoint_current_frame observed.(SchedState).(isRunning) entry)).
  constructor; try assumption.
  - rewrite Hcur; exact Hcurrent.
  - rewrite Htasks; exact Hnode.
  - rewrite Htasks; exact Hparked.
  - rewrite Htasks; exact Hcoverage.
  - unfold irq_wrapper_c_input; rewrite Htasks.
    match type of Hmiddle with ?P middle => assert (Hreorder : P |--
      UCOS2_fields_inv sg (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry) **
      store_parked_continuations
        (kernel_saved_continuation_entry environment.(task_stack_call_continuations)
          entry.(TskState) (kernel_irq_fields_local local suspended receipt))
        entry.(TskState).(parkedTaskStacks) **
      (interrupt_platform_running environment.(task_stack_call_platform)
        handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
        os_int_exit_context_resources environment.(task_stack_call_port) handler **
        (unmap_table_rep sg ** frame))) end.
    { entailer!. }
    exact (Hreorder middle Hmiddle).
Qed.

Lemma os_int_exit_returned_c_completion_resources :
  forall environment critical sg observed read_heap observation_frame entry local suspended receipt
    original node handler frame before middle after,
  os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
    entry local suspended receipt original node handler frame before middle after ->
  os_int_exit_returned_c_input environment sg entry local suspended receipt handler frame before /\
  irq_wrapper_c_output environment sg
    (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
    local suspended receipt original handler (unmap_table_rep sg ** frame) after.
Proof.
  intros until after; intro Hcompletion; split.
  - exact (os_int_exit_returned_before_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcompletion).
  - eapply (proj2 (irq_wrapper_c_completion_resources _ _ _ _ _ _ _ _ _ _ _ _
      (os_int_exit_returned_c_completion_wrapper _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcompletion))).
Qed.

Inductive os_int_exit_returned_c_step environment critical sg : KernelCSegmentRelation :=
| OSIntExitReturnedCStep : forall observed read_heap observation_frame entry local suspended receipt
    original node handler frame before middle after,
  os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
    entry local suspended receipt original node handler frame before middle after ->
  os_int_exit_returned_c_step environment critical sg entry before
    (os_int_exit_returned_c_input environment sg entry local suspended receipt handler frame)
    false
    (os_int_exit_wrapper_restored_state
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
      suspended.(armv7a_continuation_stack)) after
    (irq_wrapper_c_output environment sg
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
      local suspended receipt original handler (unmap_table_rep sg ** frame)).

Lemma os_int_exit_returned_c_step_resources :
  forall environment critical sg entry before input stopped current after output,
  os_int_exit_returned_c_step environment critical sg entry before input stopped current after output ->
  input before /\ output after.
Proof.
  intros until output; intro Hstep; destruct Hstep.
  eapply os_int_exit_returned_c_completion_resources; exact H.
Qed.

Lemma os_int_exit_returned_c_step_preserves_observer :
  forall environment critical sg entry before input stopped current after output,
  os_int_exit_returned_c_step environment critical sg entry before input stopped current after output ->
  forall observer origin,
  task_invocation_active entry.(TskState) observer origin /\ sched_observer_current_cache origin entry ->
  task_invocation_active current.(TskState) observer origin /\ sched_observer_current_cache origin current.
Proof.
  intros until output; intro Hstep; destruct Hstep; intros observer origin [Hactive Hcache].
  pose proof (proj1 (os_int_exit_checkpoint_frame observed.(SchedState).(isRunning) entry)) as Htasks.
  split.
  - cbn [os_int_exit_wrapper_restored_state replace_TskS TskState]; rewrite Htasks; exact Hactive.
  - destruct origin as [|slot generation]; [exact I|].
    destruct (os_int_exit_checkpoint_current_frame observed.(SchedState).(isRunning) entry)
      as [Hcurrent [Hpriority Hrunning]].
    change (forall task,
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry).(TskState).(inUsedTaskStates) slot = Some task ->
      task.(taskGeneration) = generation ->
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry).(SchedState).(curTaskID) = Some slot ->
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry).(SchedState).(curSchedPrio) = Some task.(curPrio)).
    rewrite Htasks, Hcurrent, Hpriority; exact Hcache.
Qed.

Lemma os_int_exit_returned_c_step_lifetime :
  forall environment critical sg entry before input stopped current after output,
  os_int_exit_returned_c_step environment critical sg entry before input stopped current after output ->
  forall observer origin,
  task_observer_lifetime_result observer origin entry.(TskState) current.(TskState) stopped.
Proof.
  intros until output; intro Hstep; destruct Hstep; intros observer origin.
  destruct observed.(SchedState).(isRunning);
  apply task_observer_lifetime_result_not_stopped, task_observer_lifetime_transport_fields;
    reflexivity.
Qed.

Lemma os_int_exit_returned_c_step_source_frames :
  forall environment critical sg entry before input stopped current after output,
  os_int_exit_returned_c_step environment critical sg entry before input stopped current after output ->
  forall task_observer event_observer,
  task_creation_frame task_observer entry.(TskState) current.(TskState) /\
  event_creation_frame event_observer entry.(EventState) current.(EventState) /\
  entry.(NameState) = current.(NameState) /\ entry.(TimerState) = current.(TimerState).
Proof.
  intros until output; intro Hstep; destruct Hstep; intros task_observer event_observer.
  destruct observed.(SchedState).(isRunning); repeat split; reflexivity.
Qed.

Lemma os_int_exit_returned_c_step_running :
  forall environment critical sg entry before input stopped current after output,
  os_int_exit_returned_c_step environment critical sg entry before input stopped current after output ->
  current.(SchedState).(isRunning) = entry.(SchedState).(isRunning).
Proof.
  intros until output; intro Hstep; destruct Hstep.
  exact (proj2 (proj2 (os_int_exit_checkpoint_current_frame observed.(SchedState).(isRunning) entry))).
Qed.

Lemma os_int_exit_returned_c_step_idle_non_idle :
  forall environment critical sg observed entry before input stopped current after output,
  os_int_exit_returned_c_step environment critical sg entry before input stopped current after output ->
  (task_idle_ready sg entry.(TskState) -> task_idle_ready sg current.(TskState)) /\
  (flag_pend_non_idle_at sg observed entry -> flag_pend_non_idle_at sg observed current).
Proof.
  intros until output; intro Hstep.
  destruct Hstep as [observation read_heap observation_frame entry local suspended receipt
    original node handler frame before middle after Hcompletion].
  destruct observation.(SchedState).(isRunning); split; intro Hfact; exact Hfact.
Qed.

Lemma os_int_exit_returned_c_step_profile_counter :
  forall environment critical sg entry before input stopped current after output,
  os_int_exit_returned_c_step environment critical sg entry before input stopped current after output ->
  current.(SchedState).(ctxSwCtr) = entry.(SchedState).(ctxSwCtr).
Proof.
  intros until output; intro Hstep; destruct Hstep.
  pose proof (os_int_exit_returned_full_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as Hreturned.
  change (os_int_exit_return_relation critical sg handler observed entry) in Hreturned.
  destruct Hreturned as [_ Hnoswitch].
  change ((os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry).(SchedState).(ctxSwCtr) =
    entry.(SchedState).(ctxSwCtr)).
  rewrite os_int_exit_checkpoint_counter_eq, Hnoswitch; reflexivity.
Qed.

Lemma os_int_exit_returned_c_completion_intr_state :
  forall environment critical sg observed read_heap observation_frame entry local suspended receipt
    original node handler frame before middle after,
  os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
    entry local suspended receipt original node handler frame before middle after ->
  (os_int_exit_wrapper_restored_state
    (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
    suspended.(armv7a_continuation_stack)).(IntrState) =
  interrupt_exit_state observed.(SchedState).(isRunning) entry.(IntrState).
Proof.
  intros until after; intro Hcompletion.
  exact (os_int_exit_checkpoint_nesting_eq observed.(SchedState).(isRunning) entry).
Qed.

Lemma os_int_exit_returned_c_step_lock_nesting :
  forall environment critical sg entry before input stopped current after output,
  os_int_exit_returned_c_step environment critical sg entry before input stopped current after output ->
  current.(IntrState).(lockNesting) = entry.(IntrState).(lockNesting).
Proof.
  intros until output; intro Hstep; destruct Hstep.
  change ((os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry).(IntrState).(lockNesting) =
    entry.(IntrState).(lockNesting)).
  rewrite os_int_exit_checkpoint_nesting_eq.
  unfold interrupt_exit_state.
  destruct observed.(SchedState).(isRunning); [destruct (0 <? entry.(IntrState).(intNesting))|]; reflexivity.
Qed.

Lemma os_int_exit_returned_c_step_task_fields :
  forall environment critical sg entry before input stopped current after output,
  os_int_exit_returned_c_step environment critical sg entry before input stopped current after output ->
  current.(TskState).(inUsedTaskStates) = entry.(TskState).(inUsedTaskStates) /\
  current.(TskState).(taskLifecycle) = entry.(TskState).(taskLifecycle) /\
  current.(SchedState).(curTaskID) = entry.(SchedState).(curTaskID) /\
  current.(SchedState).(curSchedPrio) = entry.(SchedState).(curSchedPrio).
Proof.
  intros until output; intro Hstep; destruct Hstep.
  destruct (os_int_exit_checkpoint_current_frame observed.(SchedState).(isRunning) entry)
    as [Hcurrent [Hpriority Hrunning]].
  split.
  - destruct observed.(SchedState).(isRunning); reflexivity.
  - split.
    + destruct observed.(SchedState).(isRunning); reflexivity.
    + split; assumption.
Qed.

End OSIntExitReturnedC.
