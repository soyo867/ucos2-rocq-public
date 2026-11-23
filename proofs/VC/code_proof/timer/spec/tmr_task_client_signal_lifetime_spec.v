Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_pool Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.mutex_query_spec Ucos2Verify.lib.sem Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_context Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.queue_core Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_handle_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_protocol_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_call_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_delete_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_legacy_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_delete_source_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_c_segment_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_c_segment_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_c_segment_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_api_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_masked_c_step_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_c_segment_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_c_segment_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_acquire_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_irq_completion_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_irq_entry_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_program_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_acquire_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_checkpoint_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_program_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_fields_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_delete_call_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_delete_return_source_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations DeleteComponent.
Import SchedulerPhaseCandidate SelectedCProgram SelectedCSource.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A relation on two actual states. The additional public-slot facts are
    current pool projections, allowing composition without an invariant
    premise at every intermediate source cut. *)
Definition tmr_task_signal_public_slots_preserved (before after : UCOS2_Verify_State) : Prop :=
  forall eid generation, tmr_task_signal_public_slot before.(EventState) eid generation ->
    tmr_task_signal_public_slot after.(EventState) eid generation.

Lemma tmr_task_signal_public_slots_refl : forall state,
  tmr_task_signal_public_slots_preserved state state.
Proof. intros state eid generation Hslot; exact Hslot. Qed.

Lemma tmr_task_signal_public_slots_trans : forall before middle after,
  tmr_task_signal_public_slots_preserved before middle ->
  tmr_task_signal_public_slots_preserved middle after ->
  tmr_task_signal_public_slots_preserved before after.
Proof. intros before middle after Hfirst Hlast eid generation Hslot; apply Hlast, Hfirst, Hslot. Qed.

Lemma tmr_task_signal_public_slots_event_eq : forall before after,
  after.(EventState) = before.(EventState) -> tmr_task_signal_public_slots_preserved before after.
Proof. intros before after Heq eid generation Hslot; rewrite Heq; exact Hslot. Qed.

Lemma tmr_task_live_sem_public_slots_from_returned_pool : forall sg before after,
  tmr_task_live_sem_identity before after -> event_pool_partition sg after.(EventState) ->
  tmr_task_signal_public_slots_preserved before after.
Proof.
  intros sg before after Hidentity Hpool eid generation [previous [Hlookup [Hgen [Hsem Hrest]]]].
  destruct (Hidentity eid previous Hlookup Hsem) as [current [Hcurrent [Hgeneration Htype]]].
  assert (Hslot := tmr_task_signal_public_slot_from_pool sg after.(EventState) eid current
    Hpool Hcurrent ltac:(congruence)).
  rewrite Hgeneration, Hgen in Hslot; exact Hslot.
Qed.

Lemma tmr_task_wake_c_source_preserves_public_slots : forall sg before after,
  WakeComponent.kernel_wake_c_source sg before after -> tmr_task_signal_public_slots_preserved before after.
Proof.
  intros sg before after Hsource; destruct Hsource; intros observed generation Hslot.
  - destruct (flag_task_rdy_result _ _ _ _ _ _ _ H)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]]; exact Hslot.
  - eapply tmr_task_signal_public_slot_event_ready; eassumption.
  - unfold tick_task_step; repeat match goal with |- context [if ?test then _ else _] => destruct test end; exact Hslot.
Qed.

Lemma tmr_task_status_c_source_preserves_public_slots : forall sg before after,
  StatusComponent.kernel_status_c_source sg before after -> tmr_task_signal_public_slots_preserved before after.
Proof.
  intros sg before after Hsource; destruct Hsource; intros observed generation Hslot.
  - destruct H as [cid [current [_ [_ [_ Hstep]]]]].
    destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg priority current)));
      [destruct Hstep as [_ ->]|destruct Hstep as [_ ->]|destruct Hstep as [old [_ [_ ->]]]]; exact Hslot.
  - destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority).
    + destruct Hstep as [_ ->]; exact Hslot.
    + destruct Hstep as [_ ->]; exact Hslot.
    + destruct Hstep as [old [_ Hstep]]; destruct (task_is_suspended old.(stat)).
      * destruct Hstep as [_ ->]; unfold task_resume_state, sched_resume_task, sched_wake_by_status;
          repeat match goal with |- context [if ?test then _ else _] => destruct test end; exact Hslot.
      * destruct Hstep as [_ ->]; exact Hslot.
  - destruct H as [event [fields [Hselected [_ [_ ->]]]]].
    destruct (Z.ltb 0 fields.(semCount)); [|exact Hslot].
    eapply tmr_task_signal_public_slot_count; eassumption.
Qed.

Lemma tmr_task_event_creation_c_segment_preserves_public_slots : forall sg before heap input after heap' output,
  EventCreationComponent.kernel_event_creation_c_segment sg before heap input after heap' output ->
  tmr_task_signal_public_slots_preserved before after.
Proof.
  intros sg before heap input after heap' output Hsegment.
  pose proof (EventCreationComponent.kernel_event_creation_c_segment_source
    _ _ _ _ _ _ _ Hsegment) as Hsource.
  destruct Hsource; intros observed generation Hslot.
  - unfold event_create_allocate_critical in H.
    destruct entry.(EventState).(unUsedEventStates) as [|selected rest] eqn:Hfree.
    + destruct H as [_ ->]; exact Hslot.
    + destruct H as [image [_ [_ ->]]]. eapply tmr_task_signal_public_slot_detach; eassumption.
  - eapply tmr_task_signal_public_slot_private_write; eassumption.
  - eapply tmr_task_signal_public_slot_publish; eassumption.
Qed.

Lemma tmr_task_queue_creation_c_segment_preserves_public_slots : forall sg before heap input after heap' output,
  QueueCreationComponent.kernel_queue_creation_c_segment sg before heap input after heap' output ->
  tmr_task_signal_public_slots_preserved before after.
Proof.
  intros sg before heap input after heap' output Hsegment.
  pose proof (tmr_task_queue_creation_segment_preserves_live_sem _ _ _ _ _ _ _ Hsegment) as Hidentity.
  apply (tmr_task_live_sem_public_slots_from_returned_pool sg before after Hidentity).
  destruct Hsegment.
  all: match goal with Houtput : ?P ?heap |- _ =>
    lazymatch P with context [UCOS2_inv ?pool_sg ?state] =>
      assert (Hopen : P |-- coq_prop (UCOS2_state_inv pool_sg state) && TT)
        by (unfold UCOS2_inv; entailer!);
      pose proof (proj1 (Hopen heap Houtput)) as Hvalid;
      exact (proj1 (proj1 (proj2 (proj2 (proj2 Hvalid))))) end end.
Qed.

Lemma tmr_task_program_named_source_preserves_public_slots :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (step : kernel_program_c_step environment critical sg observer origin state before input stopped current after output),
  kernel_program_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output step -> tmr_task_signal_public_slots_preserved state current.
Proof.
  intros environment critical sg observer origin event_observer state before input stopped current after output step Hsource.
  destruct Hsource.
  - eapply tmr_task_wake_c_source_preserves_public_slots, WakeComponent.kernel_wake_c_segment_source; exact Hsegment.
  - eapply tmr_task_status_c_source_preserves_public_slots, StatusComponent.kernel_status_c_segment_code; exact Hsegment.
  - apply tmr_task_signal_public_slots_event_eq.
    exact (proj1 (NamedSourceFrames.kernel_task_creation_c_source_other_fields _ _ _
      (CreationComponent.kernel_task_creation_c_segment_source _ _ _ _ _ _ _ Hsegment))).
  - eapply tmr_task_event_creation_c_segment_preserves_public_slots; exact Hsegment.
  - eapply tmr_task_queue_creation_c_segment_preserves_public_slots; exact Hsegment.
Qed.

Lemma tmr_task_critical_c_source_preserves_public_slots : forall sg call,
  CriticalComponent.kernel_critical_c_source sg call ->
  tmr_task_signal_public_slots_preserved (CriticalComponent.kernel_critical_c_entry call)
    (CriticalComponent.kernel_critical_c_returned call).
Proof.
  intros sg [actual|actual] Hsource; cbn in Hsource |- *; intros eid generation Hslot.
  - destruct Hsource as [error [Hcritical Hcode]].
    eapply tmr_task_change_prio_critical_preserves_signal_public_slot; eassumption.
  - unfold CriticalComponent.mutex_del_critical_fields_observation in Hsource; destruct Hsource.
    + destruct H0 as [error [scheduled [Hcritical [Hcode Hrequest]]]].
      eapply tmr_task_signal_public_slot_mutex_delete; eassumption.
    + exact Hslot.
Qed.

Lemma tmr_task_install_c_segment_preserves_public_slots :
  forall environment local sg before heap input stopped after heap' output,
  InstallComponent.task_install_c_step environment local sg before heap input stopped after heap' output ->
  tmr_task_signal_public_slots_preserved before after.
Proof.
  intros environment local sg before heap input stopped after heap' output
    [frame call before_heap after_heap sp Hactual [Hsource Hcompletion]].
  apply tmr_task_signal_public_slots_event_eq.
  exact (proj1 (proj2 (proj2 (os_sched_install_client_state_frame environment.(task_stack_call_external)
    call.(InstallComponent.task_install_fields_context) call.(InstallComponent.task_install_fields_outgoing)
    call.(InstallComponent.task_install_fields_incoming) call.(InstallComponent.task_install_fields_resumed)
    sg call.(InstallComponent.task_install_fields_entry) (InstallComponent.task_install_fields_current call) Hsource)))).
Qed.

Lemma tmr_task_delete_prepare_preserves_public_slots : forall state tid old prepared loan,
  task_delete_prepare_single_wait state tid old = Some (prepared, loan) ->
  tmr_task_signal_public_slots_preserved state prepared.
Proof.
  intros state tid old prepared loan Hstep eid generation Hslot.
  eapply tmr_task_signal_public_slot_live_frame;
    [eapply tmr_task_delete_prepare_preserves_live_sem; exact Hstep| | |exact Hslot].
  all: unfold task_delete_prepare_single_wait in Hstep;
    destruct old.(eventPtr) as [selected|];
    [destruct (state.(EventState).(inUsedEventStates) selected) as [event|]; [|discriminate]|];
    cbn [task_set_event_ptr tcbFlagNode] in Hstep;
    destruct (Z.eqb old.(tcbFlagNode) 0);
    try (destruct (flag.flag_unlink_node state.(FlagState) old.(tcbFlagNode)) as [[waiter flags]|]; [|discriminate]);
    inversion Hstep; reflexivity.
Qed.

Lemma tmr_task_delete_own_c_segment_preserves_public_slots :
  forall environment critical sg observer origin state before input stopped current after output,
  DeleteComponent.task_delete_own_c_segment environment critical sg observer origin
    state before input stopped current after output -> tmr_task_signal_public_slots_preserved state current.
Proof.
  intros environment critical sg observer origin state before input stopped current after output Hstep.
  destruct Hstep as [inputs before_heap prepared_heap Hcontext Hcompleted|capture after_heap Hcontext Hcompleted].
  - destruct Hcompleted as [[Hlive [Hprepare Hprotocol]] Hbefore Hafter].
    change (tmr_task_signal_public_slots_preserved inputs.(DeleteComponent.delete_capture_acquired)
      inputs.(DeleteComponent.delete_capture_prepared)).
    eapply tmr_task_delete_prepare_preserves_public_slots; exact Hprepare.
  - apply tmr_task_signal_public_slots_event_eq; reflexivity.
Qed.

Lemma tmr_task_delete_primitive_c_preserves_public_slots :
  forall environment critical sg state before input stopped current after output,
  DeleteComponent.task_delete_primitive_c_segment environment critical sg
    state before input stopped current after output -> tmr_task_signal_public_slots_preserved state current.
Proof. intros * Hstep; destruct Hstep; apply tmr_task_signal_public_slots_event_eq; reflexivity. Qed.

Lemma tmr_task_paired_primitive_c_preserves_public_slots :
  forall environment critical sg before heap input stopped after heap' output,
  PrimitiveComponent.flag_pend_task_primitive_c_step environment critical sg
    before heap input stopped after heap' output -> tmr_task_signal_public_slots_preserved before after.
Proof.
  intros * Hstep; destruct Hstep.
  - destruct H; apply tmr_task_signal_public_slots_event_eq; reflexivity.
  - apply tmr_task_signal_public_slots_event_eq; reflexivity.
  - apply tmr_task_signal_public_slots_event_eq; reflexivity.
Qed.

Lemma tmr_task_builtin_c_segment_preserves_public_slots :
  forall environment critical local sg state before current after input output,
  BuiltinComponent.kernel_builtin_c_segment environment critical local sg state before current after input output ->
  tmr_task_signal_public_slots_preserved state current.
Proof.
  intros * Hsegment; destruct Hsegment.
  - destruct operation; apply tmr_task_signal_public_slots_event_eq; reflexivity.
  - apply tmr_task_signal_public_slots_event_eq; reflexivity.
  - pose proof (BuiltinComponent.kernel_irq_transfer_c_completion_source environment critical sg
      handler saved entry transfer frame before after H) as Htransfer.
    destruct (BuiltinComponent.os_int_exit_configured_transfer_state_frame environment sg handler entry transfer Htransfer)
      as [Hnodes [Hlife [Hevent Hrest]]].
    apply tmr_task_signal_public_slots_event_eq; exact Hevent.
Qed.

Lemma tmr_task_program_remaining_source_preserves_public_slots :
  forall environment critical sg observer origin state before input stopped current after output
    (step : kernel_program_c_step environment critical sg observer origin state before input stopped current after output),
  kernel_program_c_step_remaining_source environment critical sg observer origin
    state before input stopped current after output step -> tmr_task_signal_public_slots_preserved state current.
Proof.
  intros * Hsource; destruct Hsource.
  - destruct Hsegment as [Hcompletion [Hphysical [Hcode Hpacket]]].
    eapply tmr_task_critical_c_source_preserves_public_slots; exact Hcode.
  - eapply tmr_task_builtin_c_segment_preserves_public_slots; exact Hsegment.
  - eapply tmr_task_install_c_segment_preserves_public_slots; exact Hsegment.
  - destruct Hsegment as [Hcode Hpre Hpost].
    apply (tmr_task_live_sem_public_slots_from_returned_pool sg _ _
      (tmr_task_mutex_inherit_source_preserves_live_sem _ _ Hcode)).
    match type of Hpost with ?P after => assert (Hopen : P |--
      coq_prop (UCOS2_state_inv sg call.(PendComponent.mutex_pend_inheritance_returned)) && TT) end.
    { unfold PendComponent.mutex_pend_inheritance_c_owner, UCOS2_inv;
        entailer!. }
    pose proof (proj1 (Hopen after Hpost)) as Hvalid.
    exact (proj1 (proj1 (proj2 (proj2 (proj2 Hvalid))))).
  - destruct Hsegment as [[Hcaller Hcode] Hpre Hpost].
    apply (tmr_task_live_sem_public_slots_from_returned_pool sg _ _
      (tmr_task_mutex_post_critical_preserves_live_sem _ _ _ _ _ _ _ Hcode)).
    match type of Hpost with ?P after => assert (Hopen : P |--
      coq_prop (UCOS2_state_inv sg call.(PostComponent.mutex_post_critical_checkpoint)) && TT) end.
    { unfold PostComponent.mutex_post_critical_c_owner, UCOS2_inv;
        entailer!. }
    pose proof (proj1 (Hopen after Hpost)) as Hvalid.
    exact (proj1 (proj1 (proj2 (proj2 (proj2 Hvalid))))).
  - eapply tmr_task_delete_primitive_c_preserves_public_slots; exact Hsegment.
  - eapply tmr_task_paired_primitive_c_preserves_public_slots; exact Hsegment.
  - eapply tmr_task_delete_own_c_segment_preserves_public_slots; exact Hsegment.
Qed.

Lemma tmr_task_program_c_step_source_preserves_public_slots :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (step : kernel_program_c_step environment critical sg observer origin state before input stopped current after output),
  kernel_program_c_step_call_source environment critical sg observer origin event_observer
    state before input stopped current after output step -> tmr_task_signal_public_slots_preserved state current.
Proof.
  intros * [Hnamed|Hremaining].
  - eapply tmr_task_program_named_source_preserves_public_slots; exact Hnamed.
  - eapply tmr_task_program_remaining_source_preserves_public_slots; exact Hremaining.
Qed.

Lemma tmr_task_program_c_sequence_source_preserves_public_slots :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_c_step environment critical sg observer origin)
      state before input stopped current after output),
  kernel_program_c_sequence_call_source environment critical sg observer origin event_observer
    state before input stopped current after output run -> tmr_task_signal_public_slots_preserved state current.
Proof.
  intros * Hsource.
  eapply (kernel_c_sequence_source_relation (kernel_program_c_step environment critical sg observer origin)
    (kernel_program_c_step_call_source environment critical sg observer origin event_observer)
    tmr_task_signal_public_slots_preserved).
  - apply tmr_task_signal_public_slots_refl.
  - apply tmr_task_signal_public_slots_trans.
  - intros; eapply tmr_task_program_c_step_source_preserves_public_slots; eassumption.
  - exact Hsource.
Qed.

Lemma tmr_task_return_c_step_source_preserves_public_slots :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (step : SelectedReturnPrimitive.kernel_program_return_c_step environment critical sg observer origin
      state before input stopped current after output),
  SelectedCompletionSource.kernel_program_return_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output step -> tmr_task_signal_public_slots_preserved state current.
Proof.
  intros * Hsource; destruct Hsource.
  - eapply tmr_task_program_c_step_source_preserves_public_slots; exact H.
  - destruct (SelectedReturnPrimitive.kernel_selected_return_c_step_state_stop _ _ _ _ _ _ _ _ Hstep) as [-> ->].
    apply tmr_task_signal_public_slots_refl.
  - eapply tmr_task_install_c_segment_preserves_public_slots.
    exact (@InstallComponent.TaskInstallCStep environment local sg frame call before installed sp actual complete).
  - apply tmr_task_signal_public_slots_event_eq; reflexivity.
Qed.

Lemma tmr_task_suspend_step_preserves_public_slots : forall sg request priority state result self current,
  task_suspend_step sg request priority state result self current -> tmr_task_signal_public_slots_preserved state current.
Proof.
  intros * [error [Herror [Hpriority Hstep]]].
  destruct (Z.eqb (task_suspend_resolved_priority sg request priority) sg.(osTaskIdlePrio)).
  - destruct Hstep as [_ ->]; apply tmr_task_signal_public_slots_refl.
  - destruct (state.(TskState).(prioTbl) (task_suspend_resolved_priority sg request priority)).
    + destruct Hstep as [_ ->]; apply tmr_task_signal_public_slots_refl.
    + destruct Hstep as [_ ->]; apply tmr_task_signal_public_slots_refl.
    + destruct Hstep as [old [_ [_ ->]]]; apply tmr_task_signal_public_slots_event_eq; reflexivity.
Qed.

Lemma tmr_task_selected_c_step_source_preserves_public_slots :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (step : SelectedCProgram.kernel_program_selected_c_step environment critical sg observer origin
      state before input stopped current after output),
  SelectedCSource.kernel_program_selected_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output step -> tmr_task_signal_public_slots_preserved state current.
Proof.
  intros * Hsource; destruct Hsource.
  - eapply tmr_task_return_c_step_source_preserves_public_slots; exact H.
  - destruct step.
    destruct (BuiltinComponent.os_int_exit_configured_transfer_state_frame environment sg handler entry transfer source)
      as [Hnodes [Hlife [Hevent Hrest]]].
    apply tmr_task_signal_public_slots_event_eq; exact Hevent.
  - destruct step as [saved_local caller saved call frame before after [[Hread Hcode] Hinput Houtput]].
    eapply tmr_task_suspend_step_preserves_public_slots; exact Hcode.
Qed.

Lemma tmr_task_selected_c_sequence_source_preserves_public_slots :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (run : kernel_c_sequence (SelectedCProgram.kernel_program_selected_c_step environment critical sg observer origin)
      state before input stopped current after output),
  SelectedCSource.kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    state before input stopped current after output run -> tmr_task_signal_public_slots_preserved state current.
Proof.
  intros * Hsource.
  eapply (kernel_c_sequence_source_relation (SelectedCProgram.kernel_program_selected_c_step environment critical sg observer origin)
    (SelectedCSource.kernel_program_selected_c_step_source environment critical sg observer origin event_observer)
    tmr_task_signal_public_slots_preserved).
  - apply tmr_task_signal_public_slots_refl.
  - apply tmr_task_signal_public_slots_trans.
  - intros; eapply tmr_task_selected_c_step_source_preserves_public_slots; eassumption.
  - exact Hsource.
Qed.

Definition tmr_task_signal_public_frame (before after : UCOS2_Verify_State) : Prop :=
  after.(TimerState).(timerSignalSem) = before.(TimerState).(timerSignalSem) /\
  tmr_task_signal_public_slots_preserved before after.

Lemma tmr_task_signal_public_frame_refl : forall state, tmr_task_signal_public_frame state state.
Proof. intros; split; [reflexivity|apply tmr_task_signal_public_slots_refl]. Qed.

Lemma tmr_task_signal_public_frame_trans : forall before middle after,
  tmr_task_signal_public_frame before middle -> tmr_task_signal_public_frame middle after ->
  tmr_task_signal_public_frame before after.
Proof.
  intros before middle after [Hfirst Hfirst_slots] [Hlast Hlast_slots].
  split; [congruence|eapply tmr_task_signal_public_slots_trans; eassumption].
Qed.

Lemma tmr_task_event_timer_eq_signal_public_frame : forall before after,
  after.(EventState) = before.(EventState) -> after.(TimerState) = before.(TimerState) ->
  tmr_task_signal_public_frame before after.
Proof.
  intros before after Hevent Htimer; split; [rewrite Htimer; reflexivity|].
  apply tmr_task_signal_public_slots_event_eq; exact Hevent.
Qed.

Lemma tmr_task_registered_trace_signal_public_frame :
  forall external critical sg observer event_observer before stopped after,
  tmr_task_registered_source_coverage external critical ->
  kernel_client_resource_trace critical.(critical_region_clients) sg observer event_observer before stopped after ->
  tmr_task_signal_public_frame before after.
Proof.
  intros * Hcoverage Htrace; split.
  - eapply tmr_task_registered_trace_signal_value; eassumption.
  - intros eid generation Hslot; eapply tmr_task_registered_trace_preserves_signal_public_slot; eassumption.
Qed.

Lemma tmr_task_registered_resumption_signal_public_frame :
  forall external port critical sg observer event_observer origin before stopped next_origin after,
  tmr_task_registered_source_coverage external critical ->
  kernel_resumption_task_source_trace external port critical.(critical_region_clients) sg
    observer event_observer origin before stopped next_origin after ->
  tmr_task_signal_public_frame before after.
Proof.
  intros * Hcoverage Htrace; eapply tmr_task_registered_trace_signal_public_frame; [exact Hcoverage|].
  apply kernel_resumption_resource_trace_erases.
  exact (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)).
Qed.

Lemma tmr_task_registered_delete_environment_signal_public_frame :
  forall environment critical saved_local requested sg completed phase loan original before returned after
    mask before_heap after_heap frame,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  sched_task_delete_environment_execution environment critical saved_local requested sg completed
    phase loan original before returned after mask before_heap after_heap frame ->
  tmr_task_signal_public_frame before after.
Proof.
  intros * Hcoverage Hsource.
  destruct (sched_task_delete_environment_source_resources environment critical saved_local requested sg completed
    phase loan original before returned after mask before_heap after_heap frame Hsource) as [Htrace Hrest].
  eapply tmr_task_registered_resumption_signal_public_frame; eassumption.
Qed.

Lemma tmr_task_registered_delete_window_signal_public_frame :
  forall environment critical sg before before_heap after after_heap,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  sched_task_delete_window_execution environment critical sg before before_heap after after_heap ->
  tmr_task_signal_public_frame before after.
Proof.
  intros environment critical sg before before_heap after after_heap Hcoverage Hsource.
  destruct Hsource as [saved_local requested completed arch restore save original initial
    first acquired priority tid node prepared loan saved cursor initial_heap written
    prefix_heap middle between restore_environment_heap final_cursor middle_heap registers
    returned resumed save_environment_heap final_registers reacquired final_heap frame
    Henv Hprep Hr0 Hmask Hpre Hprefix Hactual_restore Hsuffix_restore Hactual_save
    Hreturn Hvalid Hsave_mask Hsuffix_save].
  destruct (task_delete_prepared_restore_save_window environment critical saved_local
    requested sg completed arch restore save original initial first acquired priority
    tid node prepared loan saved cursor initial_heap written prefix_heap middle between
    restore_environment_heap final_cursor middle_heap registers returned resumed
    save_environment_heap final_registers reacquired final_heap frame Henv Hprep Hr0 Hmask
    Hpre Hprefix Hactual_restore Hsuffix_restore Hactual_save Hreturn Hvalid Hsave_mask Hsuffix_save)
    as [Hreturn_word [Hstate [Hrestore_history [Hsave_history Hrest]]]].
  destruct Hrestore_history as [Hrestore_trace Hrestore_rest].
  destruct Hsave_history as [Hsave_trace Hsave_rest].
  eapply tmr_task_signal_public_frame_trans.
  - eapply tmr_task_registered_resumption_signal_public_frame; [exact Hcoverage|exact Hrestore_trace].
  - eapply tmr_task_registered_resumption_signal_public_frame; [exact Hcoverage|exact Hsave_trace].
Qed.

Lemma tmr_task_registered_phase_heap_step_signal_public_frame :
  forall environment critical sg before before_heap after after_heap,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  sched_task_phase_heap_step environment critical sg before before_heap after after_heap ->
  tmr_task_signal_public_frame before after.
Proof.
  intros * Hcoverage Hsource; split.
  - eapply tmr_task_phase_heap_step_signal_value; exact Hsource.
  - destruct Hsource.
    + destruct (sched_task_mutex_del_always_source_resources environment.(task_stack_call_external)
        sg eid entry prepared event mutex before_heap after_heap frame H H0 H1 H2 H3)
        as [Hphase [Hcritical Hafter]].
      intros observed generation Hslot; eapply tmr_task_signal_public_slot_mutex_delete; eassumption.
    + exact (proj2 (tmr_task_registered_delete_environment_signal_public_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcoverage H)).
    + exact (proj2 (tmr_task_registered_delete_window_signal_public_frame _ _ _ _ _ _ _ Hcoverage H)).
Qed.

Lemma tmr_task_registered_phase_heap_source_signal_public_frame :
  forall environment critical sg before before_heap after after_heap,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  sched_task_phase_heap_source environment critical sg before before_heap after after_heap ->
  tmr_task_signal_public_frame before after.
Proof.
  intros * Hcoverage Hsource; induction Hsource.
  - apply tmr_task_signal_public_frame_refl.
  - eapply tmr_task_signal_public_frame_trans; [|exact IHHsource].
    eapply tmr_task_registered_phase_heap_step_signal_public_frame; eassumption.
Qed.

Lemma tmr_task_registered_return_prefix_signal_public_frame :
  forall environment critical sg observer before after after_heap,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  os_sched_task_return_prefix environment critical sg observer before after after_heap ->
  tmr_task_signal_public_frame before after.
Proof.
  intros * Hcoverage Hsource; destruct Hsource.
  - destruct H.
    + eapply tmr_task_registered_trace_signal_public_frame; eassumption.
    + eapply tmr_task_registered_phase_heap_source_signal_public_frame; eassumption.
  - split.
    + eapply tmr_task_signal_public_trace_value.
      exact (proj2 (proj2 (proj2 (kernel_program_selected_c_sequence_source_frames
        _ _ _ _ _ _ _ _ _ _ _ _ _ run H)))).
    + eapply tmr_task_selected_c_sequence_source_preserves_public_slots; exact H.
Qed.

Lemma tmr_task_registered_irq_return_prefix_signal_public_frame :
  forall environment critical sg observer before after,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  os_sched_task_irq_return_prefix environment critical sg observer before after ->
  tmr_task_signal_public_frame before after.
Proof.
  intros * Hcoverage [Htrace|[heap Hprefix]].
  - eapply tmr_task_registered_trace_signal_public_frame; eassumption.
  - eapply tmr_task_registered_return_prefix_signal_public_frame; eassumption.
Qed.

(** The four original body cases retain their actual source witnesses.
    Only current signal/slot projections are transported; the intermediate
    states need not satisfy the stable scheduler invariant. *)
Lemma tmr_task_registered_body_source_signal_public_frame :
  forall environment critical sg entry original returned current,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  task_sw_hook_source_binding environment.(task_stack_call_external) ->
  os_sched_task_body_source environment critical sg entry original returned current ->
  tmr_task_signal_public_frame entry current.
Proof.
  intros * Hcoverage Hbinding Hbody; destruct Hbody.
  - apply tmr_task_event_timer_eq_signal_public_frame; reflexivity.
  - destruct (tmr_task_bound_switch_event_timer_eq _ _ _ _ _ Hbinding H) as [Hevents Htimers].
    eapply tmr_task_signal_public_frame_trans.
    + apply tmr_task_event_timer_eq_signal_public_frame; eassumption.
    + change (tmr_task_signal_public_frame first_installed hooked).
      eapply tmr_task_registered_return_prefix_signal_public_frame; eassumption.
  - destruct (tmr_task_bound_switch_event_timer_eq _ _ _ _ _ Hbinding H) as [Hevents Htimers].
    destruct (tmr_task_bound_irq_transfer_event_timer_eq _ _ _ _ _ _ Hbinding H2) as [Hlast_event Hlast_timer].
    eapply tmr_task_signal_public_frame_trans; [|apply tmr_task_event_timer_eq_signal_public_frame; eassumption].
    eapply tmr_task_signal_public_frame_trans; [apply tmr_task_event_timer_eq_signal_public_frame; eassumption|].
    eapply tmr_task_registered_irq_return_prefix_signal_public_frame; eassumption.
  - destruct (tmr_task_bound_switch_event_timer_eq _ _ _ _ _ Hbinding H) as [Hevents Htimers].
    destruct (tmr_task_bound_switch_event_timer_eq _ _ _ _ _ Hbinding H2) as [Hlast_event Hlast_timer].
    eapply tmr_task_signal_public_frame_trans; [|apply tmr_task_event_timer_eq_signal_public_frame; eassumption].
    eapply tmr_task_signal_public_frame_trans; [apply tmr_task_event_timer_eq_signal_public_frame; eassumption|].
    eapply tmr_task_registered_return_prefix_signal_public_frame; eassumption.
Qed.

Lemma tmr_task_registered_interval_signal_public_frame : forall external critical sg invocation before after,
  tmr_task_registered_source_coverage external critical ->
  critical_region_interval critical sg invocation before after -> tmr_task_signal_public_frame before after.
Proof.
  intros * Hcoverage Hsource; eapply tmr_task_registered_trace_signal_public_frame; [exact Hcoverage|].
  eapply critical_region_interval_raw_trace; exact Hsource.
Qed.

Lemma tmr_task_registered_sched_return_signal_public_frame :
  forall external critical sg before call returned after,
  tmr_task_registered_source_coverage external critical -> task_sw_hook_source_binding external ->
  os_sched_c_return external critical sg before call returned after -> tmr_task_signal_public_frame before after.
Proof.
  intros * Hcoverage Hbinding Hsource; unfold os_sched_c_return in Hsource.
  destruct (os_sched_requests_switch before).
  - destruct Hsource as [installed [Hswitch [[stopped [Htrace Hstop]] Hrest]]].
    destruct (tmr_task_bound_switch_event_timer_eq _ _ _ _ _ Hbinding Hswitch) as [Hevent Htimer].
    eapply tmr_task_signal_public_frame_trans.
    + apply tmr_task_event_timer_eq_signal_public_frame; eassumption.
    + eapply tmr_task_registered_trace_signal_public_frame; eassumption.
  - destruct Hsource as [_ ->]; apply tmr_task_event_timer_eq_signal_public_frame; reflexivity.
Qed.

Lemma tmr_task_irq_parked_signal_public_frame : forall before call sp fragments,
  tmr_task_signal_public_frame before (armv7a_irq_live_parked_state before call sp fragments).
Proof.
  intros; unfold armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
    armv7a_irq_entry_counter_state, os_sched_save_current_sp.
  destruct before.(SchedState).(isRunning); apply tmr_task_event_timer_eq_signal_public_frame; reflexivity.
Qed.

Lemma tmr_task_registered_save_history_signal_public_frame :
  forall environment critical sg call before returned after,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  kernel_call_save_history environment critical sg call before returned after ->
  tmr_task_signal_public_frame before after.
Proof.
  intros * Hcoverage Hsource; destruct Hsource; try apply tmr_task_signal_public_frame_refl.
  all: match goal with Htrace : kernel_resumption_task_source_trace _ _ _ _ _ _ _
      (armv7a_irq_live_parked_state ?state ?call ?sp ?fragments) _ _ ?current |- _ =>
    eapply tmr_task_signal_public_frame_trans;
      [apply (tmr_task_irq_parked_signal_public_frame state call sp fragments)|];
    eapply tmr_task_signal_public_frame_trans;
      [eapply tmr_task_registered_resumption_signal_public_frame; [exact Hcoverage|exact Htrace]|];
    apply tmr_task_event_timer_eq_signal_public_frame; reflexivity
    end.
Qed.

Lemma tmr_task_registered_restore_history_signal_public_frame :
  forall environment critical sg call before returned after,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  kernel_call_restore_history environment critical sg call before returned after ->
  tmr_task_signal_public_frame before after.
Proof.
  intros * Hcoverage Hsource; destruct Hsource; try apply tmr_task_signal_public_frame_refl.
  all: match goal with Htrace : kernel_resumption_task_source_trace _ _ _ _ _ _ _
      (armv7a_irq_live_parked_state ?state ?call ?sp ?fragments) _ _ ?current |- _ =>
    eapply tmr_task_signal_public_frame_trans;
      [apply (tmr_task_irq_parked_signal_public_frame state call sp fragments)|];
    eapply tmr_task_signal_public_frame_trans;
      [eapply tmr_task_registered_resumption_signal_public_frame; [exact Hcoverage|exact Htrace]|];
    apply tmr_task_event_timer_eq_signal_public_frame; reflexivity
    end.
Qed.

Lemma tmr_task_registered_save_call_signal_public_frame :
  forall environment critical sg call before returned after,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  sem_pend_save_call_history environment critical sg call before returned after ->
  tmr_task_signal_public_frame before after.
Proof.
  intros * Hcoverage [Hhistory|[Htrace Hnormal]].
  - eapply tmr_task_registered_save_history_signal_public_frame; eassumption.
  - eapply tmr_task_registered_resumption_signal_public_frame; eassumption.
Qed.

Lemma tmr_task_registered_restore_call_signal_public_frame :
  forall environment critical sg call before returned after,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  sem_pend_restore_call_history environment critical sg call before returned after ->
  tmr_task_signal_public_frame before after.
Proof.
  intros * Hcoverage [Hhistory|[Htrace Hnormal]].
  - eapply tmr_task_registered_restore_history_signal_public_frame; eassumption.
  - eapply tmr_task_registered_resumption_signal_public_frame; eassumption.
Qed.

Lemma tmr_task_registered_legacy_wait_signal_public_frame :
  forall environment critical sg original eid generation before after,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  task_sw_hook_source_binding environment.(task_stack_call_external) ->
  sem_pend_wait_source_history environment critical sg original eid generation before after ->
  tmr_task_signal_public_frame before after.
Proof.
  intros * Hcoverage Hbinding Hhistory; induction Hhistory.
  - apply tmr_task_signal_public_frame_refl.
  - eapply tmr_task_registered_resumption_signal_public_frame; eassumption.
  - apply tmr_task_event_timer_eq_signal_public_frame; reflexivity.
  - apply tmr_task_event_timer_eq_signal_public_frame; reflexivity.
  - unfold os_int_exit_installed_state; rewrite H.
    apply tmr_task_event_timer_eq_signal_public_frame; reflexivity.
  - eapply tmr_task_registered_save_history_signal_public_frame; eassumption.
  - eapply tmr_task_registered_restore_history_signal_public_frame; eassumption.
  - apply tmr_task_event_timer_eq_signal_public_frame; reflexivity.
  - apply tmr_task_event_timer_eq_signal_public_frame; reflexivity.
  - eapply tmr_task_registered_interval_signal_public_frame; eassumption.
  - eapply tmr_task_registered_sched_return_signal_public_frame; eassumption.
  - eapply tmr_task_signal_public_frame_trans; eassumption.
Qed.

Lemma tmr_task_registered_source_history_signal_public_frame :
  forall environment critical sg original eid generation before after,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  task_sw_hook_source_binding environment.(task_stack_call_external) ->
  sem_pend_source_history environment critical sg original eid generation before after ->
  tmr_task_signal_public_frame before after.
Proof.
  intros * Hcoverage Hbinding Hhistory; induction Hhistory.
  - eapply tmr_task_registered_legacy_wait_signal_public_frame; eassumption.
  - eapply tmr_task_registered_resumption_signal_public_frame; eassumption.
  - eapply tmr_task_registered_sched_return_signal_public_frame; eassumption.
  - eapply tmr_task_signal_public_frame_trans; eassumption.
Qed.

Lemma tmr_task_client_return_signal_public_frame :
  forall environment critical sg call before returned after,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  sem_pend_client_return_source environment critical sg call before returned after ->
  tmr_task_signal_public_frame before after.
Proof.
  intros environment critical sg call before returned after Hcoverage Hsource.
  pose proof (proj1 (sem_pend_client_return_source_traces _ _ _ _ _ _ _ Hsource)) as Htrace.
  clear Hsource.
  induction Htrace as [first before stopped last after trace Hcalls
    |action first before last after Hmember Htyped Hevent Hstep Hcontrol Hreceipt
    |environment0 critical0 first before before_heap input last after after_heap output
      Hexternal Hport Hclients Hcompletion
    |entry_environment first initial node handler suspended publication local frame
      before_heap saved_heap body_heap Hexternal Hport Hentry
    |post_environment post_critical source_env post_local post_frame post_call
      before_heap after_heap post_origin Hsegment Hexternal Hport Hclients Hreceipt
    |inherit_environment inherit_critical inherit_local inherit_frame inherit_call
      before_heap after_heap inherit_origin Hsegment Hexternal Hport Hclients
    |suspend_environment suspend_critical suspend_local suspend_caller suspend_saved suspend_call
      suspend_frame before_heap after_heap suspend_origin Hcompletion Hexternal Hport Hclients
    |install_environment install_local install_frame install_call before_heap after_heap sp Hactual
      Hsegment Hexternal Hport
    |stored_origin capture body_heap restore_selected restore_rely save_selected save_rely
      restore_stopped save_stopped Hdelete_source Hexternal Hport Hclients Hsg Hregistered
    |first before stopped1 middle transient stopped2 last after Hfirst IHfirst Hlast IHlast].
  - eapply tmr_task_registered_trace_signal_public_frame; [exact Hcoverage|].
    exact (proj1 (kernel_client_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ trace)).
  - split.
    + eapply tmr_task_source_client_signal_value;
        [exact (proj1 (Hcoverage action Hmember))|exact Hstep].
    + intros eid generation Hslot.
      eapply tmr_task_source_client_preserves_signal_public_slot;
        [exact (proj1 (Hcoverage action Hmember))|exact Hstep|exact Hslot].
  - pose proof (sem_pend_irq_completion_source_frame _ _ _ _ _ _ _ _ _ _ _ Hcompletion) as Hframe.
    eapply tmr_task_event_timer_eq_signal_public_frame.
    + exact (sem_pend_irq_cut_events _ _ Hframe).
    + exact (sem_pend_irq_cut_timers _ _ Hframe).
  - destruct (sem_pend_irq_entry_frames _ _ _ _ _ _ _ _ _ _ _ _ Hentry)
      as [Hlifecycle [Hevents [Hnames [Htimers Hsched]]]].
    eapply tmr_task_event_timer_eq_signal_public_frame; [exact Hevents|exact Htimers].
  - pose proof (PostComponent.mutex_post_critical_segment_source source_env
      post_environment.(task_stack_call_external) post_environment.(task_stack_call_platform)
      post_critical post_local sg post_frame post_call before_heap after_heap Hsegment) as Hcode.
    split.
    + pose proof (proj2 (mutex_post_critical_name_timer_fields _ _ _ _ _ _ _ (proj2 Hcode)))
        as Htimers.
      rewrite <- Htimers; reflexivity.
    + eapply tmr_task_program_remaining_source_preserves_public_slots with
        (step := @KernelProgramCMutexPost post_environment post_critical sg
          call.(os_sched_call_invocation) post_origin source_env post_local post_frame post_call
          before_heap after_heap Hsegment).
      constructor.
  - pose proof (PendComponent.mutex_pend_inheritance_segment_source inherit_environment inherit_critical
      inherit_local sg inherit_frame inherit_call before_heap after_heap Hsegment) as Hcode.
    split.
    + pose proof (sem_pend_mutex_inheritance_timer_frame _ _ _ _ _ _ _ _ (proj2 (proj2 Hcode)))
        as Htimers.
      rewrite Htimers; reflexivity.
    + eapply tmr_task_program_remaining_source_preserves_public_slots with
        (step := @KernelProgramCMutexPend inherit_environment inherit_critical sg
          call.(os_sched_call_invocation) inherit_origin inherit_local inherit_frame inherit_call
          before_heap after_heap Hsegment).
      constructor.
  - pose proof (TaskSuspendMaskedC.suspend_masked_source _ _ _ _ _ _ _ _ _ _ Hcompletion)
      as [_ Hcode].
    destruct (TaskSuspendActualC.task_suspend_step_state_cases _ _ _ _ _ _ _ Hcode)
      as [Hstate|[slot [node [Hnode Hstate]]]];
      eapply tmr_task_event_timer_eq_signal_public_frame; rewrite Hstate; reflexivity.
  - destruct Hsegment as [Hsource Hcompletion].
    destruct (os_sched_install_client_state_frame _ _ _ _ _ sg _ _ Hsource)
      as [_ [_ [Hevents [_ [_ [_ Htimers]]]]]].
    eapply tmr_task_event_timer_eq_signal_public_frame; eassumption.
  - destruct (sem_pend_delete_call_frames _ _ _ _ _ _ _ _ _ _ _ Hdelete_source)
      as [_ [_ [_ [Htimers Hidentity]]]].
    split.
    + eapply tmr_task_signal_public_trace_value; exact Htimers.
    + eapply tmr_task_live_sem_public_slots_from_returned_pool; [exact Hidentity|].
      pose proof (sem_pend_delete_capture_body_valid _ _ _ _ _ _ _ _ _ _ _ Hdelete_source) as Hvalid.
      exact (proj1 (proj1 (proj2 (proj2 (proj2 Hvalid))))).
  - eapply tmr_task_signal_public_frame_trans; eassumption.
Qed.

Lemma tmr_task_client_wait_signal_public_frame :
  forall environment critical sg original eid generation before after,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  task_sw_hook_source_binding environment.(task_stack_call_external) ->
  sem_pend_client_wait_source environment critical sg original eid generation before after ->
  tmr_task_signal_public_frame before after.
Proof.
  intros * Hcoverage Hbinding Hsource; induction Hsource.
  - eapply tmr_task_registered_source_history_signal_public_frame; eassumption.
  - eapply tmr_task_client_return_signal_public_frame; eassumption.
  - eapply tmr_task_registered_body_source_signal_public_frame; eassumption.
  - eapply tmr_task_signal_public_frame_trans; eassumption.
Qed.

Lemma tmr_task_pend_first_signal_public_frame : forall sg eid timeout before result after,
  sem_pend_first_critical sg eid timeout before result after -> tmr_task_signal_public_frame before after.
Proof.
  intros * [event [fields [Hselected [Hfields Hstep]]]].
  destruct (Z.ltb 0 fields.(semCount)).
  - destruct Hstep as [_ ->]; split; [reflexivity|].
    intros observed generation Hslot; eapply tmr_task_signal_public_slot_count; eassumption.
  - destruct Hstep as [tid [old [Hcurrent [Hold [_ ->]]]]]; split; [reflexivity|].
    intros observed generation Hslot.
    eapply tmr_task_signal_public_slot_live_frame with (before := before);
      [|reflexivity|reflexivity|exact Hslot].
    intros target previous Hlookup Hsem.
    unfold mutex_query_lookup, event_pend_state, event_wait_state in *;
      cbn [replace_SchedS EventState replace_EventS replace_TskS].
    eapply tmr_task_signal_event_update_preserves_identity;
      [exact Hselected|reflexivity|reflexivity|exact Hlookup].
Qed.

Lemma tmr_task_pend_cleanup_signal_public_frame : forall sg eid before result after,
  sem_pend_resume_critical sg eid before result after -> tmr_task_signal_public_frame before after.
Proof.
  intros * [tid [old [Hcurrent [Hold [_ Hstep]]]]]; destruct old.(statPend).
  - subst after; apply tmr_task_event_timer_eq_signal_public_frame; reflexivity.
  - destruct Hstep as [event [Hselected ->]]; split; [reflexivity|].
    intros observed generation Hslot.
    eapply tmr_task_signal_public_slot_live_frame with (before := before);
      [|reflexivity|reflexivity|exact Hslot].
    intros target previous Hlookup Hsem.
    unfold mutex_query_lookup, event_task_remove_state, event_pend_cleanup_state in *;
      cbn [replace_EventS EventState replace_TskS].
    eapply tmr_task_signal_wait_list_update_preserves_identity; eassumption.
  - subst after; apply tmr_task_event_timer_eq_signal_public_frame; reflexivity.
Qed.

Lemma tmr_task_legacy_checkpoint_signal_public_frame :
  forall environment critical sg call pevent timeout before error checkpoint,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  task_sw_hook_source_binding environment.(task_stack_call_external) ->
  sem_pend_source_checkpoint_result (Some environment) critical sg call pevent timeout before error checkpoint ->
  tmr_task_signal_public_frame before checkpoint.
Proof.
  intros * Hcoverage Hbinding
    (eid & observed & returned & mask & saved & entry & current & start & waiting &
      Hnonnull & Haddress & Hid & Hslot & Hcontext & Hacquire & Hfirst & Hresult).
  change (sem_pend_acquire_observation environment critical sg call returned mask saved
    before entry eid observed current) in Hacquire.
  assert (Hwaiting : tmr_task_signal_public_frame before waiting).
  { eapply tmr_task_signal_public_frame_trans.
    - eapply tmr_task_registered_save_call_signal_public_frame; [exact Hcoverage|exact (proj1 Hacquire)].
    - eapply tmr_task_pend_first_signal_public_frame; exact Hfirst. }
  destruct start as [|tid generation].
  - destruct Hresult as [_ ->]; exact Hwaiting.
  - destruct Hresult as [_ [owned [resumed [node [code
      [Howned [Hwait [_ [_ [_ Hcleanup]]]]]]]]]].
    injection Howned as Howned; subst owned.
    eapply tmr_task_signal_public_frame_trans; [exact Hwaiting|].
    eapply tmr_task_signal_public_frame_trans.
    + eapply tmr_task_registered_source_history_signal_public_frame; eassumption.
    + eapply tmr_task_pend_cleanup_signal_public_frame; exact Hcleanup.
Qed.

Lemma tmr_task_legacy_runtime_signal_public_frame :
  forall environment critical sg call pevent timeout before error current,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  task_sw_hook_source_binding environment.(task_stack_call_external) ->
  sem_pend_source_fields_program environment critical sg call pevent timeout before error current ->
  tmr_task_signal_public_frame before current.
Proof.
  intros * Hcoverage Hbinding [[Hearly [Hguard ->]]|
    [checkpoint [entered [returned [eid [Hcheckpoint [_ [_ [_ [_ Hrestore]]]]]]]]]].
  - apply tmr_task_signal_public_frame_refl.
  - eapply tmr_task_signal_public_frame_trans.
    + eapply tmr_task_legacy_checkpoint_signal_public_frame; eassumption.
    + eapply tmr_task_registered_restore_call_signal_public_frame; eassumption.
Qed.

Lemma tmr_task_client_checkpoint_signal_public_frame :
  forall environment critical sg call pevent timeout before error checkpoint,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  task_sw_hook_source_binding environment.(task_stack_call_external) ->
  sem_pend_client_checkpoint_result environment critical sg call pevent timeout before error checkpoint ->
  tmr_task_signal_public_frame before checkpoint.
Proof.
  intros * Hcoverage Hbinding
    (eid & observed & returned & mask & saved & entry & current & start & waiting &
      Hnonnull & Haddress & Hid & Hslot & Hcontext & Hacquire & Hfirst & Hresult).
  assert (Hwaiting : tmr_task_signal_public_frame before waiting).
  { eapply tmr_task_signal_public_frame_trans.
    - eapply tmr_task_client_return_signal_public_frame; [exact Hcoverage|exact (proj1 Hacquire)].
    - eapply tmr_task_pend_first_signal_public_frame; exact Hfirst. }
  destruct start as [|tid generation].
  - destruct Hresult as [_ ->]; exact Hwaiting.
  - destruct Hresult as [_ [resumed [node [code [Hwait [_ [_ [_ Hcleanup]]]]]]]].
    eapply tmr_task_signal_public_frame_trans; [exact Hwaiting|].
    eapply tmr_task_signal_public_frame_trans.
    + eapply tmr_task_client_wait_signal_public_frame; eassumption.
    + eapply tmr_task_pend_cleanup_signal_public_frame; exact Hcleanup.
Qed.

Lemma tmr_task_client_runtime_signal_public_frame :
  forall environment critical sg call pevent timeout before error current,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  task_sw_hook_source_binding environment.(task_stack_call_external) ->
  sem_pend_client_runtime_program environment critical sg call pevent timeout before error current ->
  tmr_task_signal_public_frame before current.
Proof.
  intros * Hcoverage Hbinding [Hlegacy|[checkpoint [entered [returned [Hcheckpoint [Hsame Hrestore]]]]]].
  - eapply tmr_task_legacy_runtime_signal_public_frame; eassumption.
  - eapply tmr_task_signal_public_frame_trans.
    + eapply tmr_task_client_checkpoint_signal_public_frame; eassumption.
    + eapply tmr_task_client_return_signal_public_frame; eassumption.
Qed.

Lemma tmr_task_signal_public_frame_preserves_lifetime : forall critical sg invocation before after,
  event_pool_partition sg before.(EventState) ->
  tmr_task_signal_public_frame before after -> tmr_task_signal_lifetime critical sg invocation before ->
  tmr_task_signal_lifetime critical sg invocation after.
Proof.
  intros critical sg invocation before after Hpool [Hsignal Hslots]
    [Hnull|[eid [previous [Hnonnull [Haddress [Hid [Hlookup [Hsem Hprotocol]]]]]]]].
  - left; rewrite Hsignal; exact Hnull.
  - pose proof (tmr_task_signal_public_slot_from_pool sg before.(EventState) eid previous Hpool Hlookup Hsem) as Hslot.
    destruct (Hslots eid previous.(eventGeneration) Hslot) as [current [Hcurrent [Hgen [Htype Hrest]]]].
    right; exists eid, current.
    split; [rewrite Hsignal; exact Hnonnull|]. split; [rewrite Hsignal; exact Haddress|].
    split; [exact Hid|]. split; [exact Hcurrent|]. split; assumption.
Qed.

(** The actual client program is retained in full, including its legacy
    union, the four Scheduler cases and transitive waiting paths. The only
    pool fact is read once from the caller's actual initial world owner. *)
Lemma tmr_task_client_runtime_preserves_signal_lifetime :
  forall environment critical sg call pevent timeout before error current,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  task_sw_hook_source_binding environment.(task_stack_call_external) ->
  UCOS2_state_inv sg before ->
  tmr_task_signal_lifetime critical sg call.(os_sched_call_invocation) before ->
  sem_pend_client_runtime_program environment critical sg call pevent timeout before error current ->
  tmr_task_signal_lifetime critical sg call.(os_sched_call_invocation) current.
Proof.
  intros * Hcoverage Hbinding Hvalid Hlife Hsource.
  eapply tmr_task_signal_public_frame_preserves_lifetime;
    [exact (proj1 (proj1 (proj2 (proj2 (proj2 Hvalid)))))| |exact Hlife].
  eapply tmr_task_client_runtime_signal_public_frame; eassumption.
Qed.
