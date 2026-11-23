Require Import Coq.Lists.List Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_handle_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_delete_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_c_segment_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_c_segment_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_c_segment_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_api_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_c_segment_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.mutex_query_spec Ucos2Verify.lib.sem.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.queue_core Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.flag_fields_resources Ucos2Verify.lib.ucos2_verify_inv.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This relation observes the existing public ECB map.  It neither owns
    an additional map nor identifies a private-allocation frame with a
    public handle.  A selected C consumer below must use its actual step. *)
Definition tmr_task_live_sem_identity (before after : UCOS2_Verify_State) : Prop :=
  forall eid previous,
    mutex_query_lookup before eid previous ->
    previous.(eventType) = OS_EVENT_TYPE_SEM ->
    exists current, mutex_query_lookup after eid current /\
      current.(eventGeneration) = previous.(eventGeneration) /\
      current.(eventType) = previous.(eventType).

Lemma tmr_task_live_sem_identity_refl : forall state,
  tmr_task_live_sem_identity state state.
Proof. intros state eid previous Hlookup Htype; exists previous; auto. Qed.

Lemma tmr_task_live_sem_identity_trans : forall first middle last,
  tmr_task_live_sem_identity first middle ->
  tmr_task_live_sem_identity middle last ->
  tmr_task_live_sem_identity first last.
Proof.
  intros first middle last Hfirst Hlast eid previous Hlookup Hsem.
  destruct (Hfirst eid previous Hlookup Hsem) as [next [Hnext [Hgeneration Htype]]].
  destruct (Hlast eid next Hnext ltac:(congruence)) as [current [Hcurrent [Hgeneration' Htype']]].
  exists current; split; [exact Hcurrent|]. split; congruence.
Qed.

Lemma tmr_task_event_state_eq_preserves_live_sem : forall before after,
  after.(EventState) = before.(EventState) -> tmr_task_live_sem_identity before after.
Proof.
  intros before after Hevents eid previous Hlookup Htype.
  exists previous; split; [unfold mutex_query_lookup in *; rewrite Hevents; exact Hlookup|].
  split; reflexivity.
Qed.

Lemma tmr_task_live_sem_identity_preserves_lifetime : forall critical sg invocation before after,
  tmr_task_signal_lifetime critical sg invocation before ->
  after.(TimerState).(timerSignalSem) = before.(TimerState).(timerSignalSem) ->
  tmr_task_live_sem_identity before after ->
  tmr_task_signal_lifetime critical sg invocation after.
Proof.
  intros critical sg invocation before after Hlife Hsignal Hidentity.
  destruct Hlife as [Hnull|[eid [previous [Hnonnull [Haddress [Hid [Hlookup [Hsem Hprotocol]]]]]]]].
  - left; congruence.
  - destruct (Hidentity eid previous Hlookup Hsem) as [current [Hcurrent [Hgeneration Htype]]].
    right; exists eid, current; split; [congruence|]. split; [congruence|].
    split; [exact Hid|]. split; [exact Hcurrent|]. split; [congruence|exact Hprotocol].
Qed.

(** The publication pre owns the private and public storage at the SAME
    heap.  Their Type bytes cannot alias, even when the private byte is
    uninitialized.  No global state invariant is needed for this fact. *)
Lemma tmr_task_event_storage_type_byte : forall named base image,
  event_storage_rep named base image |--
  base # UChar |->_ ** event_storage_without_field named base image EventTypeField.
Proof.
  intros named base image.
  sep_apply_l_atomic (event_storage_split_field named base image EventTypeField ltac:(simpl; auto)).
  cbn [event_cell event_field_offset]. rewrite Z.add_0_r.
  destruct (image EventTypeField) as [value|];
    [sep_apply_l_atomic (store_uchar_undef_store_uchar base value)|]; entailer!.
Qed.

Lemma tmr_task_event_storage_duplicate_false : forall named base first second,
  event_storage_rep named base first ** event_storage_rep named base second |-- coq_prop False.
Proof.
  intros named base first second.
  sep_apply_l_atomic (tmr_task_event_storage_type_byte named base first).
  sep_apply_l_atomic (tmr_task_event_storage_type_byte named base second).
  unfold undef_store_uchar.
  Intros.
  prop_apply (dup_store_byte_noninit base); entailer!.
Qed.

Lemma tmr_task_private_live_event_disjoint : forall sg tasks events selected allocation eid previous
  (frame : Assertion) heap,
  events.(inUsedEventStates) eid = Some previous ->
  (event_private_storage_rep sg selected allocation ** (event_raw_rep sg tasks events ** frame)) heap ->
  eid <> selected.
Proof.
  intros sg tasks events selected allocation eid previous frame heap Hlookup Howned Hequal.
  subst selected.
  assert (Hfalse : event_private_storage_rep sg eid allocation **
    (event_raw_rep sg tasks events ** frame) |-- coq_prop False).
  { sep_apply_l_atomic (event_raw_rep_split_eid sg tasks events eid previous Hlookup).
    unfold event_private_storage_rep, used_event_rep, event_addr.
    sep_apply_l_atomic (tmr_task_event_storage_duplicate_false
      sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
      allocation.(eventPrivateStorage) (event_image sg tasks previous)); entailer!. }
  exact (Hfalse heap Howned).
Qed.

Lemma tmr_task_event_ready_source_preserves_live_sem : forall sg before selected kind message result priority after,
  event_task_rdy sg before selected kind message result = Some (priority, after) ->
  tmr_task_live_sem_identity before after.
Proof.
  intros sg before selected kind message result priority after Hstep eid previous Hlookup Hsem.
  unfold event_task_rdy in Hstep.
  destruct (before.(EventState).(inUsedEventStates) selected) as [event|] eqn:Hselected;
    [|discriminate].
  destruct (before.(TskState).(prioTbl) (event_wait_priority before.(TskState) event));
    try discriminate.
  match type of Hstep with
  | context [before.(TskState).(inUsedTaskStates) ?tid] =>
      destruct (before.(TskState).(inUsedTaskStates) tid) as [old|] eqn:Htask
  end; [|discriminate].
  inversion Hstep; subst after.
  unfold mutex_query_lookup; cbn [event_wake_state replace_SchedS replace_EventS replace_TskS EventState].
  eapply tmr_task_signal_wait_list_update_preserves_identity; eassumption.
Qed.

Lemma tmr_task_wake_source_preserves_live_sem : forall sg before after,
  WakeComponent.kernel_wake_c_source sg before after -> tmr_task_live_sem_identity before after.
Proof.
  intros sg before after Hsource; destruct Hsource.
  - destruct (flag_task_rdy_result _ _ _ _ _ _ _ H)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    apply tmr_task_event_state_eq_preserves_live_sem; reflexivity.
  - eapply tmr_task_event_ready_source_preserves_live_sem; exact H.
  - apply tmr_task_event_state_eq_preserves_live_sem.
    unfold tick_task_step; repeat match goal with |- context [if ?test then _ else _] => destruct test end;
      reflexivity.
Qed.

Lemma tmr_task_status_source_preserves_live_sem : forall sg before after,
  StatusComponent.kernel_status_c_source sg before after -> tmr_task_live_sem_identity before after.
Proof.
  intros sg before after Hsource; destruct Hsource.
  - destruct H as [cid [current [_ [_ [_ Hstep]]]]].
    destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg priority current))).
    + destruct Hstep as [_ ->]; apply tmr_task_live_sem_identity_refl.
    + destruct Hstep as [_ ->]; apply tmr_task_live_sem_identity_refl.
    + destruct Hstep as [old [_ [_ ->]]]; apply tmr_task_event_state_eq_preserves_live_sem; reflexivity.
  - destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority).
    + destruct Hstep as [_ ->]; apply tmr_task_live_sem_identity_refl.
    + destruct Hstep as [_ ->]; apply tmr_task_live_sem_identity_refl.
    + destruct Hstep as [old [_ Hstep]]; destruct (task_is_suspended old.(stat)).
      * destruct Hstep as [_ ->]; apply tmr_task_event_state_eq_preserves_live_sem.
        unfold task_resume_state, sched_resume_task, sched_wake_by_status;
          repeat match goal with |- context [if ?test then _ else _] => destruct test end; reflexivity.
      * destruct Hstep as [_ ->]; apply tmr_task_live_sem_identity_refl.
  - destruct H as [event [fields [Hselected [_ [_ ->]]]]].
    destruct (Z.ltb 0 fields.(semCount)); [|apply tmr_task_live_sem_identity_refl].
    intros observed previous Hlookup Hsem.
    eapply tmr_task_signal_count_update_preserves_identity; eassumption.
Qed.

Lemma tmr_task_task_creation_source_preserves_live_sem : forall sg before after,
  CreationComponent.kernel_task_creation_c_source sg before after ->
  tmr_task_live_sem_identity before after.
Proof.
  intros sg before after Hsource; apply tmr_task_event_state_eq_preserves_live_sem.
  exact (proj1 (NamedSourceFrames.kernel_task_creation_c_source_other_fields _ _ _ Hsource)).
Qed.

Lemma tmr_task_event_creation_segment_preserves_live_sem : forall sg before heap input after heap' output,
  EventCreationComponent.kernel_event_creation_c_segment sg before heap input after heap' output ->
  tmr_task_live_sem_identity before after.
Proof.
  intros sg before heap input after heap' output Hsegment; destruct Hsegment.
  - unfold event_create_allocate_critical in H.
    destruct entry.(EventState).(unUsedEventStates).
    + destruct H as [_ ->]; apply tmr_task_live_sem_identity_refl.
    + destruct H as [image [_ [_ ->]]].
      intros observed previous Hlookup Hsem; exists previous; split; [exact Hlookup|]; split; reflexivity.
  - intros observed previous Hlookup Hsem; exists previous; split; [exact Hlookup|]; split; reflexivity.
  - intros observed previous Hlookup Hsem.
    assert (Hdifferent : observed <> eid).
    { eapply (tmr_task_private_live_event_disjoint sg entry.(TskState) entry.(EventState)
        eid allocation observed previous
        (queue_storage_rep sg entry.(EventState) ** UCOS2_raw_rep_missing_event_queue sg entry ** frame) h).
      - exact Hlookup.
      - assert (Hopen : EventCreationComponent.event_creation_publication_owner sg entry eid allocation ** frame |--
          event_private_storage_rep sg eid allocation **
          (event_raw_rep sg entry.(TskState) entry.(EventState) **
            (queue_storage_rep sg entry.(EventState) ** UCOS2_raw_rep_missing_event_queue sg entry ** frame))).
        { unfold EventCreationComponent.event_creation_publication_owner; entailer!. }
        exact (Hopen h H2). }
    exists previous; split; [|split; reflexivity].
    unfold mutex_query_lookup; cbn [replace_EventS EventState event_publish inUsedEventStates].
    rewrite kernel_map_set_other by exact Hdifferent; exact Hlookup.
  - unfold event_create_allocate_critical in H0.
    destruct entry.(EventState).(unUsedEventStates).
    + destruct H0 as [_ ->]; apply tmr_task_live_sem_identity_refl.
    + destruct H0 as [image [_ [_ ->]]].
      intros observed previous Hlookup Hsem; exists previous; split; [exact Hlookup|]; split; reflexivity.
  - intros observed previous Hlookup Hsem; exists previous; split; [exact Hlookup|]; split; reflexivity.
  - intros observed previous Hlookup Hsem.
    assert (Hextract : event_private_storage_rep sg eid allocation **
        kernel_program_fields_inv sg entry ** frame |--
      coq_prop (UCOS2_state_inv sg entry) &&
        (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg entry ** frame)).
    { unfold kernel_program_fields_inv; entailer!. }
    pose proof (proj1 (Hextract h H2)) as [_ [_ [_ [[Hpool _] _]]]].
    destruct (event_pool_private_not_free sg entry.(EventState) eid allocation Hpool H) as [_ [_ Hnone]].
    assert (Hdifferent : observed <> eid).
    { intro Heq; subst observed; unfold mutex_query_lookup in Hlookup; congruence. }
    exists previous; split; [|split; reflexivity].
    unfold mutex_query_lookup; cbn [replace_EventS EventState event_publish inUsedEventStates].
    rewrite kernel_map_set_other by exact Hdifferent; exact Hlookup.
Qed.

Lemma tmr_task_queue_creation_segment_preserves_live_sem : forall sg before heap input after heap' output,
  QueueCreationComponent.kernel_queue_creation_c_segment sg before heap input after heap' output ->
  tmr_task_live_sem_identity before after.
Proof.
  intros sg before heap input after heap' output Hsegment; destruct Hsegment.
  - intros observed previous Hlookup Hsem; exists previous; split; [exact Hlookup|]; split; reflexivity.
  - intros observed previous Hlookup Hsem; exists previous; split; [exact Hlookup|]; split; reflexivity.
  - intros observed previous Hlookup Hsem.
    assert (Hdifferent : observed <> eid).
    { eapply (tmr_task_private_live_event_disjoint sg entry.(TskState) entry.(EventState)
        eid allocation observed previous
        ((store_map (published_queue_node_rep sg entry.(EventState)) entry.(EventState).(inUsedEventStates) **
          (qcb_storage_rep sg qid (qcb_initialize qcb_image start size) **
            (PtrArray.mixed_full start size slots ** store_free_queue_list sg free))) **
          UCOS2_raw_rep_missing_event_queue sg entry ** frame) h).
      - exact Hlookup.
      - assert (Hopen : QueueCreationComponent.queue_creation_publication_owner sg entry free eid allocation
          qid qcb_image start size slots ** frame |--
          event_private_storage_rep sg eid allocation **
          (event_raw_rep sg entry.(TskState) entry.(EventState) **
            ((store_map (published_queue_node_rep sg entry.(EventState)) entry.(EventState).(inUsedEventStates) **
              (qcb_storage_rep sg qid (qcb_initialize qcb_image start size) **
                (PtrArray.mixed_full start size slots ** store_free_queue_list sg free))) **
              UCOS2_raw_rep_missing_event_queue sg entry ** frame))).
        { unfold QueueCreationComponent.queue_creation_publication_owner; entailer!. }
        exact (Hopen h H3). }
    exists previous; split; [|split; reflexivity].
    unfold mutex_query_lookup; cbn [replace_EventS EventState queue_publish event_publish inUsedEventStates].
    rewrite kernel_map_set_other by exact Hdifferent; exact Hlookup.
Qed.

Lemma tmr_task_install_segment_preserves_live_sem :
  forall environment local sg before heap input stopped after heap' output,
  InstallComponent.task_install_c_step environment local sg before heap input stopped after heap' output ->
  tmr_task_live_sem_identity before after.
Proof.
  intros environment local sg before heap input stopped after heap' output Hstep.
  destruct Hstep as [frame call before_heap after_heap sp Hactual [Hsource Hcompletion]].
  destruct (os_sched_install_client_state_frame environment.(task_stack_call_external)
    call.(InstallComponent.task_install_fields_context) call.(InstallComponent.task_install_fields_outgoing)
    call.(InstallComponent.task_install_fields_incoming) call.(InstallComponent.task_install_fields_resumed)
    sg call.(InstallComponent.task_install_fields_entry) (InstallComponent.task_install_fields_current call) Hsource)
    as [Hnodes [Hlife [Hevent Hrest]]].
  apply tmr_task_event_state_eq_preserves_live_sem; exact Hevent.
Qed.

Lemma tmr_task_paired_primitive_preserves_live_sem :
  forall environment critical sg before heap input stopped after heap' output,
  PrimitiveComponent.flag_pend_task_primitive_c_step environment critical sg
    before heap input stopped after heap' output -> tmr_task_live_sem_identity before after.
Proof.
  intros environment critical sg before heap input stopped after heap' output Hstep.
  destruct Hstep.
  - destruct H; apply tmr_task_event_state_eq_preserves_live_sem; reflexivity.
  - apply tmr_task_event_state_eq_preserves_live_sem; reflexivity.
  - apply tmr_task_event_state_eq_preserves_live_sem; reflexivity.
Qed.

Lemma tmr_task_program_named_source_preserves_live_sem :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (step : kernel_program_c_step environment critical sg observer origin
      state before input stopped current after output),
  kernel_program_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output step ->
  tmr_task_live_sem_identity state current.
Proof.
  intros environment critical sg observer origin event_observer state before input stopped current after output step Hsource.
  destruct Hsource.
  - apply tmr_task_wake_source_preserves_live_sem with sg.
    eapply WakeComponent.kernel_wake_c_segment_source; exact Hsegment.
  - apply tmr_task_status_source_preserves_live_sem with sg.
    eapply StatusComponent.kernel_status_c_segment_code; exact Hsegment.
  - apply tmr_task_task_creation_source_preserves_live_sem with sg.
    eapply CreationComponent.kernel_task_creation_c_segment_source; exact Hsegment.
  - eapply tmr_task_event_creation_segment_preserves_live_sem; exact Hsegment.
  - eapply tmr_task_queue_creation_segment_preserves_live_sem; exact Hsegment.
Qed.

Lemma tmr_task_change_priority_preserves_live_sem : forall sg state tid old oldprio newprio,
  tmr_task_live_sem_identity state (task_change_priority_state sg state tid old oldprio newprio).
Proof.
  intros sg state tid old oldprio newprio eid previous Hlookup Hsem.
  unfold mutex_query_lookup in *.
  cbn [task_change_priority_state replace_SchedS replace_EventS EventState].
  unfold task_change_priority_events.
  destruct old.(eventPtr) as [selected|];
    [destruct (state.(EventState).(inUsedEventStates) selected) as [event|] eqn:Hselected|];
    try (exists previous; split; [exact Hlookup|]; split; reflexivity).
  eapply tmr_task_signal_event_update_preserves_identity;
    [exact Hselected|reflexivity|reflexivity|exact Hlookup].
Qed.

Lemma tmr_task_change_priority_critical_preserves_live_sem :
  forall sg requested priority state result current,
  task_change_prio_critical sg requested priority state result current ->
  tmr_task_live_sem_identity state current.
Proof.
  intros sg requested priority state result current Hstep.
  unfold task_change_prio_critical in Hstep.
  destruct (state.(TskState).(prioTbl) priority).
  - destruct Hstep as [selected [Hselection Hstep]].
    unfold task_change_prio_selected_effect in Hstep.
    destruct (Z.eqb selected sg.(osLowestPrio));
      [destruct Hstep as [_ ->]; apply tmr_task_live_sem_identity_refl|].
    destruct (state.(TskState).(prioTbl) selected).
    + destruct Hstep as [_ ->]; apply tmr_task_live_sem_identity_refl.
    + destruct Hstep as [_ ->]; apply tmr_task_live_sem_identity_refl.
    + destruct Hstep as [old [_ [_ ->]]]; apply tmr_task_change_priority_preserves_live_sem.
  - destruct Hstep as [_ ->]; apply tmr_task_live_sem_identity_refl.
  - destruct Hstep as [_ ->]; apply tmr_task_live_sem_identity_refl.
Qed.

Lemma tmr_task_critical_source_preserves_live_sem : forall sg call,
  CriticalComponent.kernel_critical_c_source sg call ->
  tmr_task_live_sem_identity (CriticalComponent.kernel_critical_c_entry call)
    (CriticalComponent.kernel_critical_c_returned call).
Proof.
  intros sg [actual|actual] Hsource; cbn in Hsource |- *.
  - destruct Hsource as [error [Hcritical Hcode]].
    eapply tmr_task_change_priority_critical_preserves_live_sem; exact Hcritical.
  - unfold CriticalComponent.mutex_del_critical_fields_observation in Hsource.
    destruct Hsource.
    + destruct H0 as [error [scheduled [Hcritical [Hcode Hrequest]]]].
      destruct (tmr_task_mutex_delete_critical_signal_frame _ _ _ _ _ _ Hcritical) as [_ Hlookup].
      intros eid previous Hprevious Hsem; exists previous; split;
        [eapply Hlookup; eassumption|split; reflexivity].
    + apply tmr_task_live_sem_identity_refl.
Qed.

Lemma tmr_task_mutex_inherit_source_preserves_live_sem : forall sg call,
  PendComponent.mutex_pend_inheritance_c_source sg call ->
  tmr_task_live_sem_identity call.(PendComponent.mutex_pend_inheritance_entry)
    call.(PendComponent.mutex_pend_inheritance_returned).
Proof.
  intros sg call [Hnode [Hnonowner Hstep]].
  unfold mutex_pend_inherit_step in Hstep.
  destruct (mutex_pend_inherit_action sg.(osPrioMutexCeilDis)
    call.(PendComponent.mutex_pend_inheritance_base)
    call.(PendComponent.mutex_pend_inheritance_node).(curPrio)
    call.(PendComponent.mutex_pend_inheritance_waiter)
    call.(PendComponent.mutex_pend_inheritance_ceiling)).
  - rewrite Hstep; apply tmr_task_live_sem_identity_refl.
  - rewrite Hstep; apply tmr_task_event_state_eq_preserves_live_sem; reflexivity.
  - destruct Hstep as [events [Hevents ->]].
    unfold mutex_pend_promoted_events in Hevents.
    destruct (mutex_pend_owner_was_ready call.(PendComponent.mutex_pend_inheritance_entry)
      call.(PendComponent.mutex_pend_inheritance_node)).
    + rewrite Hevents; apply tmr_task_event_state_eq_preserves_live_sem; reflexivity.
    + destruct call.(PendComponent.mutex_pend_inheritance_node).(eventPtr).
      * destruct Hevents as [old [Hget ->]].
        intros eid previous Hlookup Hsem.
        unfold mutex_query_lookup; cbn [replace_EventS EventState].
        eapply tmr_task_signal_wait_list_update_preserves_identity; eassumption.
      * rewrite Hevents; apply tmr_task_event_state_eq_preserves_live_sem; reflexivity.
Qed.

Lemma tmr_task_mutex_post_critical_preserves_live_sem :
  forall sg selected caller state result schedule current,
  mutex_post_critical sg selected caller state result schedule current ->
  tmr_task_live_sem_identity state current.
Proof.
  intros sg selected caller state result schedule current Hstep; destruct Hstep.
  - apply tmr_task_live_sem_identity_refl.
  - intros eid previous Hlookup Hsem.
    pose proof (mutex_post_prepare_event_state_eq _ _ _ _ _ H3) as Hevents.
    unfold mutex_query_lookup in *.
    unfold mutex_post_owner_state; cbn [replace_EventS EventState].
    eapply tmr_task_signal_event_update_preserves_identity;
      [rewrite Hevents; exact H|reflexivity|reflexivity|rewrite Hevents; exact Hlookup].
  - pose proof (tmr_task_event_ready_source_preserves_live_sem _ _ _ _ _ _ _ _ H5) as Hwake.
    intros eid previous Hlookup Hsem.
    assert (Hprevious : mutex_query_lookup prepared eid previous).
    { unfold mutex_query_lookup; rewrite (mutex_post_prepare_event_state_eq _ _ _ _ _ H3); exact Hlookup. }
    destruct (Hwake eid previous Hprevious Hsem) as [next [Hnext [Hgeneration Htype]]].
    destruct (tmr_task_signal_event_update_preserves_identity woken.(EventState) selected found
      (mutex_post_owner_event found mutex (Some owner) (Some priority)) eid next
      H6 eq_refl eq_refl Hnext) as [final [Hfinal [Hgeneration' Htype']]].
    exists final; split; [exact Hfinal|]. split; congruence.
Qed.

Lemma tmr_task_delete_prepare_preserves_live_sem : forall state tid old prepared loan,
  task_delete_prepare_single_wait state tid old = Some (prepared, loan) ->
  tmr_task_live_sem_identity state prepared.
Proof.
  intros state tid old prepared loan Hstep.
  unfold task_delete_prepare_single_wait in Hstep.
  destruct old.(eventPtr) as [selected|];
    [destruct (state.(EventState).(inUsedEventStates) selected) as [event|] eqn:Hselected; [|discriminate]|];
    cbn [task_set_event_ptr tcbFlagNode] in Hstep;
    destruct (Z.eqb old.(tcbFlagNode) 0);
    try (destruct (flag.flag_unlink_node state.(FlagState) old.(tcbFlagNode))
      as [[waiter flags]|]; [|discriminate]);
    inversion Hstep; subst prepared;
    intros eid previous Hlookup Hsem;
    unfold mutex_query_lookup; cbn [task_delete_prepare_after_unlink replace_TskS replace_SchedS
      replace_EventS replace_FlagS EventState];
    try (exists previous; split; [exact Hlookup|]; split; reflexivity);
    eapply tmr_task_signal_wait_list_update_preserves_identity; eassumption.
Qed.

Lemma tmr_task_delete_own_segment_preserves_live_sem :
  forall environment critical sg observer origin state before input stopped current after output,
  DeleteComponent.task_delete_own_c_segment environment critical sg observer origin
    state before input stopped current after output -> tmr_task_live_sem_identity state current.
Proof.
  intros environment critical sg observer origin state before input stopped current after output Hstep.
  destruct Hstep as [inputs before_heap prepared_heap Hcontext Hcompleted|capture after_heap Hcontext Hcompleted].
  - destruct Hcompleted as [[Hlive [Hprepare Hprotocol]] Hbefore Hafter].
    change (tmr_task_live_sem_identity inputs.(DeleteComponent.delete_capture_acquired)
      inputs.(DeleteComponent.delete_capture_prepared)).
    eapply tmr_task_delete_prepare_preserves_live_sem; exact Hprepare.
  - apply tmr_task_event_state_eq_preserves_live_sem; reflexivity.
Qed.

Lemma tmr_task_delete_primitive_preserves_live_sem :
  forall environment critical sg state before input stopped current after output,
  DeleteComponent.task_delete_primitive_c_segment environment critical sg
    state before input stopped current after output -> tmr_task_live_sem_identity state current.
Proof.
  intros environment critical sg state before input stopped current after output Hstep.
  destruct Hstep; apply tmr_task_event_state_eq_preserves_live_sem; reflexivity.
Qed.

Lemma tmr_task_builtin_segment_preserves_live_sem :
  forall environment critical local sg state before current after input output,
  BuiltinComponent.kernel_builtin_c_segment environment critical local sg state before current after input output ->
  tmr_task_live_sem_identity state current.
Proof.
  intros environment critical local sg state before current after input output Hsegment; destruct Hsegment.
  - destruct operation; apply tmr_task_event_state_eq_preserves_live_sem; reflexivity.
  - apply tmr_task_event_state_eq_preserves_live_sem; reflexivity.
  - pose proof (BuiltinComponent.kernel_irq_transfer_c_completion_source environment critical sg
      handler saved entry transfer frame before after H) as Htransfer.
    destruct (BuiltinComponent.os_int_exit_configured_transfer_state_frame environment sg handler entry transfer Htransfer)
      as [Hnodes [Hlife [Hevent Hrest]]].
    apply tmr_task_event_state_eq_preserves_live_sem; exact Hevent.
Qed.

Lemma tmr_task_program_remaining_source_preserves_live_sem :
  forall environment critical sg observer origin state before input stopped current after output
    (step : kernel_program_c_step environment critical sg observer origin
      state before input stopped current after output),
  kernel_program_c_step_remaining_source environment critical sg observer origin
    state before input stopped current after output step -> tmr_task_live_sem_identity state current.
Proof.
  intros environment critical sg observer origin state before input stopped current after output step Hsource.
  destruct Hsource.
  - destruct Hsegment as [Hcompletion [Hphysical [Hcode Hpacket]]].
    eapply tmr_task_critical_source_preserves_live_sem; exact Hcode.
  - eapply tmr_task_builtin_segment_preserves_live_sem; exact Hsegment.
  - eapply tmr_task_install_segment_preserves_live_sem; exact Hsegment.
  - destruct Hsegment as [Hcode Hpre Hpost].
    eapply tmr_task_mutex_inherit_source_preserves_live_sem; exact Hcode.
  - destruct Hsegment as [[Hcaller Hcode] Hpre Hpost].
    eapply tmr_task_mutex_post_critical_preserves_live_sem; exact Hcode.
  - eapply tmr_task_delete_primitive_preserves_live_sem; exact Hsegment.
  - eapply tmr_task_paired_primitive_preserves_live_sem; exact Hsegment.
  - eapply tmr_task_delete_own_segment_preserves_live_sem; exact Hsegment.
Qed.

Lemma tmr_task_program_c_step_source_preserves_live_sem :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (step : kernel_program_c_step environment critical sg observer origin
      state before input stopped current after output),
  kernel_program_c_step_call_source environment critical sg observer origin event_observer
    state before input stopped current after output step -> tmr_task_live_sem_identity state current.
Proof.
  intros environment critical sg observer origin event_observer state before input stopped current after output step [Hnamed|Hremaining].
  - eapply tmr_task_program_named_source_preserves_live_sem; exact Hnamed.
  - eapply tmr_task_program_remaining_source_preserves_live_sem; exact Hremaining.
Qed.

(** Induction consumes the source predicate of this exact run. Its middle
    states, heaps and resource implications remain those of that run. *)
Lemma tmr_task_program_c_sequence_source_preserves_live_sem :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_c_step environment critical sg observer origin)
      state before input stopped current after output),
  kernel_program_c_sequence_call_source environment critical sg observer origin event_observer
    state before input stopped current after output run -> tmr_task_live_sem_identity state current.
Proof.
  intros environment critical sg observer origin event_observer state before input stopped current after output run Hsource.
  eapply (kernel_c_sequence_source_relation
    (kernel_program_c_step environment critical sg observer origin)
    (kernel_program_c_step_call_source environment critical sg observer origin event_observer)
    tmr_task_live_sem_identity).
  - apply tmr_task_live_sem_identity_refl.
  - apply tmr_task_live_sem_identity_trans.
  - intros; eapply tmr_task_program_c_step_source_preserves_live_sem; eassumption.
  - exact Hsource.
Qed.

Lemma tmr_task_return_c_step_source_preserves_live_sem :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (step : SelectedReturnPrimitive.kernel_program_return_c_step environment critical sg observer origin
      state before input stopped current after output),
  SelectedCompletionSource.kernel_program_return_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output step -> tmr_task_live_sem_identity state current.
Proof.
  intros environment critical sg observer origin event_observer state before input stopped current after output step Hsource.
  destruct Hsource.
  - eapply tmr_task_program_c_step_source_preserves_live_sem; exact H.
  - destruct (SelectedReturnPrimitive.kernel_selected_return_c_step_state_stop _ _ _ _ _ _ _ _ Hstep) as [-> ->].
    apply tmr_task_live_sem_identity_refl.
  - eapply tmr_task_install_segment_preserves_live_sem.
    exact (@InstallComponent.TaskInstallCStep environment local sg frame call before installed sp actual complete).
  - apply tmr_task_event_state_eq_preserves_live_sem; reflexivity.
Qed.

Lemma tmr_task_suspend_step_preserves_live_sem :
  forall sg request priority state result self current,
  task_suspend_step sg request priority state result self current ->
  tmr_task_live_sem_identity state current.
Proof.
  intros sg request priority state result self current [error [Herror Hstep]].
  destruct Hstep as [Hpriority Hstep].
  destruct (Z.eqb (task_suspend_resolved_priority sg request priority) sg.(osTaskIdlePrio)).
  - destruct Hstep as [_ ->]; apply tmr_task_live_sem_identity_refl.
  - destruct (state.(TskState).(prioTbl) (task_suspend_resolved_priority sg request priority)).
    + destruct Hstep as [_ ->]; apply tmr_task_live_sem_identity_refl.
    + destruct Hstep as [_ ->]; apply tmr_task_live_sem_identity_refl.
    + destruct Hstep as [old [_ [_ ->]]].
      apply tmr_task_event_state_eq_preserves_live_sem; reflexivity.
Qed.

Lemma tmr_task_selected_c_step_source_preserves_live_sem :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (step : SelectedCProgram.kernel_program_selected_c_step environment critical sg observer origin
      state before input stopped current after output),
  SelectedCSource.kernel_program_selected_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output step -> tmr_task_live_sem_identity state current.
Proof.
  intros environment critical sg observer origin event_observer state before input stopped current after output step Hsource.
  destruct Hsource.
  - eapply tmr_task_return_c_step_source_preserves_live_sem; exact H.
  - destruct step.
    destruct (BuiltinComponent.os_int_exit_configured_transfer_state_frame environment sg handler entry transfer source)
      as [Hnodes [Hlife [Hevent Hrest]]].
    apply tmr_task_event_state_eq_preserves_live_sem; exact Hevent.
  - destruct step as [saved_local caller saved call frame before after [[Hread Hcode] Hinput Houtput]].
    eapply tmr_task_suspend_step_preserves_live_sem; exact Hcode.
Qed.

Lemma tmr_task_selected_c_sequence_source_preserves_live_sem :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (run : kernel_c_sequence (SelectedCProgram.kernel_program_selected_c_step environment critical sg observer origin)
      state before input stopped current after output),
  SelectedCSource.kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    state before input stopped current after output run -> tmr_task_live_sem_identity state current.
Proof.
  intros environment critical sg observer origin event_observer state before input stopped current after output run Hsource.
  eapply (kernel_c_sequence_source_relation
    (SelectedCProgram.kernel_program_selected_c_step environment critical sg observer origin)
    (SelectedCSource.kernel_program_selected_c_step_source environment critical sg observer origin event_observer)
    tmr_task_live_sem_identity).
  - apply tmr_task_live_sem_identity_refl.
  - apply tmr_task_live_sem_identity_trans.
  - intros; eapply tmr_task_selected_c_step_source_preserves_live_sem; eassumption.
  - exact Hsource.
Qed.
