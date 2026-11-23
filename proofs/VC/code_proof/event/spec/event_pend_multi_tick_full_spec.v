Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Ucos2Verify.VC.code.event.spec.event_pend_multi_resume_source_spec.
Require Import Ucos2Verify.lib.tick Ucos2Verify.lib.event_registration
  Ucos2Verify.lib.event_registration_steps Ucos2Verify.lib.cross_module_invariants
  Ucos2Verify.lib.kernel_names Ucos2Verify.lib.task_stack Ucos2Verify.lib.mutex.
Import ListNotations TaskStateDef EventStateDef SchedStateDef.
Local Open Scope Z_scope.

(** Tick retains the live registrations and original array. Expiration
    clears PEND_ANY but keeps the MULTI marker, so its new source phase is
    timeout-linked rather than already unlinked or ordinary quiescence. *)
Lemma event_pend_multi_tick_preserves_linked_wait_phase : forall task kind,
  task_multi_linked_wait_phase task kind ->
  task_multi_linked_wait_phase (tick_task_update task) kind.
Proof.
  intros task kind Hphase; pose proof Hphase as Horiginal.
  destruct Hphase as [Hkind [Hsingle [Harray [Hrdy [mask [suspended [Hrange [Hbits Hphase]]]]]]]].
  change (task_status.encode_task_status task.(stat) = encode_multi_wait_status mask suspended) in Hbits.
  unfold tick_task_update; destruct (Z.eqb task.(dly) 0) eqn:Hzero; [exact Horiginal|].
  apply Z.eqb_neq in Hzero.
  destruct (Z.eqb (task.(dly) - 1) 0) eqn:Hlast.
  - apply Z.eqb_eq in Hlast.
    destruct Hphase as [[Hmask Hpend]|[_ [_ Hdelay]]]; [|contradiction].
    assert (Hpositive : 0 < mask).
    { pose proof (task_pend_mask_in_range kind) as Hkindrange.
      destruct (Z.eq_dec mask 0) as [->|Hnot]; [cbn in Hmask; lia|lia]. }
    assert (Htimeout : task_status_timeout (task_status.encode_task_status task.(stat)) =
      (encode_multi_wait_status 0 suspended, PendTimeout)).
    { rewrite Hbits; apply task_status_timeout_multi; lia. }
    split; [exact Hkind|]. split; [exact Hsingle|]. split; [exact Harray|]. split; [exact Hrdy|].
    exists 0, suspended; split; [lia|]. split.
    + change (task_status.encode_task_status (task_status_after_timeout task.(stat)) =
        encode_multi_wait_status 0 suspended).
      rewrite task_status_after_timeout_encoding, Htimeout; reflexivity.
    + right; split; [reflexivity|]. split; [|exact Hlast].
      change (snd (task_status_timeout (task_status.encode_task_status task.(stat))) = PendTimeout).
      rewrite Htimeout; reflexivity.
  - destruct Hphase as [Hpending|[_ [_ Hdelay]]]; [|contradiction].
    split; [exact Hkind|]. split; [exact Hsingle|]. split; [exact Harray|]. split; [exact Hrdy|].
    exists mask, suspended; split; [exact Hrange|]. split; [exact Hbits|left; exact Hpending].
Qed.

Lemma event_pend_multi_tick_task_cross_frame : forall sg state tid task
    (waiting_before waiting_after : Prop),
  state.(TskState).(inUsedTaskStates) tid = Some task -> waiting_after ->
  cross_module_consistency_with_wait sg state waiting_before ->
  cross_module_consistency_with_wait sg
    (replace_TskS (glob_task_set_usedtask state.(TskState) tid (tick_task_update task)) state)
    waiting_after.
Proof.
  intros sg state tid task waiting_before waiting_after Htask Hwaiting
    [Htable [Hsnapshot [_ [Hprotocol [Hunique [Hflag Htimer]]]]]].
  pose proof (tick_task_preserves_non_timeout_fields task) as Hfields; cbn zeta in Hfields.
  assert (Hid : (tick_task_update task).(taskID) = task.(taskID)) by tauto.
  assert (Hgen : (tick_task_update task).(taskGeneration) = task.(taskGeneration)) by tauto.
  assert (Hprio : (tick_task_update task).(curPrio) = task.(curPrio)) by tauto.
  split; [eapply task_mutex_priotbl_consistency_update_task; eassumption|].
  split; [eapply mutex_owner_snapshot_update_task; eassumption|].
  split; [exact Hwaiting|]. split; [exact Hprotocol|]. split; [exact Hunique|].
  split; [apply tick_task_preserves_flag_waiter_consistency; assumption|exact Htimer].
Qed.

Lemma event_pend_multi_tick_preserves_registered_wait_phase : forall task eid kind,
  task_registered_wait_phase task eid kind ->
  task_registered_wait_phase (tick_task_update task) eid kind.
Proof.
  intros task eid kind Hphase.
  pose proof (tick_task_preserves_non_timeout_fields task) as Hfields; cbn zeta in Hfields.
  assert (Hsingle : (tick_task_update task).(eventPtr) = task.(eventPtr)) by tauto.
  assert (Harray : (tick_task_update task).(tcbEventMultiPtr) = task.(tcbEventMultiPtr)) by tauto.
  assert (Hids : (tick_task_update task).(eventMultiWaitEvents) = task.(eventMultiWaitEvents)) by tauto.
  unfold task_registered_wait_phase; rewrite Hsingle, Harray, Hids.
  destruct Hphase as [[Hptr [Hzero Hphase]]|[Hin Hphase]].
  - left; split; [exact Hptr|]. split; [exact Hzero|apply tick_preserves_linked_phase; exact Hphase].
  - right; split; [exact Hin|apply event_pend_multi_tick_preserves_linked_wait_phase; exact Hphase].
Qed.

Lemma event_pend_multi_tick_preserves_registration : forall sg tasks events tid task,
  tasks.(inUsedTaskStates) tid = Some task ->
  event_registration_consistency sg tasks events ->
  event_registration_consistency sg (glob_task_set_usedtask tasks tid (tick_task_update task)) events.
Proof.
  intros sg tasks events tid task Htask Hregistration.
  eapply event_registration_update_task; [exact Htask| | | |exact Hregistration].
  - unfold tick_task_update; destruct (Z.eqb task.(dly) 0); reflexivity.
  - intro eid; unfold task_event_registered, tick_task_update;
      destruct (Z.eqb task.(dly) 0); reflexivity.
  - apply event_pend_multi_tick_preserves_registered_wait_phase.
Qed.

Lemma event_pend_multi_tick_expired_source_ready : forall task,
  task.(dly) <> 0 -> (tick_task_update task).(dly) = 0 ->
  task_is_suspended (tick_task_update task).(stat) = false ->
  task_source_ready (tick_task_update task).
Proof.
  intros task Hnonzero Hdelay Hsuspended; split; [exact Hsuspended|].
  apply task_resume_ready_test_iff; split; [|exact Hdelay].
  unfold tick_task_update in Hdelay |- *.
  rewrite (proj2 (Z.eqb_neq _ _) Hnonzero) in Hdelay |- *; cbn [dly] in Hdelay.
  rewrite Hdelay, Z.eqb_refl; cbn [stat].
  unfold task.encode_task_status; rewrite task_status_after_timeout_encoding.
  pose proof (task_status_timeout_clears_pending (task_status.encode_task_status task.(stat))) as Hclear.
  unfold task_status_has_pending in Hclear; apply Bool.negb_false_iff in Hclear.
  apply Z.eqb_eq in Hclear; exact Hclear.
Qed.

Lemma event_pend_multi_tick_preserves_registered_ready : forall sg state tid task,
  task_in_range sg state.(TskState) ->
  state.(TskState).(inUsedTaskStates) tid = Some task ->
  sched_registered_ready_in_range sg state.(TskState) state.(SchedState) ->
  sched_registered_ready_in_range sg (tick_task_step sg tid task state).(TskState)
    (tick_task_step sg tid task state).(SchedState).
Proof.
  intros sg state tid task Htasks Htask Hready.
  pose proof Hready as [Hstructure [Hforward Hback]].
  pose proof (tick_task_preserves_non_timeout_fields task) as Hfields; cbn zeta in Hfields.
  assert (Hpriority : (tick_task_update task).(curPrio) = task.(curPrio)) by tauto.
  assert (Hunique : task_priority_unique state.(TskState))
    by (unfold task_in_range in Htasks; tauto).
  assert (Hrange : task_priority_in_range sg task.(curPrio)).
  { destruct Htasks as (_ & _ & _ & _ & _ & _ & _ & Hrange & _); eapply Hrange; exact Htask. }
  unfold tick_task_step; destruct (Z.eqb task.(dly) 0) eqn:Hzero; [exact Hready|].
  apply Z.eqb_neq in Hzero.
  assert (Hnotready : ~ In tid state.(SchedState).(readyList)).
  { intro Hin; destruct (Hforward tid task Hin Htask) as [[_ Hsource]|[_ [Hdelay _]]];
      [apply task_resume_ready_test_iff in Hsource; tauto|contradiction]. }
  destruct (Z.eqb (tick_task_update task).(dly) 0) eqn:Hexpired.
  - apply Z.eqb_eq in Hexpired.
    split.
    + eapply sched_ready_structure_update_task; [exact Htask|exact Hpriority|].
      eapply sched_wake_by_status_preserves_structure; eassumption.
    + split.
      * intros member node Hin Hnode.
        apply sched_wake_by_status_membership in Hin.
        cbn [replace_TskS replace_SchedS TskState glob_task_set_usedtask inUsedTaskStates] in Hnode.
        destruct (Z.eqb member tid) eqn:E.
        -- apply Z.eqb_eq in E; subst member; injection Hnode as <-.
           destruct Hin as [Hin|[_ Hsuspended]]; [contradiction|].
           left; apply event_pend_multi_tick_expired_source_ready; assumption.
        -- destruct Hin as [Hin|[Hequal _]]; [eapply Hforward; eassumption|].
           apply Z.eqb_neq in E; contradiction.
      * intros member node Hnode Hsource.
        apply sched_wake_by_status_membership.
        cbn [replace_TskS replace_SchedS TskState glob_task_set_usedtask inUsedTaskStates] in Hnode.
        destruct (Z.eqb member tid) eqn:E.
        -- apply Z.eqb_eq in E; subst member; injection Hnode as <-.
           right; split; [reflexivity|exact (proj1 Hsource)].
        -- left; eapply Hback; eassumption.
  - apply Z.eqb_neq in Hexpired.
    split.
    + eapply sched_ready_structure_update_task; [exact Htask|exact Hpriority|exact Hstructure].
    + split.
      * intros member node Hin Hnode.
        cbn [replace_TskS replace_SchedS TskState glob_task_set_usedtask inUsedTaskStates] in Hnode.
        destruct (Z.eqb member tid) eqn:E.
        -- apply Z.eqb_eq in E; subst member; contradiction.
        -- eapply Hforward; eassumption.
      * intros member node Hnode [Hsuspended Hsource].
        cbn [replace_TskS replace_SchedS TskState glob_task_set_usedtask inUsedTaskStates] in Hnode.
        destruct (Z.eqb member tid) eqn:E.
        -- injection Hnode as <-; apply task_resume_ready_test_iff in Hsource; tauto.
        -- eapply Hback; [exact Hnode|]. split; [|exact Hsource].
           exact Hsuspended.
Qed.

(** One actual protected loop body. The clock, hook, cursor/idle tests and
    outer Restore remain separate source cuts. No single-wait-only or
    Multi-disabled invariant is substituted for this full-profile one. *)
Lemma event_pend_multi_tick_step_preserves_full_state : forall sg state tid task,
  UCOS2_full_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some task ->
  UCOS2_full_state_inv sg (tick_task_step sg tid task state).
Proof.
  intros sg state tid task Hvalid Htask.
  destruct Hvalid as [Hprofile [Htasks [[Hready Hmetadata] [Hevents [Hcross
    [Hidle [Hbits [Hflag [Hmemory [Htimer [Hstats [Hcontrol [Hnames
    [Hreferences [Hstacks Hpending]]]]]]]]]]]]]]].
  pose proof (tick_task_preserves_non_timeout_fields task) as Hfields; cbn zeta in Hfields.
  assert (Hprio : (tick_task_update task).(curPrio) = task.(curPrio)) by tauto.
  pose proof (event_pend_multi_tick_preserves_registered_ready sg state tid task Htasks Htask Hready)
    as HreadyAfter.
  pose proof (tick_task_step_preserves_task_in_range sg tid task state Htasks Htask) as HtasksAfter.
  pose proof (f_equal EventState (tick_task_step_non_task_sched_state_eq sg tid task state)) as HeventEq.
  cbn [replace_TskS replace_SchedS EventState] in HeventEq.
  assert (HeventsAfter : event_registered_in_range sg
      (tick_task_step sg tid task state).(TskState) (tick_task_step sg tid task state).(EventState)).
  { rewrite tick_task_step_task_state_eq by exact Htask; rewrite HeventEq.
    eapply event_registered_in_range_update_task;
      [exact Htask|exact Hprio| |exact Hevents].
    apply event_pend_multi_tick_preserves_registered_wait_phase. }
  assert (Hregistration : event_registration_consistency sg state.(TskState) state.(EventState))
    by (destruct Hcross as [_ [_ [Hregistration _]]]; exact Hregistration).
  pose proof (event_pend_multi_tick_preserves_registration sg state.(TskState) state.(EventState)
    tid task Htask Hregistration) as HregisteredAfter.
  assert (HcrossUpdated : cross_module_registration_consistency sg
      (replace_TskS (glob_task_set_usedtask state.(TskState) tid (tick_task_update task)) state)).
  { unfold cross_module_registration_consistency.
    eapply event_pend_multi_tick_task_cross_frame; eassumption. }
  assert (HcrossAfter : cross_module_registration_consistency sg (tick_task_step sg tid task state)).
  { unfold tick_task_step; destruct (Z.eqb task.(dly) 0); [exact Hcross|].
    destruct (Z.eqb (tick_task_update task).(dly) 0); [|exact HcrossUpdated].
    change (cross_module_registration_consistency sg
      (replace_SchedS (sched_wake_by_status sg state.(TskState) state.(SchedState)
        tid (encode_task_status (tick_task_update task).(stat)))
        (replace_TskS (glob_task_set_usedtask state.(TskState) tid (tick_task_update task)) state))).
    apply cross_module_registration_sched_frame; [|exact HcrossUpdated].
    apply sched_wake_by_status_running_eq. }
  assert (HidleAfter : (tick_task_step sg tid task state).(SchedState).(isRunning) = true ->
    task_idle_tail sg (tick_task_step sg tid task state).(TskState)).
  { rewrite tick_task_step_task_state_eq by exact Htask.
    intros Hrunning; eapply task_update_preserves_idle_tail; [exact Htask|exact Hprio|].
    apply Hidle; unfold tick_task_step, sched_wake_by_status in Hrunning.
    destruct (Z.eqb task.(dly) 0) in Hrunning;
      [exact Hrunning|destruct (Z.eqb (tick_task_update task).(dly) 0) in Hrunning;
        [destruct (task_status_is_suspended _) in Hrunning|]; exact Hrunning]. }
  assert (HbitsAfter : task_reserved_bits_clear sg (tick_task_step sg tid task state).(TskState)).
  { rewrite tick_task_step_task_state_eq by exact Htask.
    apply task_reserved_bits_clear_update_task; [exact Hbits|].
    apply tick_task_preserves_reserved_bits_clear; exact (Hbits tid task Htask). }
  assert (HreferencesAfter : kernel_names_valid sg (tick_task_step sg tid task state)).
  { unfold tick_task_step; destruct (Z.eqb task.(dly) 0); [exact Hreferences|].
    destruct (Z.eqb (tick_task_update task).(dly) 0).
    all: assert (Hname : (tick_task_update task).(tcbTaskName) = task.(tcbTaskName)) by tauto.
    all: eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
    all: first [eapply task_update_name_references; [exact Htask|exact Hname]|intros; assumption]. }
  assert (HstacksAfter : parked_stacks_consistent
      (tick_task_step sg tid task state).(TskState)
      (tick_task_step sg tid task state).(TskState).(parkedTaskStacks)).
  { rewrite tick_task_step_task_state_eq by exact Htask; cbn [glob_task_set_usedtask parkedTaskStacks].
    eapply parked_stacks_consistent_update_task; [exact Htask| | | |exact Hstacks]; tauto. }
  split; [exact Hprofile|]. split; [exact HtasksAfter|].
  split; [split; [exact HreadyAfter|]|].
  - unfold tick_task_step, sched_wake_by_status;
      destruct (Z.eqb task.(dly) 0); [exact Hmetadata|];
      destruct (Z.eqb (tick_task_update task).(dly) 0);
      [destruct (task_status_is_suspended _)|]; exact Hmetadata.
  - split; [exact HeventsAfter|]. split; [exact HcrossAfter|].
    split; [exact HidleAfter|]. split; [exact HbitsAfter|].
    unfold tick_task_step in HreferencesAfter, HstacksAfter |- *;
      destruct (Z.eqb task.(dly) 0); [|destruct (Z.eqb (tick_task_update task).(dly) 0)];
      exact (conj Hflag (conj Hmemory (conj Htimer (conj Hstats
        (conj Hcontrol (conj Hnames (conj HreferencesAfter (conj HstacksAfter Hpending)))))))).
Qed.
