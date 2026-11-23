Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Require Export Ucos2Verify.VC.code.event.spec.event_pend_multi_wake_source_spec.
Require Import Ucos2Verify.lib.atomic_ops_lib Ucos2Verify.lib.event_registration
  Ucos2Verify.lib.event_registration_steps Ucos2Verify.lib.cross_module_invariants
  Ucos2Verify.lib.kernel_names Ucos2Verify.lib.task_stack Ucos2Verify.lib.mutex.
Import ListNotations TaskStateDef EventStateDef SchedStateDef.
Local Open Scope Z_scope.

Lemma event_pend_multi_wake_status_mask : forall mask suspended kind,
  0 <= mask < 8 -> (kind = PendSem \/ kind = PendMbox \/ kind = PendQ) ->
  exists remaining, 0 <= remaining < 8 /\
    task_status_clear_wait (encode_multi_wait_status mask suspended) (task_pend_mask kind) =
    encode_multi_wait_status remaining suspended.
Proof.
  intros mask suspended kind Hmask Hkind.
  exists (Z.land mask (Z.lxor (task_pend_mask kind) 7)).
  assert (mask = 0 \/ mask = 1 \/ mask = 2 \/ mask = 3 \/
    mask = 4 \/ mask = 5 \/ mask = 6 \/ mask = 7) as Hcases by lia.
  repeat destruct Hcases as [Hcases|Hcases]; subst mask;
    destruct Hkind as [Hkind|[Hkind|Hkind]]; subst kind;
    destruct suspended; split; vm_compute; intuition congruence.
Qed.

Lemma event_pend_multi_wake_selected_phase : forall sg tasks events tid task selected node kind,
  event_registration_consistency sg tasks events ->
  tasks.(inUsedTaskStates) tid = Some task -> task.(tcbEventMultiPtr) <> 0 ->
  events.(inUsedEventStates) selected = Some node -> In tid node.(waitList) ->
  event_type_to_pend_type node.(eventType) = Some kind ->
  In selected task.(eventMultiWaitEvents) /\ task_multi_linked_wait_phase task kind.
Proof.
  intros sg tasks events tid task selected node kind [Hentries _]
    Htask Hlinked Hnode Hin Hkind.
  destruct (Hentries selected node Hnode) as [_ Hentry]; rewrite Hkind in Hentry.
  destruct (Hentry tid Hin) as [found [Hfound Hphase]].
  assert (found = task) by congruence; subst found.
  destruct Hphase as [[_ [Hzero _]]|Hmulti]; [contradiction|exact Hmulti].
Qed.

Lemma event_pend_multi_wake_registered_ready : forall task kind message result selected,
  task_multi_linked_wait_phase task kind -> task_is_suspended task.(stat) = false ->
  (result = PendOK \/ result = PendAbort) ->
  task_multi_woken_ready (task_multi_wake task kind message result selected).
Proof.
  intros task kind message result selected
    [Hkind [Hsingle [Hlinked [Hrdy [mask [suspended [Hrange [Hbits Hphase]]]]]]]]
    Hsuspended Hresult.
  change (task_status.encode_task_status task.(stat) = encode_multi_wait_status mask suspended) in Hbits.
  assert (HsuspendedEq : suspended = false).
  { pose proof (proj1 (proj2 (encode_multi_wait_status_observations mask suspended Hrange))) as H.
    unfold task_is_suspended in Hsuspended; rewrite Hbits, H in Hsuspended; exact Hsuspended. }
  subst suspended.
  destruct (event_pend_multi_wake_status_mask mask false kind Hrange Hkind)
    as [remaining [Hremaining Hafter]].
  split.
  - change (task_is_suspended (task_clear_pending_status task.(stat) kind) = false).
    rewrite task_clear_pending_status_preserves_suspension; exact Hsuspended.
  - split; [reflexivity|]. split; [reflexivity|]. split; [discriminate|].
    split; [exact Hresult|]. exists remaining; split; [exact Hremaining|].
    change (task_status.encode_task_status (task_clear_pending_status task.(stat) kind) =
      encode_multi_wait_status remaining false).
    rewrite task_clear_pending_status_encoding, Hbits; exact Hafter.
Qed.

Lemma event_pend_multi_wake_preserves_registered_ready :
  forall sg tasks sched tid task selected kind message result,
  task_priority_unique tasks -> tasks.(inUsedTaskStates) tid = Some task ->
  task_priority_in_range sg task.(curPrio) -> task_multi_linked_wait_phase task kind ->
  (result = PendOK \/ result = PendAbort) ->
  sched_registered_ready_in_range sg tasks sched ->
  sched_registered_ready_in_range sg
    (glob_task_set_usedtask tasks tid (task_multi_wake task kind message result selected))
    (sched_wake_by_status sg tasks sched tid
      (encode_task_status (task_multi_wake task kind message result selected).(stat))).
Proof.
  intros sg tasks sched tid task selected kind message result Hunique Htask Hpriority Hphase Hresult
    [Hstructure [Hforward Hback]].
  assert (Hsusp : task_status_is_suspended
    (encode_task_status (task_multi_wake task kind message result selected).(stat)) =
    task_is_suspended task.(stat)).
  { change (task_is_suspended (task_clear_pending_status task.(stat) kind) =
      task_is_suspended task.(stat)).
    apply task_clear_pending_status_preserves_suspension. }
  split.
  - eapply sched_ready_structure_update_task; [exact Htask|reflexivity|].
    eapply sched_wake_by_status_preserves_structure; eassumption.
  - split.
    + intros member node Hin Hnode.
      apply sched_wake_by_status_membership in Hin; rewrite Hsusp in Hin.
      cbn [glob_task_set_usedtask inUsedTaskStates] in Hnode.
      destruct (Z.eqb member tid) eqn:E.
      * apply Z.eqb_eq in E; subst member; injection Hnode as <-.
        right; apply event_pend_multi_wake_registered_ready; [exact Hphase| |exact Hresult].
        destruct Hin as [Hin|[_ Hin]]; [|exact Hin].
        destruct (Hforward tid task Hin Htask) as [[H _]|[H _]]; exact H.
      * destruct Hin as [Hin|[Hmember _]]; [eapply Hforward; eassumption|].
        apply Z.eqb_neq in E; contradiction.
    + intros member node Hnode Hready.
      apply sched_wake_by_status_membership; rewrite Hsusp.
      cbn [glob_task_set_usedtask inUsedTaskStates] in Hnode.
      destruct (Z.eqb member tid) eqn:E.
      * apply Z.eqb_eq in E; subst member; injection Hnode as <-.
        right; split; [reflexivity|].
        destruct Hready as [Hready _].
        change (task_is_suspended (task_clear_pending_status task.(stat) kind) = false) in Hready.
        rewrite task_clear_pending_status_preserves_suspension in Hready; exact Hready.
      * left; eapply Hback; eassumption.
Qed.

Lemma event_pend_multi_wake_task_cross_frame : forall sg state tid task kind message result selected
    (waiting_before waiting_after : Prop),
  state.(TskState).(inUsedTaskStates) tid = Some task -> task.(tcbFlagNode) = 0 ->
  task_multi_linked_wait_phase task kind -> waiting_after ->
  cross_module_consistency_with_wait sg state waiting_before ->
  cross_module_consistency_with_wait sg
    (replace_TskS (glob_task_set_usedtask state.(TskState) tid
      (task_multi_wake task kind message result selected)) state) waiting_after.
Proof.
  intros sg state tid task kind message result selected waiting_before waiting_after
    Htask Hflag [Hkind Hphase] Hafter
    [Htable [Hsnapshot [_ [Hprotocol [Hunique [Hflags Htimer]]]]]].
  split.
  - eapply task_mutex_priotbl_consistency_update_task; [exact Htask|reflexivity|exact Htable].
  - split; [eapply mutex_owner_snapshot_update_task; eassumption|].
    split; [exact Hafter|]. split; [exact Hprotocol|]. split; [exact Hunique|].
    split; [|exact Htimer].
    eapply task_flag_waiter_consistency_update_unregistered_task;
      [exact Htask|exact Hflag|exact Hflag| |exact Hflags].
    destruct Hphase as [_ [_ [_ [mask [suspended [Hrange [Hbits _]]]]]]].
    change (task_status.encode_task_status task.(stat) = encode_multi_wait_status mask suspended) in Hbits.
    change (task_non_suspension_bits (task_clear_pending_status task.(stat) kind) <>
      task_pend_mask PendFlag).
    unfold task_non_suspension_bits; rewrite task_clear_pending_status_encoding, Hbits.
    assert (mask = 0 \/ mask = 1 \/ mask = 2 \/ mask = 3 \/
      mask = 4 \/ mask = 5 \/ mask = 6 \/ mask = 7) as Hcases by lia.
    repeat destruct Hcases as [Hcases|Hcases]; subst mask;
      destruct Hkind as [Hkind|[Hkind|Hkind]]; subst kind; destruct suspended; discriminate.
Qed.

(** This is the complete pure Multi wake endpoint, not a post-invariant
    guard. All phase facts are obtained from the actual selected waiter,
    the Event's source kind and the before-state registration invariant.
    No current/ready assertion is demanded for the task being woken. *)
Lemma event_pend_multi_wake_preserves_full_state :
  forall sg state tid task selected node kind message result,
  UCOS2_full_state_inv sg state ->
  state.(TskState).(inUsedTaskStates) tid = Some task -> task.(tcbEventMultiPtr) <> 0 ->
  state.(EventState).(inUsedEventStates) selected = Some node -> In tid node.(waitList) ->
  event_type_to_pend_type node.(eventType) = Some kind ->
  (result = PendOK \/ result = PendAbort) ->
  UCOS2_full_state_inv sg
    (event_multi_wake_state sg state tid task selected kind message result
      (event_multi_remove_waiters state.(EventState) tid (selected :: task.(eventMultiWaitEvents)))).
Proof.
  intros sg state tid task selected node kind message result Hvalid Htask Hlinked Hnode Hin Hkind Hresult.
  pose proof Hvalid as [Hprofile [Htasks [[Hready Hmetadata] [Hevents [Hcross
    [Hidle [Hstatus [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames
    [Hreferences [Hstacks Hpending]]]]]]]]]]]]]]].
  pose proof Hcross as [_ [_ [Hregistration [_ [_ [HflagConsistency _]]]]]].
  destruct (event_pend_multi_wake_selected_phase sg state.(TskState) state.(EventState)
    tid task selected node kind Hregistration Htask Hlinked Hnode Hin Hkind)
    as [Hselected Hphase].
  pose proof Hphase as [_ [Hsingle _]].
  assert (Hnonempty : task.(eventMultiWaitEvents) <> []).
  { intro Hnil; rewrite Hnil in Hselected; contradiction. }
  assert (Hflag : task.(tcbFlagNode) = 0).
  { eapply event_pend_multi_nonempty_history_no_flag_node; eassumption. }
  assert (Hlive : Forall (fun eid => exists e, state.(EventState).(inUsedEventStates) eid = Some e)
      (selected :: task.(eventMultiWaitEvents))).
  { constructor; [eauto|]. eapply event_pend_multi_linked_ids_live; eauto. }
  set (events := event_multi_remove_waiters state.(EventState) tid
    (selected :: task.(eventMultiWaitEvents))).
  set (written := task_multi_wake task kind message result selected).
  set (tasks := glob_task_set_usedtask state.(TskState) tid written).
  set (sched := sched_wake_by_status sg state.(TskState) state.(SchedState) tid
    (encode_task_status written.(stat))).
  set (after := replace_SchedS sched (replace_TskS tasks (replace_EventS events state))).
  assert (HregisteredAfter : event_registration_consistency sg tasks events).
  { apply event_multi_wake_preserves_registration; assumption. }
  assert (HeventsAfter : event_registered_in_range sg tasks events).
  { pose proof (event_pend_multi_remove_preserves_module_fields sg state.(TskState)
      state.(EventState) tid (selected :: task.(eventMultiWaitEvents)) Hevents Hlive)
      as [Hp [Hf [Hi [Hc [Hb [Hq _]]]]]].
    repeat (split; [assumption|]); exact (proj1 HregisteredAfter). }
  assert (Horigin : forall eid e, events.(inUsedEventStates) eid = Some e ->
    exists before, state.(EventState).(inUsedEventStates) eid = Some before /\
      e.(eventType) = before.(eventType) /\ e.(mutexFields) = before.(mutexFields) /\
      e.(eventName) = before.(eventName) /\
      (e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(waitList) = before.(waitList))).
  { intros eid e He; unfold events in He; cbn [event_multi_remove_waiters inUsedEventStates] in He.
    destruct (state.(EventState).(inUsedEventStates) eid) as [before|] eqn:Hbefore;
      [|discriminate].
    destruct (in_dec Z.eq_dec eid (selected :: task.(eventMultiWaitEvents)));
      injection He as <-; exists before; repeat split; try reflexivity.
    intro Hmutex; apply remove_Z_eqb_notin_eq.
    exact (event_pend_multi_no_single_mutex_waiter sg state.(TskState) state.(EventState)
      tid task eid before Hregistration Htask Hsingle Hbefore Hmutex). }
  assert (Hforward : forall eid before,
    state.(EventState).(inUsedEventStates) eid = Some before ->
    exists e, events.(inUsedEventStates) eid = Some e /\
      e.(eventType) = before.(eventType) /\ e.(mutexFields) = before.(mutexFields)).
  { intros eid before Hbefore; unfold events; cbn [event_multi_remove_waiters inUsedEventStates].
    rewrite Hbefore; destruct (in_dec Z.eq_dec eid (selected :: task.(eventMultiWaitEvents)));
      eexists; repeat split; reflexivity. }
  assert (Hleases : event_mutex_lease_view events = event_mutex_lease_view state.(EventState))
    by reflexivity.
  assert (HcrossEvents : cross_module_consistency_with_wait sg (replace_EventS events state)
      (event_registration_consistency sg tasks events)).
  { eapply cross_module_consistency_with_wait_event_mutex_transport;
      [| |exact HregisteredAfter|exact Hleases|exact Hcross].
    - intros eid e He Htype.
      destruct (Horigin eid e He) as [before [Hb [Ht [Hm [_ Hw]]]]].
      exists before; repeat split; auto.
    - intros eid e He Htype; apply Hforward; exact He. }
  assert (HcrossTask : cross_module_registration_consistency sg
      (replace_TskS tasks (replace_EventS events state))).
  { unfold cross_module_registration_consistency.
    exact (event_pend_multi_wake_task_cross_frame sg (replace_EventS events state)
      tid task kind message result selected
      (event_registration_consistency sg tasks events)
      (event_registration_consistency sg tasks events)
      Htask Hflag Hphase HregisteredAfter HcrossEvents). }
  assert (Hrunning : sched.(isRunning) = state.(SchedState).(isRunning)).
  { apply sched_wake_by_status_running_eq. }
  assert (HcrossAfter : cross_module_registration_consistency sg after).
  { eapply cross_module_registration_sched_frame; [exact Hrunning|exact HcrossTask]. }
  assert (HreferencesAfter : kernel_names_valid sg after).
  { eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
    - eapply task_update_name_references; [exact Htask|reflexivity].
    - intros name [eid [e [He Hname]]].
      destruct (Horigin eid e He) as [before [Hb [_ [_ [Hsame _]]]]].
      exists eid, before; split; [exact Hb|congruence].
    - intros; assumption.
    - intros; assumption.
    - intros; assumption. }
  assert (HstacksAfter : parked_stacks_consistent tasks tasks.(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Htask|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  assert (HpendingAfter : pending_mutex_consistency sg tasks events).
  { eapply pending_mutex_consistency_frame;
      [reflexivity|reflexivity|exact Hleases| |exact Hpending].
    intros p [eid [e [m [He [Htype [Hm Hclaim]]]]]].
    destruct (Horigin eid e He) as [before [Hb [Ht [Hfields _]]]].
    exists eid, before, m; split; [exact Hb|]. split; [congruence|].
    split; [congruence|exact Hclaim]. }
  assert (Hunique : task_priority_unique state.(TskState))
    by (unfold task_in_range in Htasks; tauto).
  assert (Hpriority : task_priority_in_range sg task.(curPrio)).
  { destruct Htasks as (_ & _ & _ & _ & _ & _ & _ & Hrange & _); eapply Hrange; exact Htask. }
  change (UCOS2_full_state_inv sg after).
  split; [exact Hprofile|]. split.
  - eapply task_update_preserves_in_range;
      [exact Htasks|exact Htask|reflexivity|reflexivity|reflexivity|reflexivity|reflexivity].
  - split.
    + split.
      * eapply event_pend_multi_wake_preserves_registered_ready; eassumption.
      * change (sched_metadata_in_range sg sched).
        unfold sched, sched_wake_by_status.
        destruct (task_status_is_suspended (encode_task_status written.(stat))); exact Hmetadata.
    + split; [exact HeventsAfter|]. split; [exact HcrossAfter|]. split.
      * intro Hrun; eapply task_update_preserves_idle_tail;
          [exact Htask|reflexivity|apply Hidle].
        change (sched.(isRunning) = true) in Hrun; rewrite Hrunning in Hrun; exact Hrun.
      * split.
        -- apply task_reserved_bits_clear_update_task; [exact Hstatus|].
           apply task_status_clear_wait_preserves_reserved_bits; exact (Hstatus tid task Htask).
        -- repeat (split; [assumption|]); exact HpendingAfter.
Qed.

Lemma event_pend_multi_wake_step_preserves_full_state :
  forall sg before after tid task selected node kind message result,
  UCOS2_full_state_inv sg before ->
  before.(TskState).(inUsedTaskStates) tid = Some task ->
  before.(EventState).(inUsedEventStates) selected = Some node -> In tid node.(waitList) ->
  event_type_to_pend_type node.(eventType) = Some kind ->
  (result = PendOK \/ result = PendAbort) ->
  atomic_event_task_wake_multi sg tid selected kind message result before tt after ->
  UCOS2_full_state_inv sg after.
Proof.
  intros sg before after tid task selected node kind message result Hvalid Htask Hnode Hin Hkind Hresult
    [actual [events [Hactual [Hlinked [Hloop ->]]]]].
  assert (actual = task) by congruence; subst actual.
  assert (Hlive : Forall (fun eid => exists e, before.(EventState).(inUsedEventStates) eid = Some e)
      (selected :: task.(eventMultiWaitEvents))).
  { constructor; [eauto|]. eapply event_pend_multi_linked_ids_live; eauto. }
  rewrite (event_multi_remove_loop_eq_endpoint _ _ _ Hlive) in Hloop; injection Hloop as <-.
  eapply event_pend_multi_wake_preserves_full_state; eassumption.
Qed.
