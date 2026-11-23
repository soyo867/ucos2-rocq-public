Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Require Export Ucos2Verify.VC.code.event.spec.event_pend_multi_wait_prefix_spec.
Require Import Ucos2Verify.lib.event_registration Ucos2Verify.lib.event_registration_steps
  Ucos2Verify.lib.tick.
Import ListNotations TaskStateDef EventStateDef SchedStateDef.
Local Open Scope Z_scope.

(** The still-linked source branch, not the old input list alone, gives
    current live objects. Generations below are chosen from those current
    lookups; no claim is made that an already woken invocation's historical
    Events remain published. *)
Lemma event_pend_multi_linked_ids_live : forall sg state tid task ids,
  UCOS2_full_state_inv sg state ->
  state.(TskState).(inUsedTaskStates) tid = Some task ->
  task.(tcbEventMultiPtr) <> 0 -> task.(eventMultiWaitEvents) = ids ->
  Forall (fun eid => exists node, state.(EventState).(inUsedEventStates) eid = Some node) ids.
Proof.
  intros sg state tid task ids Hvalid Htask Hlinked Hids.
  assert (Hregistration : event_registration_consistency sg state.(TskState) state.(EventState)).
  { destruct Hvalid as [_ [_ [_ [_ [[_ [_ [Hr _]]] _]]]]]; exact Hr. }
  destruct Hregistration as [_ [_ Hclosed]].
  rewrite Forall_forall; intros eid Hin.
  eapply Hclosed; [exact Htask|].
  right; split; [exact Hlinked|rewrite Hids; exact Hin].
Qed.

(** Ready membership is a continuation fact. The registered ready relation
    permits both ordinary timeout-ready and residual-bit Multi-woken states;
    both have zero delay. Mere current-pointer equality is not used here. *)
Lemma event_pend_multi_ready_member_delay_zero : forall sg state tid task,
  UCOS2_full_state_inv sg state ->
  state.(TskState).(inUsedTaskStates) tid = Some task ->
  In tid state.(SchedState).(readyList) -> task.(dly) = 0.
Proof.
  intros sg state tid task Hvalid Htask Hmember.
  destruct Hvalid as [_ [_ [[[_ [Hforward _]] _] _]]].
  destruct (Hforward tid task Hmember Htask) as [[_ Hready]|[_ [Hdelay _]]].
  - apply task_resume_ready_test_iff in Hready; tauto.
  - exact Hdelay.
Qed.

Lemma event_pend_multi_cleanup_source_ready : forall task,
  task.(dly) = 0 -> task_source_ready (task_multi_cleanup task).
Proof.
  intros task Hdelay; split; [reflexivity|].
  apply task_resume_ready_test_iff; split; [reflexivity|exact Hdelay].
Qed.

Lemma event_pend_multi_cleanup_preserves_registered_ready : forall sg tasks sched tid task,
  sched_registered_ready_in_range sg tasks sched ->
  tasks.(inUsedTaskStates) tid = Some task -> In tid sched.(readyList) -> task.(dly) = 0 ->
  sched_registered_ready_in_range sg
    (glob_task_set_usedtask tasks tid (task_multi_cleanup task)) sched.
Proof.
  intros sg tasks sched tid task [Hstructure [Hforward Hback]] Htask Hmember Hdelay.
  pose proof (event_pend_multi_cleanup_source_ready task Hdelay) as Hwritten.
  split.
  - eapply sched_ready_structure_update_task; [exact Htask|reflexivity|exact Hstructure].
  - split.
    + intros member node Hin Hnode.
      cbn [glob_task_set_usedtask inUsedTaskStates] in Hnode.
      destruct (Z.eqb member tid) eqn:E.
      * injection Hnode as <-; left; exact Hwritten.
      * eapply Hforward; eassumption.
    + intros member node Hnode Hready.
      cbn [glob_task_set_usedtask inUsedTaskStates] in Hnode.
      destruct (Z.eqb member tid) eqn:E.
      * apply Z.eqb_eq in E; subst member; exact Hmember.
      * eapply Hback; eassumption.
Qed.

(** The original tail clears exactly the five modeled fields. Its Event
    registration proof distinguishes a still-linked removal from a wake
    that already removed the task. The branch facts below are source-stage
    inputs, not a claimed consequence of an arbitrary scheduler return. *)
Lemma event_pend_multi_cleanup_preserves_registration : forall sg state tid task ids,
  state.(TskState).(inUsedTaskStates) tid = Some task -> task.(eventPtr) = None ->
  (if event_pend_multi_remove_needed sg task
   then task.(tcbEventMultiPtr) <> 0 /\ task.(eventMultiWaitEvents) = ids
   else task.(tcbEventMultiPtr) = 0) ->
  event_registration_consistency sg state.(TskState) state.(EventState) ->
  event_registration_consistency sg
    (glob_task_set_usedtask state.(TskState) tid (task_multi_cleanup task))
    (event_pend_multi_resumed_events sg state tid task ids).
Proof.
  intros sg state tid task ids Htask Hsingle Hbranch Hregistration.
  assert (Hnone : forall eid, ~ task_event_registered (task_multi_cleanup task) eid).
  { intro eid; unfold task_event_registered.
    cbn [task_multi_cleanup task_set_multi_fields task_clear_pend_status_message
      task_clear_pend_status eventPtr tcbEventMultiPtr eventMultiWaitEvents].
    rewrite Hsingle; intros [H|[H _]]; congruence. }
  unfold event_pend_multi_resumed_events.
  destruct (event_pend_multi_remove_needed sg task).
  - destruct Hbranch as [Hlinked Hids].
    eapply event_multi_remove_preserves_registration;
      [exact Htask|reflexivity| |exact Hnone|exact Hregistration].
    intro eid; unfold task_event_registered; rewrite Hsingle, Hids.
    split; [intros [H|[_ H]]; [discriminate|exact H]|auto].
  - assert (Holdnone : forall eid, ~ task_event_registered task eid).
    { intro eid; unfold task_event_registered; rewrite Hsingle, Hbranch.
      intros [H|[H _]]; congruence. }
    eapply event_registration_update_task;
      [exact Htask|reflexivity| | |exact Hregistration].
    + intro eid; split; intro H; exfalso; [exact (Hnone eid H)|exact (Holdnone eid H)].
    + intros eid kind Hphase; exfalso; apply (Holdnone eid).
      eapply task_registered_wait_phase_implies_registered; exact Hphase.
Qed.

(** A nonempty registered sequence also supplies the callee's non-idle
    priority bound through a real bitmap backlink. The full Task bound by
    itself includes the idle priority and is intentionally not substituted. *)
Lemma event_pend_multi_linked_priority_valid : forall sg state tid task ids,
  UCOS2_full_state_inv sg state ->
  state.(TskState).(inUsedTaskStates) tid = Some task ->
  task.(tcbEventMultiPtr) <> 0 -> task.(eventMultiWaitEvents) = ids -> ids <> [] ->
  valid_task_prio sg task.(curPrio).
Proof.
  intros sg state tid task [|eid ids] Hvalid Htask Hlinked Hids Hnonempty;
    [contradiction|].
  assert (Hregistration : event_registration_consistency sg state.(TskState) state.(EventState)).
  { destruct Hvalid as [_ [_ [_ [_ [[_ [_ [Hr _]]] _]]]]]; exact Hr. }
  destruct Hregistration as [Hentries [Hback Hclosed]].
  assert (Href : task_event_registered task eid).
  { right; split; [exact Hlinked|rewrite Hids; left; reflexivity]. }
  destruct (Hclosed tid task eid Htask Href) as [node Hnode].
  pose proof (Hback tid task eid node Htask Hnode Href) as Hin.
  destruct (Hentries eid node Hnode) as [[_ [_ Hpriority]] _].
  destruct (Hpriority tid Hin) as [actual [Hactual Hrange]].
  assert (actual = task) by congruence; subst actual; exact Hrange.
Qed.

Lemma event_pend_multi_linked_remove_input :
  forall sg state tid task ids pointers,
  event_pend_multi_abi sg -> event_pend_multi_ids_valid sg pointers ids ->
  UCOS2_full_state_inv sg state -> event_pend_multi_task_selected sg state tid task ->
  task.(tcbEventMultiPtr) <> 0 -> task.(eventMultiWaitEvents) = ids -> ids <> [] ->
  exists instances, event_pend_multi_remove_input sg state tid task ids pointers instances.
Proof.
  intros sg state tid task ids pointers [Hlayout Hqueue] [Hpointers Hids]
    Hvalid [Hcurrent [Htask Hrow]] Hlinked Hsequence Hnonempty.
  pose proof (event_pend_multi_linked_ids_live _ _ _ _ _
    Hvalid Htask Hlinked Hsequence) as Hlive.
  pose proof (event_pend_multi_linked_priority_valid _ _ _ _ _
    Hvalid Htask Hlinked Hsequence Hnonempty) as Hpriority.
  destruct (event_pend_multi_live_ids_array_binding sg state.(EventState) ids Hlive)
    as [instances [Hinstances Hbinding]].
  exists instances; split; [exact Hinstances|].
  destruct Hvalid as [Hprofile [Htasks [_ [_ [Hcross _]]]]].
  assert (Hstable : valid_stable_glob_vars sg).
  { unfold full_features_kernel_profile in Hprofile; tauto. }
  assert (Hunique : task_priority_unique state.(TskState)).
  { unfold task_in_range in Htasks; tauto. }
  assert (Hentries : forall eid node, state.(EventState).(inUsedEventStates) eid = Some node ->
    event_registered_wait_entry sg state.(TskState) eid node).
  { destruct Hcross as [_ [_ [[He _] _]]]; exact He. }
  unfold event_task_remove_multi_input.
  split; [exact Hstable|]. split; [exact Hunique|]. split; [exact Hpriority|].
  split; [exact Htask|]. split; [exact Hrow|].
  split; [rewrite Hpointers; exact Hbinding|]. split.
  - rewrite Forall_forall in Hids |- *; intros [eid generation] Hin; cbn.
    apply Hlayout, Hids; rewrite <- Hinstances; apply in_map_iff.
    exists (eid, generation); auto.
  - intros eid node Hnode; exact (proj1 (Hentries eid node Hnode)).
Qed.

(** OSTimeTick changes delay/status but not the still-linked array and
    Event sequence. This is an exact transformer projection, not an
    environment-wide stability assumption. *)
Lemma event_pend_multi_tick_retains_registration : forall task base ids,
  task.(tcbEventMultiPtr) = base -> task.(eventMultiWaitEvents) = ids ->
  (tick_task_update task).(tcbEventMultiPtr) = base /\
  (tick_task_update task).(eventMultiWaitEvents) = ids /\
  (tick_task_update task).(eventMultiRdy) = task.(eventMultiRdy) /\
  (tick_task_update task).(eventPtr) = task.(eventPtr).
Proof.
  intros task base ids Hbase Hids; unfold tick_task_update.
  destruct (Z.eqb task.(dly) 0); simpl; auto.
Qed.

Lemma event_pend_multi_tick_expiration_takes_remove : forall sg task,
  task.(dly) = 1 -> task_status_has_pending (encode_task_status task.(stat)) = true ->
  (tick_task_update task).(statPend) = PendTimeout /\
  (tick_task_update task).(dly) = 0 /\
  event_pend_multi_remove_needed sg (tick_task_update task) = true.
Proof.
  intros sg task Hdelay Hpending.
  unfold tick_task_update; rewrite Hdelay; cbn [Z.eqb Z.sub].
  unfold task_status_timeout; rewrite Hpending.
  repeat split; reflexivity.
Qed.

(** EventTaskRdy's actual Multi suffix clears registration and writes the
    selected Event address. For the source OK/ABORT outcomes this prevents
    PendMulti from taking either RemoveMulti branch. *)
Lemma event_pend_multi_wake_skips_remove : forall sg task kind message result selected,
  (result = PendOK \/ result = PendAbort) -> event_addr sg selected <> 0 ->
  (task_multi_wake task kind message result selected).(tcbEventMultiPtr) = 0 /\
  (task_multi_wake task kind message result selected).(eventMultiWaitEvents) =
    task.(eventMultiWaitEvents) /\
  (task_multi_wake task kind message result selected).(dly) = 0 /\
  (task_multi_wake task kind message result selected).(eventPtr) = None /\
  event_pend_multi_remove_needed sg (task_multi_wake task kind message result selected) = false.
Proof.
  intros sg task kind message result selected Hresult Hnonzero.
  destruct Hresult as [-> | ->]; repeat split; try reflexivity.
  all: unfold event_pend_multi_remove_needed;
    cbn [task_multi_wake task_set_multi_fields task_event_wake_single task_set_event_ptr
      task_event_wake_before_remove statPend eventMultiRdy encode_event_link];
    apply Z.eqb_neq; exact Hnonzero.
Qed.
