Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Strings.String Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.VC.code.event.spec.event_pend_multi_resume_source_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_pend_multi_cleanup_heap_spec.
Require Import Ucos2Verify.lib.event_registration Ucos2Verify.lib.event_registration_steps
  Ucos2Verify.lib.kernel_names Ucos2Verify.lib.task_stack
  Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.event Ucos2Verify.lib.event_pool
  Ucos2Verify.lib.mutex Ucos2Verify.lib.task_status.
Import ListNotations TaskStateDef EventStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

Lemma event_pend_multi_no_single_mutex_waiter : forall sg tasks events tid task eid node,
  event_registration_consistency sg tasks events ->
  tasks.(inUsedTaskStates) tid = Some task -> task.(eventPtr) = None ->
  events.(inUsedEventStates) eid = Some node -> node.(eventType) = OS_EVENT_TYPE_MUTEX ->
  ~ In tid node.(waitList).
Proof.
  intros sg tasks events tid task eid node [Hentries _] Htask Hsingle Hnode Htype Hin.
  destruct (Hentries eid node Hnode) as [_ Hphase].
  rewrite Htype in Hphase; cbn [event_type_to_pend_type] in Hphase.
  destruct (Hphase tid Hin) as [found [Hfound Hwaiting]].
  assert (found = task) by congruence; subst found.
  destruct Hwaiting as [[Hptr _]|[_ [[Hkind|[Hkind|Hkind]] _]]]; congruence.
Qed.

Lemma event_pend_multi_nonempty_history_no_flag_node : forall sg tasks flags tid task,
  task_flag_waiter_consistency sg tasks flags ->
  tasks.(inUsedTaskStates) tid = Some task -> task.(eventMultiWaitEvents) <> [] ->
  task.(tcbFlagNode) = 0.
Proof.
  intros sg tasks flags tid task [Hnodes Hback] Htask Hnonempty.
  destruct (Z.eq_dec task.(tcbFlagNode) 0) as [Hzero|Hnonzero]; [exact Hzero|].
  destruct (Hback tid task Htask (or_introl Hnonzero)) as [w [Hw Htid]].
  destruct (Hnodes task.(tcbFlagNode) w Hw) as [_ [found [Hfound Hfields]]].
  rewrite Htid in Hfound; assert (found = task) by congruence; subst found.
  exfalso; apply Hnonempty; tauto.
Qed.

(** A module-field factor, not a global invariant: the waiter clauses are
    rebuilt separately from the exact registration theorem. No public
    contract is weakened by using True at this intermediate factor. *)
Lemma event_pend_multi_remove_preserves_module_fields : forall sg tasks events tid ids,
  event_registered_in_range sg tasks events ->
  Forall (fun eid => exists node, events.(inUsedEventStates) eid = Some node) ids ->
  event_in_range_with_wait sg (event_multi_remove_waiters events tid ids)
    (fun _ _ => True).
Proof.
  intros sg tasks events tid ids Hvalid Hlive.
  assert (Hfields : event_in_range_with_wait sg events (fun _ _ => True)).
  { destruct Hvalid as [Hp [Hf [Hi [Hc [Hb [Hq _]]]]]].
    repeat (split; [assumption|]); intros; exact I. }
  clear Hvalid; revert events Hfields Hlive.
  induction ids as [|eid ids IH]; intros events Hfields Hlive.
  - rewrite event_multi_remove_waiters_nil; exact Hfields.
  - inversion Hlive as [|head tail Hhead Htail]; subst head tail.
    destruct Hhead as [node Hnode].
    rewrite (event_multi_remove_waiters_source_order events tid eid ids node Hnode).
    apply IH.
    + pose proof Hfields as [_ [_ [_ [Hcells [Hpayload _]]]]].
      eapply event_update_preserves_in_range_with_wait;
        [exact Hfields|exact Hnode|reflexivity| | |reflexivity|exact I].
      * apply event_fields_consistency_remove_waiter; eapply Hcells; exact Hnode.
      * destruct (in_dec Z.eq_dec tid node.(waitList)) as [Hin|Hnot].
        -- apply event_payload_consistency_remove_waiter; [exact Hin|eapply Hpayload; exact Hnode].
        -- rewrite (remove_Z_eqb_notin_eq tid node.(waitList) Hnot).
           replace (event_set_wait_list node node.(waitList)) with node by (destruct node; reflexivity).
           eapply Hpayload; exact Hnode.
    + rewrite Forall_forall in Htail |- *; intros slot Hin.
      destruct (Htail slot Hin) as [found Hfound].
      cbn [update_event_field_raw inUsedEventStates]; destruct (Z.eqb slot eid); eauto.
Qed.

Lemma event_pend_multi_cleanup_task_cross_frame : forall sg state tid task
    (waiting_before waiting_after : Prop),
  state.(TskState).(inUsedTaskStates) tid = Some task -> task.(tcbFlagNode) = 0 ->
  waiting_after -> cross_module_consistency_with_wait sg state waiting_before ->
  cross_module_consistency_with_wait sg
    (replace_TskS (glob_task_set_usedtask state.(TskState) tid (task_multi_cleanup task)) state)
    waiting_after.
Proof.
  intros sg state tid task waiting_before waiting_after Htask Hflag Hafter
    [Htable [Hsnapshot [_ [Hprotocol [Hunique [Hflags Htimer]]]]]].
  split.
  - eapply task_mutex_priotbl_consistency_update_task; [exact Htask|reflexivity|exact Htable].
  - split; [eapply mutex_owner_snapshot_update_task; eassumption|].
    split; [exact Hafter|]. split; [exact Hprotocol|]. split; [exact Hunique|].
    split; [|exact Htimer].
    eapply task_flag_waiter_consistency_update_unregistered_task;
      [exact Htask|exact Hflag|exact Hflag|discriminate|exact Hflags].
Qed.

Lemma event_pend_multi_cleanup_events_origin : forall sg state tid task ids,
  event_registration_consistency sg state.(TskState) state.(EventState) ->
  state.(TskState).(inUsedTaskStates) tid = Some task -> task.(eventPtr) = None ->
  forall eid node,
  (event_pend_multi_resumed_events sg state tid task ids).(inUsedEventStates) eid = Some node ->
  exists before, state.(EventState).(inUsedEventStates) eid = Some before /\
    node.(eventType) = before.(eventType) /\ node.(mutexFields) = before.(mutexFields) /\
    node.(eventName) = before.(eventName) /\
    (node.(eventType) = OS_EVENT_TYPE_MUTEX -> node.(waitList) = before.(waitList)).
Proof.
  intros sg state tid task ids Hregistration Htask Hsingle eid node Hnode.
  unfold event_pend_multi_resumed_events in Hnode.
  destruct (event_pend_multi_remove_needed sg task).
  - cbn [event_multi_remove_waiters inUsedEventStates] in Hnode.
    destruct (state.(EventState).(inUsedEventStates) eid) as [before|] eqn:Hbefore;
      [|discriminate].
    destruct (in_dec Z.eq_dec eid ids); injection Hnode as <-; exists before;
      repeat split; try reflexivity.
    intro Hmutex; apply remove_Z_eqb_notin_eq.
    eapply event_pend_multi_no_single_mutex_waiter; eassumption.
  - exists node; repeat split; assumption || reflexivity.
Qed.

Lemma event_pend_multi_cleanup_events_forward : forall sg state tid task ids eid before,
  state.(EventState).(inUsedEventStates) eid = Some before ->
  exists node,
    (event_pend_multi_resumed_events sg state tid task ids).(inUsedEventStates) eid = Some node /\
    node.(eventType) = before.(eventType) /\ node.(mutexFields) = before.(mutexFields).
Proof.
  intros sg state tid task ids eid before Hbefore.
  unfold event_pend_multi_resumed_events; destruct (event_pend_multi_remove_needed sg task).
  - cbn [event_multi_remove_waiters inUsedEventStates]; rewrite Hbefore.
    destruct (in_dec Z.eq_dec eid ids); eexists; repeat split; reflexivity.
  - exists before; auto.
Qed.

(** Complete pure endpoint for the original five stores. The hypotheses
    describe the resumed invocation's source phase: the task really is on
    the ready list; its original nonempty sequence remains available; and
    it is either still linked or was already unlinked by a Multi wake.
    Dly and EventPtr are not silently overwritten by this theorem. *)
Lemma event_pend_multi_cleanup_preserves_full_state : forall sg state tid task ids,
  UCOS2_full_state_inv sg state ->
  state.(TskState).(inUsedTaskStates) tid = Some task ->
  In tid state.(SchedState).(readyList) -> task.(eventPtr) = None ->
  task.(eventMultiWaitEvents) = ids -> ids <> [] ->
  (if event_pend_multi_remove_needed sg task
   then task.(tcbEventMultiPtr) <> 0 else task.(tcbEventMultiPtr) = 0) ->
  event_pend_multi_resumed_error sg state task <> 1 ->
  UCOS2_full_state_inv sg (event_pend_multi_resumed_state sg state tid task ids).
Proof.
  intros sg state tid task ids Hvalid Htask Hmember Hsingle Hsequence Hnonempty Hbranch Herror.
  pose proof (event_pend_multi_ready_member_delay_zero sg state tid task Hvalid Htask Hmember)
    as Hdelay.
  pose proof Hvalid as [Hprofile [Htasks [[Hready Hmetadata] [Hevents [Hcross
    [Hidle [Hstatus [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames
    [Hreferences [Hstacks Hpending]]]]]]]]]]]]]]].
  pose proof Hcross as [_ [_ [Hregistration [_ [_ [HflagConsistency _]]]]]].
  assert (Hflag : task.(tcbFlagNode) = 0).
  { eapply event_pend_multi_nonempty_history_no_flag_node;
      [exact HflagConsistency|exact Htask|congruence]. }
  set (events := event_pend_multi_resumed_events sg state tid task ids).
  set (tasks := glob_task_set_usedtask state.(TskState) tid (task_multi_cleanup task)).
  set (after := replace_TskS tasks (replace_EventS events state)).
  assert (HregisteredAfter : event_registration_consistency sg tasks events).
  { apply event_pend_multi_cleanup_preserves_registration; [exact Htask|exact Hsingle| |exact Hregistration].
    destruct (event_pend_multi_remove_needed sg task); auto. }
  assert (HeventsAfter : event_registered_in_range sg tasks events).
  { assert (Hdata : event_in_range_with_wait sg events (fun _ _ => True)).
    { unfold events, event_pend_multi_resumed_events.
      destruct (event_pend_multi_remove_needed sg task).
      - apply event_pend_multi_remove_preserves_module_fields with (tasks := state.(TskState));
          [exact Hevents|].
        eapply event_pend_multi_linked_ids_live; eassumption.
      - destruct Hevents as [Hp [Hf [Hi [Hc [Hb [Hq _]]]]]].
        repeat (split; [assumption|]); intros; exact I. }
    destruct Hdata as [Hp [Hf [Hi [Hc [Hb [Hq _]]]]]].
    repeat (split; [assumption|]); exact (proj1 HregisteredAfter). }
  pose proof (event_pend_multi_cleanup_events_origin sg state tid task ids
    Hregistration Htask Hsingle) as Horigin.
  pose proof (event_pend_multi_cleanup_events_forward sg state tid task ids) as Hforward.
  assert (Hleases : event_mutex_lease_view events = event_mutex_lease_view state.(EventState)).
  { unfold events, event_pend_multi_resumed_events.
    destruct (event_pend_multi_remove_needed sg task); reflexivity. }
  assert (HcrossEvents : cross_module_consistency_with_wait sg (replace_EventS events state)
      (event_registration_consistency sg tasks events)).
  { eapply cross_module_consistency_with_wait_event_mutex_transport;
      [| |exact HregisteredAfter|exact Hleases|exact Hcross].
    - intros eid node Hnode Htype.
      destruct (Horigin eid node Hnode) as [before [Hb [Ht [Hm [_ Hw]]]]].
      exists before; repeat split; auto.
    - intros eid node Hnode Htype; apply Hforward; exact Hnode. }
  assert (HcrossAfter : cross_module_registration_consistency sg after).
  { unfold after, cross_module_registration_consistency.
    exact (event_pend_multi_cleanup_task_cross_frame sg (replace_EventS events state) tid task
      (event_registration_consistency sg tasks events)
      (event_registration_consistency sg tasks events)
      Htask Hflag HregisteredAfter HcrossEvents). }
  assert (HreferencesAfter : kernel_names_valid sg after).
  { eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
    - eapply task_update_name_references; [exact Htask|reflexivity].
    - intros name [eid [node [Hnode Hname]]].
      destruct (Horigin eid node Hnode) as [before [Hb [_ [_ [Hsame _]]]]].
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
    intros p [eid [node [m [Hnode [Htype [Hm Hclaim]]]]]].
    destruct (Horigin eid node Hnode) as [before [Hb [Ht [Hfields _]]]].
    exists eid, before, m; split; [exact Hb|]. split; [congruence|].
    split; [congruence|exact Hclaim]. }
  assert (Hafter : UCOS2_full_state_inv sg after).
  { split; [exact Hprofile|]. split.
    - eapply task_update_preserves_in_range;
        [exact Htasks|exact Htask|reflexivity|reflexivity|reflexivity|reflexivity|reflexivity].
    - split.
      + split; [|exact Hmetadata].
        eapply event_pend_multi_cleanup_preserves_registered_ready; eassumption.
      + split; [exact HeventsAfter|]. split; [exact HcrossAfter|]. split.
        * intro Hrunning; eapply task_update_preserves_idle_tail;
            [exact Htask|reflexivity|apply Hidle; exact Hrunning].
        * split.
          -- apply task_reserved_bits_clear_update_task; [exact Hstatus|].
             apply task_status_no_pending_reserved_bits_clear; reflexivity.
          -- repeat (split; [assumption|]); exact HpendingAfter. }
  unfold event_pend_multi_resumed_state; rewrite (proj2 (Z.eqb_neq _ _) Herror).
  exact Hafter.
Qed.

Lemma event_pend_multi_cleanup_full_merge : forall sg state tid task ids,
  UCOS2_full_state_inv sg state -> event_pend_multi_task_selected sg state tid task ->
  In tid state.(SchedState).(readyList) -> task.(eventPtr) = None ->
  task.(eventMultiWaitEvents) = ids -> ids <> [] ->
  (if event_pend_multi_remove_needed sg task
   then task.(tcbEventMultiPtr) <> 0 else task.(tcbEventMultiPtr) = 0) ->
  event_pend_multi_resumed_error sg state task <> 1 ->
  let tcb := task_slot_addr sg tid in
  sg.(g_OSTCBCur) # Ptr |-> tcb **
  &(tcb # "os_tcb" ->ₛ "OSTCBStat") # UChar |-> 0 **
  &(tcb # "os_tcb" ->ₛ "OSTCBStatPend") # UChar |-> 0 **
  &(tcb # "os_tcb" ->ₛ "OSTCBEventMultiPtr") # Ptr |-> 0 **
  &(tcb # "os_tcb" ->ₛ "OSTCBEventMultiRdy") # Ptr |-> 0 **
  &(tcb # "os_tcb" ->ₛ "OSTCBMsg") # Ptr |-> 0 **
  event_task_remove_multi_tcb_reads tcb task **
  event_pend_multi_task_frame sg state tid task event_pend_multi_resume_fields **
  event_raw_rep sg state.(TskState) (event_pend_multi_resumed_events sg state tid task ids) |--
  UCOS2_full_inv sg (event_pend_multi_resumed_state sg state tid task ids).
Proof.
  intros sg state tid task ids Hvalid Hselected Hmember Hsingle Hsequence Hnonempty Hbranch Herror;
    cbn zeta.
  pose proof (event_pend_multi_cleanup_preserves_full_state sg state tid task ids
    Hvalid (proj1 (proj2 Hselected)) Hmember Hsingle Hsequence Hnonempty Hbranch Herror) as Hafter.
  pose proof (event_pend_multi_cleanup_raw_merge sg state tid task ids Hvalid Hselected Herror)
    as Hheap; cbn zeta in Hheap.
  sep_apply_l_atomic Hheap; unfold UCOS2_full_inv; entailer!.
Qed.
