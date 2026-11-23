Require Export Ucos2Verify.VC.code.event.spec.event_pend_multi_field_frame.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Import ListNotations UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** These lemmas classify the actual encoded pointer test. They do not
    decode NULL as ghost None, supply the scheduler/Save producer, or assume
    that historical Event instances remain live. *)
Lemma event_pend_multi_resumed_fields_ready : forall sg state tid task ids eid,
  (statPend task = PendOK \/ statPend task = PendAbort) ->
  eventMultiRdy task = Some eid -> event_addr sg eid <> 0 ->
  event_pend_multi_resumed_pending sg task = encode_pend_status (statPend task) /\
  event_pend_multi_resumed_events sg state tid task ids = EventState state /\
  event_pend_multi_resumed_ready sg task = [event_addr sg eid].
Proof.
  intros sg state tid task ids eid Hstatus Hready Hpointer.
  unfold event_pend_multi_resumed_pending, event_pend_multi_resumed_events,
    event_pend_multi_resumed_ready, event_pend_multi_remove_needed.
  destruct Hstatus as [Hstatus|Hstatus]; rewrite Hstatus, Hready;
    cbn [encode_event_link]; change (event_pool_addr sg eid) with (event_addr sg eid);
    rewrite (proj2 (Z.eqb_neq _ _) Hpointer); repeat split; reflexivity.
Qed.

Lemma event_pend_multi_resumed_fields_null_pointer : forall sg state tid task ids,
  encode_event_link sg task.(eventMultiRdy) = 0 ->
  event_pend_multi_resumed_pending sg task = 1 /\
  event_pend_multi_resumed_events sg state tid task ids =
    event_multi_remove_waiters (EventState state) tid ids /\
  event_pend_multi_resumed_ready sg task = [].
Proof.
  intros sg state tid task ids Hnull.
  unfold event_pend_multi_resumed_pending, event_pend_multi_resumed_events,
    event_pend_multi_resumed_ready.
  rewrite (event_pend_multi_remove_needed_null_pointer sg task Hnull).
  repeat split; reflexivity.
Qed.

Lemma event_pend_multi_resumed_fields_null : forall sg state tid task ids,
  eventMultiRdy task = None ->
  event_pend_multi_resumed_pending sg task = 1 /\
  event_pend_multi_resumed_events sg state tid task ids =
    event_multi_remove_waiters (EventState state) tid ids /\
  event_pend_multi_resumed_ready sg task = [].
Proof.
  intros sg state tid task ids Hready.
  unfold event_pend_multi_resumed_pending, event_pend_multi_resumed_events,
    event_pend_multi_resumed_ready, event_pend_multi_remove_needed.
  rewrite Hready; destruct (statPend task); repeat split; reflexivity.
Qed.

Lemma event_pend_multi_resumed_fields_timeout : forall sg state tid task ids,
  statPend task = PendTimeout ->
  event_pend_multi_resumed_pending sg task = 1 /\
  event_pend_multi_resumed_events sg state tid task ids =
    event_multi_remove_waiters (EventState state) tid ids /\
  event_pend_multi_resumed_ready sg task = [].
Proof.
  intros sg state tid task ids Hstatus.
  unfold event_pend_multi_resumed_pending, event_pend_multi_resumed_events,
    event_pend_multi_resumed_ready, event_pend_multi_remove_needed.
  rewrite Hstatus; repeat split; reflexivity.
Qed.

Lemma event_pend_multi_resumed_pending_in_range : forall sg task,
  0 <= event_pend_multi_resumed_pending sg task <= 2.
Proof.
  intros; unfold event_pend_multi_resumed_pending, event_pend_multi_remove_needed.
  destruct (statPend task); destruct (Z.eqb (encode_event_link sg (eventMultiRdy task)) 0);
    cbn [encode_pend_status]; lia.
Qed.

Lemma event_pend_multi_resumed_pending_ok_has_ready : forall sg task,
  event_pend_multi_resumed_pending sg task = 0 ->
  statPend task = PendOK /\ exists eid, eventMultiRdy task = Some eid.
Proof.
  intros sg task Hpending.
  unfold event_pend_multi_resumed_pending, event_pend_multi_remove_needed in Hpending.
  destruct (statPend task) eqn:Hstatus; destruct (eventMultiRdy task) eqn:Hready;
    cbn [encode_pend_status encode_event_link] in Hpending; try discriminate;
    try destruct (Z.eqb (event_pool_addr sg e) 0); try discriminate; split; eauto.
Qed.

Lemma event_pend_multi_resumed_pending_ok_nonnull : forall sg task,
  event_pend_multi_resumed_pending sg task = 0 ->
  encode_event_link sg task.(eventMultiRdy) <> 0.
Proof.
  intros sg task Hpending Hnull.
  unfold event_pend_multi_resumed_pending in Hpending.
  rewrite (event_pend_multi_remove_needed_null_pointer sg task Hnull) in Hpending; discriminate.
Qed.

Lemma event_pend_multi_pend_status_cases : forall task,
  event_pend_multi_task_pend_status task = 0 \/
  event_pend_multi_task_pend_status task = 1 \/
  event_pend_multi_task_pend_status task = 2.
Proof.
  intros; unfold event_pend_multi_task_pend_status.
  destruct (statPend task); cbn [encode_pend_status]; auto.
Qed.

(** The branch normalization keeps the whole stage heap, including the
    configured TCB remainder, the other kernel modules, both full output
    arrays, and the original ordered input array.  The common CPU/local
    frame is not consumed by either side.  These are representation
    equivalences, not producers for the branch hypotheses or RemoveMulti. *)
Lemma event_pend_multi_resume_stage_ready_equiv :
  forall sg state tid task ids pointers base ready messages old_ready old_messages eid,
  (statPend task = PendOK \/ statPend task = PendAbort) ->
  eventMultiRdy task = Some eid -> event_addr sg eid <> 0 ->
  event_pend_multi_resume_stage sg state tid task ids pointers base ready messages
    old_ready old_messages --||--
  (event_pend_multi_resume_cells sg tid task (encode_pend_status (statPend task)) **
   event_pend_multi_task_frame sg state tid task event_pend_multi_resume_fields **
   event_raw_rep sg (TskState state) (EventState state) **
   event_multi_array_rep base pointers **
   PtrArray.mixed_full ready (Zlength old_ready)
     (event_pend_multi_ready_values [event_addr sg eid] old_ready) **
   PtrArray.mixed_full messages (Zlength old_messages) old_messages).
Proof.
  intros sg state tid task ids pointers base ready messages old_ready old_messages eid Hstatus Hready Hpointer.
  pose proof (event_pend_multi_resumed_fields_ready sg state tid task ids eid Hstatus Hready Hpointer)
    as [Hpending [Hevents Hvalues]].
  unfold event_pend_multi_resume_stage; rewrite Hpending, Hevents, Hvalues.
  split; entailer!.
Qed.

Lemma event_pend_multi_resume_stage_null_pointer_equiv :
  forall sg state tid task ids pointers base ready messages old_ready old_messages,
  encode_event_link sg task.(eventMultiRdy) = 0 ->
  event_pend_multi_resume_stage sg state tid task ids pointers base ready messages
    old_ready old_messages --||--
  (event_pend_multi_resume_cells sg tid task 1 **
   event_pend_multi_task_frame sg state tid task event_pend_multi_resume_fields **
   event_raw_rep sg (TskState state) (event_multi_remove_waiters (EventState state) tid ids) **
   event_multi_array_rep base pointers **
   PtrArray.mixed_full ready (Zlength old_ready) (event_pend_multi_ready_values [] old_ready) **
   PtrArray.mixed_full messages (Zlength old_messages) old_messages).
Proof.
  intros sg state tid task ids pointers base ready messages old_ready old_messages Hnull.
  pose proof (event_pend_multi_resumed_fields_null_pointer sg state tid task ids Hnull)
    as [Hpending [Hevents Hvalues]].
  unfold event_pend_multi_resume_stage; rewrite Hpending, Hevents, Hvalues.
  split; entailer!.
Qed.

Lemma event_pend_multi_resume_stage_null_equiv :
  forall sg state tid task ids pointers base ready messages old_ready old_messages,
  eventMultiRdy task = None ->
  event_pend_multi_resume_stage sg state tid task ids pointers base ready messages
    old_ready old_messages --||--
  (event_pend_multi_resume_cells sg tid task 1 **
   event_pend_multi_task_frame sg state tid task event_pend_multi_resume_fields **
   event_raw_rep sg (TskState state) (event_multi_remove_waiters (EventState state) tid ids) **
   event_multi_array_rep base pointers **
   PtrArray.mixed_full ready (Zlength old_ready) (event_pend_multi_ready_values [] old_ready) **
   PtrArray.mixed_full messages (Zlength old_messages) old_messages).
Proof.
  intros sg state tid task ids pointers base ready messages old_ready old_messages Hready.
  pose proof (event_pend_multi_resumed_fields_null sg state tid task ids Hready)
    as [Hpending [Hevents Hvalues]].
  unfold event_pend_multi_resume_stage; rewrite Hpending, Hevents, Hvalues.
  split; entailer!.
Qed.

Lemma event_pend_multi_resume_stage_timeout_equiv :
  forall sg state tid task ids pointers base ready messages old_ready old_messages,
  statPend task = PendTimeout ->
  event_pend_multi_resume_stage sg state tid task ids pointers base ready messages
    old_ready old_messages --||--
  (event_pend_multi_resume_cells sg tid task 1 **
   event_pend_multi_task_frame sg state tid task event_pend_multi_resume_fields **
   event_raw_rep sg (TskState state) (event_multi_remove_waiters (EventState state) tid ids) **
   event_multi_array_rep base pointers **
   PtrArray.mixed_full ready (Zlength old_ready) (event_pend_multi_ready_values [] old_ready) **
   PtrArray.mixed_full messages (Zlength old_messages) old_messages).
Proof.
  intros sg state tid task ids pointers base ready messages old_ready old_messages Hstatus.
  pose proof (event_pend_multi_resumed_fields_timeout sg state tid task ids Hstatus)
    as [Hpending [Hevents Hvalues]].
  unfold event_pend_multi_resume_stage; rewrite Hpending, Hevents, Hvalues.
  split; entailer!.
Qed.
