Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Require Export Ucos2Verify.VC.code.event.spec.event_pend_multi_cleanup_full_spec.
Require Import Ucos2Verify.lib.event_registration Ucos2Verify.lib.tick
  Ucos2Verify.lib.task_context Ucos2Verify.lib.task_status.
Import ListNotations TaskStateDef EventStateDef SchedStateDef.
Local Open Scope Z_scope.

(** Fields of this one suspended PendMulti call, before its normal cleanup.
    This predicate owns no C cells and says neither that the Task is current
    nor that it is ready. Its two cases are established by WaitMulti and
    the actual EventTaskRdy Multi suffix below, not by a generic CPU return.
    The retained ids are only a sequence in the woken case, not live owners. *)
Definition event_pend_multi_task_continuation (base : Z) (ids : list EventID)
  (task : TaskAbstractState) : Prop :=
  task.(eventPtr) = None /\ task.(eventMultiWaitEvents) = ids /\
  ((base <> 0 /\ task.(tcbEventMultiPtr) = base /\ task.(eventMultiRdy) = None) \/
   (task.(tcbEventMultiPtr) = 0 /\ exists selected,
      In selected ids /\ task.(eventMultiRdy) = Some selected /\
      (task.(statPend) = PendOK \/ task.(statPend) = PendAbort) /\ task.(dly) = 0)).

Lemma event_pend_multi_wait_establishes_task_continuation : forall task mask timeout base ids,
  task.(eventPtr) = None -> base <> 0 ->
  event_pend_multi_task_continuation base ids
    (task_set_multi_fields (task_prepare_multi_wait task mask timeout) base ids None).
Proof.
  intros task mask timeout base ids Hsingle Hbase.
  split; [exact Hsingle|]. split; [reflexivity|]. left; auto.
Qed.

Lemma event_pend_multi_tick_preserves_task_continuation : forall base ids task,
  event_pend_multi_task_continuation base ids task ->
  event_pend_multi_task_continuation base ids (tick_task_update task).
Proof.
  intros base ids task [Hsingle [Hids [Hlinked|[Hunlinked [selected [Hin [Hrdy [Hresult Hdelay]]]]]]]].
  - unfold tick_task_update; destruct (Z.eqb task.(dly) 0).
    + split; [exact Hsingle|]. split; [exact Hids|]. left; exact Hlinked.
    + split; [exact Hsingle|]. split; [exact Hids|]. left; exact Hlinked.
  - unfold tick_task_update; rewrite Hdelay; cbn [Z.eqb].
    split; [exact Hsingle|]. split; [exact Hids|]. right; split; [exact Hunlinked|].
    exists selected; auto.
Qed.

Lemma event_pend_multi_profile_preserves_task_continuation :
  forall base ids task switches cycles start stack_base used,
  event_pend_multi_task_continuation base ids task ->
  event_pend_multi_task_continuation base ids
    (task_set_profile task switches cycles start stack_base used).
Proof. intros; exact H. Qed.

Lemma event_pend_multi_saved_sp_preserves_task_continuation : forall base ids task sp,
  event_pend_multi_task_continuation base ids task ->
  event_pend_multi_task_continuation base ids (task_set_saved_sp task sp).
Proof. intros; exact H. Qed.

Lemma event_pend_multi_status_preserves_task_continuation : forall base ids task status,
  event_pend_multi_task_continuation base ids task ->
  event_pend_multi_task_continuation base ids (task_set_status task status).
Proof. intros; exact H. Qed.

(** The selected Event is obtained from the actual waiter relation. An
    arbitrary Event id is not allowed to become the saved ready choice. *)
Lemma event_pend_multi_wake_establishes_task_continuation :
  forall sg tasks events base ids tid task selected node kind message result,
  event_registration_consistency sg tasks events ->
  tasks.(inUsedTaskStates) tid = Some task ->
  events.(inUsedEventStates) selected = Some node -> In tid node.(waitList) ->
  event_pend_multi_task_continuation base ids task -> task.(tcbEventMultiPtr) <> 0 ->
  (result = PendOK \/ result = PendAbort) ->
  event_pend_multi_task_continuation base ids (task_multi_wake task kind message result selected).
Proof.
  intros sg tasks events base ids tid task selected node kind message result
    Hregistration Htask Hnode Hin [Hsingle [Hids Hphase]] Hlinked Hresult.
  assert (Hselected : In selected ids).
  { pose proof (proj1 (event_registration_waiter_iff sg tasks events tid task selected node
      Hregistration Htask Hnode) Hin) as Hregistered.
    unfold task_event_registered in Hregistered; rewrite Hsingle in Hregistered.
    destruct Hregistered as [Hbad|[_ Hselected]]; [discriminate|rewrite <- Hids; exact Hselected]. }
  split; [reflexivity|]. split; [exact Hids|]. right; split; [reflexivity|].
  exists selected; split; [exact Hselected|]. split; [reflexivity|].
  split; [exact Hresult|reflexivity].
Qed.

Lemma event_pend_multi_valid_id_address_nonzero : forall sg eid,
  valid_stable_glob_vars sg -> valid_event_id sg eid -> event_addr sg eid <> 0.
Proof.
  intros sg eid Hstable [Hnonnegative Hbound].
  assert (Haddresses : valid_stable_global_addresses sg) by (unfold valid_stable_glob_vars in Hstable; tauto).
  destruct Haddresses as [Hpositive _].
  inversion Hpositive as [|head tail Hbase Htail].
  pose proof (event_object_size_positive sg.(osKernelConfig)) as Hsize.
  unfold event_addr, event_pool_addr; nia.
Qed.

Lemma event_pend_multi_task_continuation_remove_branch : forall sg base ids pointers task,
  valid_stable_glob_vars sg -> event_pend_multi_ids_valid sg pointers ids ->
  event_pend_multi_task_continuation base ids task ->
  (if event_pend_multi_remove_needed sg task
   then task.(tcbEventMultiPtr) <> 0 else task.(tcbEventMultiPtr) = 0).
Proof.
  intros sg base ids pointers task Hstable [_ Hvalid] [Hsingle [Hids [Hlinked|Hwoken]]].
  - destruct Hlinked as [Hbase [Hpointer Hready]].
    unfold event_pend_multi_remove_needed; rewrite Hready; destruct task.(statPend);
      cbn [encode_event_link Z.eqb]; congruence.
  - destruct Hwoken as [Hpointer [selected [Hin [Hready [Hresult Hdelay]]]]].
    assert (Hnonzero : event_addr sg selected <> 0).
    { apply event_pend_multi_valid_id_address_nonzero; [exact Hstable|].
      rewrite Forall_forall in Hvalid; apply Hvalid; exact Hin. }
    assert (Hnonnull : Z.eqb (encode_event_link sg (Some selected)) 0 = false).
    { apply Z.eqb_neq; exact Hnonzero. }
    unfold event_pend_multi_remove_needed; destruct Hresult as [Hresult|Hresult];
      rewrite Hresult, Hready, Hnonnull; exact Hpointer.
Qed.

Lemma event_pend_multi_task_continuation_ready_choice : forall sg base ids pointers task,
  event_pend_multi_ids_valid sg pointers ids ->
  event_pend_multi_task_continuation base ids task ->
  event_pend_multi_task_ready_pointer sg task <> 0 ->
  exists selected, In selected ids /\ valid_event_id sg selected /\
    task.(eventMultiRdy) = Some selected.
Proof.
  intros sg base ids pointers task [_ Hvalid] [Hsingle [Hids [Hlinked|Hwoken]]] Hnonzero.
  - destruct Hlinked as [_ [_ Hready]].
    unfold event_pend_multi_task_ready_pointer in Hnonzero; rewrite Hready in Hnonzero.
    contradiction.
  - destruct Hwoken as [_ [selected [Hin [Hready _]]]].
    exists selected; split; [exact Hin|]. split; [|exact Hready].
    rewrite Forall_forall in Hvalid; apply Hvalid; exact Hin.
Qed.

Lemma event_pend_multi_task_continuation_cleanup_full_state : forall sg state tid task base ids pointers,
  UCOS2_full_state_inv sg state ->
  state.(TskState).(inUsedTaskStates) tid = Some task ->
  In tid state.(SchedState).(readyList) -> event_pend_multi_ids_valid sg pointers ids -> ids <> [] ->
  event_pend_multi_task_continuation base ids task ->
  event_pend_multi_resumed_error sg state task <> 1 ->
  UCOS2_full_state_inv sg (event_pend_multi_resumed_state sg state tid task ids).
Proof.
  intros sg state tid task base ids pointers Hvalid Htask Hmember Hids Hnonempty Hphase Herror.
  pose proof Hphase as [Hsingle [Hsequence _]].
  eapply event_pend_multi_cleanup_preserves_full_state;
    [exact Hvalid|exact Htask|exact Hmember|exact Hsingle|exact Hsequence|exact Hnonempty| |exact Herror].
  eapply event_pend_multi_task_continuation_remove_branch;
    [exact (proj1 (proj1 Hvalid))|exact Hids|exact Hphase].
Qed.

Lemma event_pend_multi_task_continuation_remove_input :
  forall sg state tid task base ids pointers,
  event_pend_multi_abi sg -> event_pend_multi_ids_valid sg pointers ids ->
  UCOS2_full_state_inv sg state -> event_pend_multi_task_selected sg state tid task ->
  event_pend_multi_task_continuation base ids task -> ids <> [] ->
  event_pend_multi_remove_needed sg task = true ->
  exists instances, event_pend_multi_remove_input sg state tid task ids pointers instances.
Proof.
  intros sg state tid task base ids pointers Habi Hids Hvalid Hselected Hphase Hnonempty Hremove.
  pose proof (event_pend_multi_task_continuation_remove_branch sg base ids pointers task
    (proj1 (proj1 Hvalid)) Hids Hphase) as Hlinked.
  rewrite Hremove in Hlinked.
  eapply event_pend_multi_linked_remove_input;
    [exact Habi|exact Hids|exact Hvalid|exact Hselected|exact Hlinked|exact (proj1 (proj2 Hphase))|exact Hnonempty].
Qed.
