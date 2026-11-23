Require Import Coq.Relations.Relation_Operators.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_idle_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_idle_protocol_spec.
Import TaskStateDef EventStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.

(** Admission of the already checked, actual Post source trace.  The
    identity-only Frame step proves its real active-order footprint; no
    caller/non-Idle premise is added to the Post critical transformer. *)
Lemma mutex_post_idle_frame_source : forall sg idle before after,
  after.(TskState).(inUsedTaskStates) = before.(TskState).(inUsedTaskStates) ->
  after.(EventState).(inUsedEventStates) = before.(EventState).(inUsedEventStates) ->
  after.(TskState).(taskLifecycle).(taskActiveOrder) = before.(TskState).(taskLifecycle).(taskActiveOrder) ->
  mutex_idle_source_history sg idle before after.
Proof.
  intros * Htasks Hevents Horder; apply Relation_Operators.rt_step.
  eapply MutexIdleExistingSource with
    (source := MutexOwnerSourceFrame sg before after Htasks Hevents).
  apply MutexIdleCallsFrame; exact Horder.
Qed.

Lemma mutex_post_idle_task_fields_source : forall sg idle before after tid old new,
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  new.(eventPtr) = old.(eventPtr) -> new.(eventMultiWaitEvents) = old.(eventMultiWaitEvents) ->
  after.(TskState).(inUsedTaskStates) =
    (glob_task_set_usedtask before.(TskState) tid new).(inUsedTaskStates) ->
  after.(EventState).(inUsedEventStates) = before.(EventState).(inUsedEventStates) ->
  after.(TskState).(taskLifecycle).(taskActiveOrder) = before.(TskState).(taskLifecycle).(taskActiveOrder) ->
  mutex_idle_source_history sg idle before after.
Proof.
  intros * Hold Hptr Hmulti Htasks Hevents Horder.
  eapply Relation_Operators.rt_trans with
    (y := replace_TskS (glob_task_set_usedtask before.(TskState) tid new) before).
  - apply Relation_Operators.rt_step.
    eapply MutexIdleExistingSource with (source := MutexOwnerSourceTaskField sg before
      (replace_TskS (glob_task_set_usedtask before.(TskState) tid new) before)
      tid old new Hold Hptr Hmulti eq_refl eq_refl).
    apply MutexIdleCallsTaskField.
  - apply Relation_Operators.rt_step.
    eapply MutexIdleExistingSource with (source := MutexOwnerSourceFrame sg
      (replace_TskS (glob_task_set_usedtask before.(TskState) tid new) before)
      after Htasks Hevents).
    apply MutexIdleCallsFrame; exact Horder.
Qed.

Lemma mutex_post_prepare_idle_source : forall sg idle mutex owner entry prepared,
  mutex_post_prepare sg mutex owner entry prepared ->
  mutex_idle_source_history sg idle entry prepared.
Proof.
  intros * Hprepare; unfold mutex_post_prepare in Hprepare.
  destruct Z.eq_dec; [subst; apply Relation_Operators.rt_refl|].
  destruct Hprepare as [node [priority [Hnode [_ ->]]]].
  unfold mutex_post_owner_priority_state; destruct Z.eq_dec.
  - apply mutex_post_idle_frame_source; reflexivity.
  - eapply mutex_post_idle_task_fields_source with (old := node)
      (new := mutex_priority_task node priority); try reflexivity; exact Hnode.
Qed.

Lemma mutex_post_empty_idle_source : forall sg idle state eid event mutex caller,
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some caller -> event.(waitList) = [] ->
  mutex_idle_source_history sg idle state (mutex_post_owner_state state eid event mutex None None).
Proof.
  intros * He Htype Hfields Howner Hempty.
  eapply Relation_Operators.rt_trans.
  - apply Relation_Operators.rt_step; eapply MutexIdleExistingSource.
    unshelve eapply MutexIdleCallsRelease with (eid := eid).
    unfold atomic_mutex_release.
    exists event; eexists; exists mutex; eexists; exists caller.
    do 2 eexists; repeat first [assumption | reflexivity | split].
  - apply mutex_post_idle_frame_source; reflexivity.
Qed.

Lemma mutex_post_handover_idle_source : forall sg idle state eid event mutex caller priority woken found owner,
  UCOS2_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some caller ->
  encode_event_wait_grp event.(waitList) state.(TskState) <> 0 ->
  event_task_rdy sg state eid PendMutex 0 PendOK = Some (priority, woken) ->
  woken.(EventState).(inUsedEventStates) eid = Some found ->
  woken.(TskState).(prioTbl) priority = PTTask owner ->
  mutex_idle_source_history sg idle state
    (mutex_post_owner_state woken eid found mutex (Some owner) (Some priority)).
Proof.
  intros * Hvalid He Htype Hfields Howner Hgroup Hwake Hfound Htable.
  destruct (event_wake_decompose sg state eid event PendMutex 0 PendOK priority woken
    Hvalid He ltac:(rewrite Htype; reflexivity) Hgroup Hwake)
    as [tid [tail [old [Hlist [Hold [Hp [Ew [Hw Hlookup]]]]]]]].
  rewrite Hlookup in Hfound; injection Hfound as Efound; subst found.
  assert (Hselection : state.(TskState).(prioTbl) old.(curPrio) = PTTask tid).
  { pose proof Hvalid as [Hprofile [Htasks [_ [[_ [_ [_ [_ [_ [_ Hentries]]]]]] _]]]].
    destruct (event_wait_priority_table_entry sg state.(TskState) eid event tid tail
      (proj1 Hprofile) Htasks (Hentries eid event He) Hlist) as [node [Hnode [Hprio Hsel]]].
    rewrite Hold in Hnode; injection Hnode as E; subst node; congruence. }
  assert (Eowner : owner = tid).
  { rewrite Ew, Hp in Htable; change (state.(TskState).(prioTbl) old.(curPrio) = PTTask owner) in Htable.
    rewrite Hselection in Htable; congruence. }
  subst owner priority woken.
  eapply Relation_Operators.rt_trans.
  - apply Relation_Operators.rt_step; eapply MutexIdleExistingSource.
    unshelve eapply MutexIdleCallsHandover with (eid := eid) (tid := tid); [exact Hvalid|].
    unfold atomic_mutex_release_with_handover.
    exists event; eexists; exists mutex; eexists; exists caller, old.
    do 6 eexists; exists tail; repeat first [assumption | reflexivity | split].
  - eapply mutex_post_idle_task_fields_source with
      (new := task_event_wake_single old PendMutex 0 PendOK).
    + cbn; rewrite Z.eqb_refl; reflexivity.
    + reflexivity.
    + reflexivity.
    + apply functional_extensionality; intros slot.
      cbn [mutex_post_owner_state replace_EventS event_wake_state replace_SchedS
        replace_TskS TskState inUsedTaskStates glob_task_set_usedtask].
      destruct (Z.eqb slot tid); reflexivity.
    + apply functional_extensionality; intros slot.
      cbn [mutex_post_owner_state replace_EventS event_wake_state replace_SchedS
        replace_TskS EventState inUsedEventStates update_event_field_raw].
      destruct (Z.eqb slot eid); reflexivity.
    + reflexivity.
Qed.

Lemma mutex_post_critical_idle_source : forall sg idle eid caller entry result schedule after,
  UCOS2_state_inv sg entry -> mutex_owner_event_unlinked entry.(TskState) entry.(EventState) ->
  task_slot_addr sg caller <> 1 ->
  mutex_post_critical sg eid caller entry result schedule after ->
  mutex_idle_source_history sg idle entry after.
Proof.
  intros * Hvalid Huse Hpointer Hrun; destruct Hrun.
  - apply Relation_Operators.rt_refl.
  - destruct (mutex_post_prepare_properties sg entry eid event mutex caller prepared
      Hvalid Huse H H0 H1 H2 Hpointer H3) as [Hprepared [Hevents Hslot]].
    assert (He : prepared.(EventState).(inUsedEventStates) eid = Some event) by (rewrite Hevents; exact H).
    eapply Relation_Operators.rt_trans; [eapply mutex_post_prepare_idle_source; exact H3|].
    eapply mutex_post_empty_idle_source; try eassumption.
    exact (mutex_del_event_group_zero_implies_empty sg prepared eid event Hprepared He H4).
  - destruct (mutex_post_prepare_properties sg entry eid event mutex caller prepared
      Hvalid Huse H H0 H1 H2 Hpointer H3) as [Hprepared [Hevents Hslot]].
    assert (He : prepared.(EventState).(inUsedEventStates) eid = Some event) by (rewrite Hevents; exact H).
    eapply Relation_Operators.rt_trans; [eapply mutex_post_prepare_idle_source; exact H3|].
    eapply mutex_post_handover_idle_source; eassumption.
Qed.

Lemma mutex_post_critical_preserves_idle_slot : forall sg idle eid caller entry result schedule after,
  UCOS2_state_inv sg entry -> mutex_owner_event_unlinked entry.(TskState) entry.(EventState) ->
  task_slot_addr sg caller <> 1 -> mutex_idle_slot entry.(TskState) idle ->
  mutex_post_critical sg eid caller entry result schedule after -> mutex_idle_slot after.(TskState) idle.
Proof.
  intros; eapply mutex_idle_source_history_preserves_slot;
    [eapply mutex_post_critical_idle_source; eassumption|eassumption].
Qed.
