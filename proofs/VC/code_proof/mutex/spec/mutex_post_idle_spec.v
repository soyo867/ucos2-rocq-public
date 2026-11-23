Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_idle_protocol_spec.
Import TaskStateDef EventStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.

(** A consequence of the checked Post transformer.  This file neither
    changes the C entry domain nor assumes that the chosen new owner is
    non-Idle: the handover proof derives that fact from the actual wait list. *)
Lemma mutex_post_prepare_preserves_idle_excluded : forall sg idle mutex caller acquired prepared,
  mutex_post_prepare sg mutex caller acquired prepared ->
  mutex_idle_excluded idle acquired.(EventState) ->
  mutex_idle_excluded idle prepared.(EventState).
Proof.
  intros * Hprepare Hidle.
  rewrite (mutex_post_prepare_event_state_eq sg mutex caller acquired prepared Hprepare); exact Hidle.
Qed.

Lemma mutex_post_owner_state_preserves_idle_excluded : forall idle state eid event mutex owner snapshot,
  mutex_idle_excluded idle state.(EventState) ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  (forall tid, owner = Some tid -> tid <> idle) ->
  mutex_idle_excluded idle (mutex_post_owner_state state eid event mutex owner snapshot).(EventState).
Proof.
  intros * Hidle Hlookup Howner.
  intros slot current Hcurrent Htype.
  cbn [mutex_post_owner_state replace_EventS EventState update_event_field_raw inUsedEventStates] in Hcurrent.
  destruct (Z.eqb slot eid) eqn:Hsame.
  - injection Hcurrent as E; subst current.
    cbn [mutex_post_owner_event eventType] in Htype.
    destruct (Hidle eid event Hlookup Htype) as [_ Hwait].
    split; [|exact Hwait].
    intros fields tid Hfields Htid.
    cbn [mutex_post_owner_event mutexFields] in Hfields; injection Hfields as E; subst fields.
    apply Howner; exact Htid.
  - exact (Hidle slot current Hcurrent Htype).
Qed.

Lemma mutex_post_wake_preserves_idle_excluded : forall sg idle state eid event tid old kind message result,
  mutex_idle_excluded idle state.(EventState) ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  mutex_idle_excluded idle
    (event_wake_state sg state eid event tid old kind message result).(EventState).
Proof.
  intros; eapply event_wake_preserves_idle_excluded; eassumption.
Qed.

Lemma mutex_post_handover_preserves_idle_excluded : forall sg idle state eid event mutex priority woken found owner,
  UCOS2_state_inv sg state -> mutex_idle_excluded idle state.(EventState) ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  encode_event_wait_grp event.(waitList) state.(TskState) <> 0 ->
  event_task_rdy sg state eid PendMutex 0 PendOK = Some (priority, woken) ->
  woken.(EventState).(inUsedEventStates) eid = Some found ->
  woken.(TskState).(prioTbl) priority = PTTask owner ->
  owner <> idle /\ mutex_idle_excluded idle
    (mutex_post_owner_state woken eid found mutex (Some owner) (Some priority)).(EventState).
Proof.
  intros * Hvalid Hidle He Htype Hfields Hgroup Hwake Hfound Htable.
  destruct (event_wake_decompose sg state eid event PendMutex 0 PendOK priority woken
    Hvalid He ltac:(rewrite Htype; reflexivity) Hgroup Hwake)
    as [tid [tail [old [Hlist [Hold [Hp [Ew [Hw Hlookup]]]]]]]].
  assert (Hselection : state.(TskState).(prioTbl) old.(curPrio) = PTTask tid).
  { pose proof Hvalid as [Hprofile [Htasks [_ [[_ [_ [_ [_ [_ [_ Hentries]]]]]] _]]]].
    destruct (event_wait_priority_table_entry sg state.(TskState) eid event tid tail
      (proj1 Hprofile) Htasks (Hentries eid event He) Hlist) as [node [Hnode [Hprio Hsel]]].
    rewrite Hold in Hnode; injection Hnode as E; subst node; congruence. }
  assert (Eowner : owner = tid).
  { rewrite Ew, Hp in Htable; change (state.(TskState).(prioTbl) old.(curPrio) = PTTask owner) in Htable.
    rewrite Hselection in Htable; congruence. }
  assert (Hnotidle : tid <> idle).
  { intro E; apply (proj2 (Hidle eid event He Htype)); rewrite Hlist, E; left; reflexivity. }
  split; [congruence|].
  apply mutex_post_owner_state_preserves_idle_excluded; [|exact Hfound|].
  - rewrite Ew; eapply mutex_post_wake_preserves_idle_excluded; eassumption.
  - intros selected Hselected; injection Hselected as E; subst selected; congruence.
Qed.

Lemma mutex_post_critical_preserves_idle_excluded : forall sg idle eid caller acquired result schedule committed,
  UCOS2_state_inv sg acquired -> mutex_owner_event_unlinked acquired.(TskState) acquired.(EventState) ->
  task_slot_addr sg caller <> 1 -> mutex_idle_excluded idle acquired.(EventState) ->
  mutex_post_critical sg eid caller acquired result schedule committed ->
  mutex_idle_excluded idle committed.(EventState).
Proof.
  intros * Hvalid Huse Hpointer Hidle Hrun; destruct Hrun.
  - exact Hidle.
  - pose proof (mutex_post_prepare_preserves_idle_excluded sg idle mutex caller entry prepared H3 Hidle) as Hprepared.
    apply mutex_post_owner_state_preserves_idle_excluded; [exact Hprepared| |].
    + rewrite (mutex_post_prepare_event_state_eq sg mutex caller entry prepared H3); exact H.
    + intros tid Hnone; discriminate.
  - destruct (mutex_post_prepare_properties sg entry eid event mutex caller prepared
      Hvalid Huse H H0 H1 H2 Hpointer H3) as [Hprepared [Hevents Hslot]].
    assert (He : prepared.(EventState).(inUsedEventStates) eid = Some event) by (rewrite Hevents; exact H).
    apply (proj2 (mutex_post_handover_preserves_idle_excluded sg idle prepared eid event mutex priority woken found owner
      Hprepared ltac:(rewrite Hevents; exact Hidle) He H0 H1 H4 H5 H6 H7)).
Qed.

Lemma mutex_post_critical_source_preserves_idle_excluded : forall sg idle eid caller acquired result schedule committed,
  UCOS2_state_inv sg acquired -> mutex_owner_event_unlinked acquired.(TskState) acquired.(EventState) ->
  task_slot_addr sg caller <> 1 -> mutex_idle_excluded idle acquired.(EventState) ->
  mutex_post_critical sg eid caller acquired result schedule committed ->
  mutex_owner_source_history sg acquired committed /\ mutex_idle_excluded idle committed.(EventState).
Proof.
  intros * Hvalid Huse Hpointer Hidle Hrun; split.
  - eapply mutex_post_critical_source; eassumption.
  - eapply mutex_post_critical_preserves_idle_excluded; eassumption.
Qed.

(** The same actual Idle slot remains at its initialized priority.  Both
    writes to task fields target a non-Idle task, justified respectively
    by the old owner and by the selected waiter. *)
Lemma mutex_post_prepare_preserves_idle_task : forall sg idle mutex owner acquired prepared,
  owner <> idle -> mutex_idle_task sg acquired.(TskState) idle ->
  mutex_post_prepare sg mutex owner acquired prepared ->
  mutex_idle_task sg prepared.(TskState) idle.
Proof.
  intros * Hother Hidle Hprepare; unfold mutex_post_prepare in Hprepare.
  destruct Z.eq_dec; [subst; exact Hidle|].
  destruct Hprepare as [node [priority [Hnode [_ ->]]]].
  unfold mutex_post_owner_priority_state; destruct Z.eq_dec; [exact Hidle|].
  destruct Hidle as [old [Hlookup Hpriority]]; exists old; split; [|exact Hpriority].
  cbn [mutex_post_relocated_state mutex_del_ceiling_view mutex_del_ceiling_view_tasks
    mutex_del_relocated_state replace_SchedS replace_TskS TskState
    mutex_del_relocated_tasks glob_task_set_usedtask inUsedTaskStates].
  rewrite (proj2 (Z.eqb_neq idle owner) ltac:(congruence)); exact Hlookup.
Qed.

Lemma mutex_post_ready_preserves_idle_task : forall sg idle state eid event priority woken,
  UCOS2_state_inv sg state -> mutex_idle_excluded idle state.(EventState) ->
  mutex_idle_task sg state.(TskState) idle ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX ->
  encode_event_wait_grp event.(waitList) state.(TskState) <> 0 ->
  event_task_rdy sg state eid PendMutex 0 PendOK = Some (priority, woken) ->
  mutex_idle_task sg woken.(TskState) idle.
Proof.
  intros * Hvalid Hidle Htask He Htype Hgroup Hwake.
  destruct (event_wake_decompose sg state eid event PendMutex 0 PendOK priority woken
    Hvalid He ltac:(rewrite Htype; reflexivity) Hgroup Hwake)
    as [tid [tail [old [Hlist [Hold [Hp [Ew [Hw Hlookup]]]]]]]].
  assert (Hother : tid <> idle).
  { eapply mutex_idle_excluded_waiter; try eassumption; rewrite Hlist; left; reflexivity. }
  rewrite Ew; apply mutex_idle_task_update_other; assumption.
Qed.

Lemma mutex_post_critical_preserves_idle_task : forall sg idle eid caller acquired result schedule committed,
  UCOS2_state_inv sg acquired -> mutex_owner_event_unlinked acquired.(TskState) acquired.(EventState) ->
  task_slot_addr sg caller <> 1 -> mutex_idle_excluded idle acquired.(EventState) ->
  mutex_idle_task sg acquired.(TskState) idle ->
  mutex_post_critical sg eid caller acquired result schedule committed ->
  mutex_idle_task sg committed.(TskState) idle.
Proof.
  intros * Hvalid Huse Hpointer Hidle Htask Hrun; destruct Hrun.
  - exact Htask.
  - apply (mutex_post_prepare_preserves_idle_task sg idle mutex caller entry prepared);
      [eapply mutex_idle_excluded_owner; eassumption|exact Htask|exact H3].
  - destruct (mutex_post_prepare_properties sg entry eid event mutex caller prepared
      Hvalid Huse H H0 H1 H2 Hpointer H3) as [Hprepared [Hevents Hslot]].
    assert (He : prepared.(EventState).(inUsedEventStates) eid = Some event) by (rewrite Hevents; exact H).
    change (mutex_idle_task sg woken.(TskState) idle).
    eapply mutex_post_ready_preserves_idle_task; try eassumption.
    + rewrite Hevents; exact Hidle.
    + eapply mutex_post_prepare_preserves_idle_task;
        [eapply mutex_idle_excluded_owner; eassumption|exact Htask|exact H3].
Qed.
