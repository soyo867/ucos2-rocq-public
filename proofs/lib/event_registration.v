Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_multi.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.cross_module_invariants.
Import ListNotations TaskStateDef EventStateDef SchedStateDef.
Local Open Scope Z_scope.

(** In the Multi-enabled layout the real MultiPtr, not the retained input
    sequence alone, says whether the task is still registered. EventTaskRdy
    clears MultiPtr after removing the task from all Event bitmaps. The
    logical sequence may remain available to the suspended C invocation;
    it then supplies neither a live-object guarantee nor a bitmap backlink.
    This predicate owns no TCB, Event or borrowed-array cells. *)
Definition task_event_registered (t : TaskAbstractState) (eid : EventID) : Prop :=
  t.(eventPtr) = Some eid \/
  (t.(tcbEventMultiPtr) <> 0 /\ In eid t.(eventMultiWaitEvents)).

Definition task_multi_linked_wait_phase (t : TaskAbstractState) (kind : PendType) : Prop :=
  (kind = PendSem \/ kind = PendMbox \/ kind = PendQ) /\
  t.(eventPtr) = None /\ t.(tcbEventMultiPtr) <> 0 /\ t.(eventMultiRdy) = None /\
  exists mask suspended,
    0 <= mask < 8 /\ encode_task_status t.(stat) = encode_multi_wait_status mask suspended /\
    ((Z.land mask (task_pend_mask kind) = task_pend_mask kind /\ t.(statPend) = PendOK) \/
     (mask = 0 /\ t.(statPend) = PendTimeout /\ t.(dly) = 0)).

Definition task_registered_wait_phase (t : TaskAbstractState)
  (eid : EventID) (kind : PendType) : Prop :=
  (t.(eventPtr) = Some eid /\ t.(tcbEventMultiPtr) = 0 /\ task_linked_wait_phase t kind) \/
  (In eid t.(eventMultiWaitEvents) /\ task_multi_linked_wait_phase t kind).

Definition event_registered_wait_entry (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (eid : EventID) (e : OSEventAbstractState) : Prop :=
  event_waitList_canonical sg tasks e.(waitList) /\
  match event_type_to_pend_type e.(eventType) with
  | Some kind => forall tid, In tid e.(waitList) -> exists t,
      tasks.(inUsedTaskStates) tid = Some t /\ task_registered_wait_phase t eid kind
  | None => e.(waitList) = []
  end.

Definition event_registered_backlinks (tasks : Glob_TaskAbstractState)
  (events : Glob_EventAbstractState) : Prop :=
  forall tid t eid e, tasks.(inUsedTaskStates) tid = Some t ->
    events.(inUsedEventStates) eid = Some e -> task_event_registered t eid ->
    In tid e.(waitList).

Definition event_registered_reference_closure (tasks : Glob_TaskAbstractState)
  (events : Glob_EventAbstractState) : Prop :=
  forall tid t eid, tasks.(inUsedTaskStates) tid = Some t ->
    task_event_registered t eid -> exists e, events.(inUsedEventStates) eid = Some e.

Definition event_registration_consistency (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (events : Glob_EventAbstractState) : Prop :=
  (forall eid e, events.(inUsedEventStates) eid = Some e ->
    event_registered_wait_entry sg tasks eid e) /\
  event_registered_backlinks tasks events /\ event_registered_reference_closure tasks events.

Lemma task_registered_wait_phase_implies_registered : forall t eid kind,
  task_registered_wait_phase t eid kind -> task_event_registered t eid.
Proof.
  intros t eid kind [[Hptr _]|[Hin [_ [_ [Hptr _]]]]];
    unfold task_event_registered; auto.
Qed.

Definition event_registered_in_range (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (events : Glob_EventAbstractState) : Prop :=
  event_in_range_with_wait sg events (event_registered_wait_entry sg tasks).

Definition cross_module_registration_consistency (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Prop :=
  cross_module_consistency_with_wait sg s
    (event_registration_consistency sg s.(TskState) s.(EventState)).

Lemma task_event_registered_multi_fields : forall t array ids ready eid,
  t.(eventPtr) = None -> array <> 0 ->
  (task_event_registered (task_set_multi_fields t array ids ready) eid <-> In eid ids).
Proof.
  intros t array ids ready eid Hptr Harray.
  unfold task_event_registered; cbn [task_set_multi_fields eventPtr tcbEventMultiPtr eventMultiWaitEvents].
  rewrite Hptr; split; [intros [H|[_ H]]; [discriminate|exact H]|auto].
Qed.

Lemma task_multi_wake_has_no_registration : forall t kind message result selected eid,
  ~ task_event_registered (task_multi_wake t kind message result selected) eid.
Proof.
  intros; unfold task_event_registered; cbn [task_multi_wake task_set_multi_fields
    task_event_wake_single task_set_event_ptr task_event_wake_before_remove
    eventPtr tcbEventMultiPtr eventMultiWaitEvents]; intros [H|[H _]]; congruence.
Qed.

Lemma event_registered_wait_entry_empty : forall sg tasks eid e,
  e.(waitList) = [] -> event_registered_wait_entry sg tasks eid e.
Proof.
  intros sg tasks eid e Hempty; unfold event_registered_wait_entry, event_waitList_canonical.
  rewrite Hempty; split.
  - split; [constructor|]. split; [constructor|intros tid Hin; contradiction].
  - destruct (event_type_to_pend_type e.(eventType)); [intros tid Hin; contradiction|reflexivity].
Qed.

Lemma event_registration_consistency_empty : forall sg tasks events,
  (forall tid, tasks.(inUsedTaskStates) tid = None) ->
  (forall eid e, events.(inUsedEventStates) eid = Some e -> e.(waitList) = []) ->
  event_registration_consistency sg tasks events.
Proof.
  intros sg tasks events Htasks Hevents; split.
  - intros; apply event_registered_wait_entry_empty; eauto.
  - split; intros tid t eid; rewrite Htasks; intros H; discriminate.
Qed.

Lemma event_registration_waiter_iff : forall sg tasks events tid t eid e,
  event_registration_consistency sg tasks events ->
  tasks.(inUsedTaskStates) tid = Some t -> events.(inUsedEventStates) eid = Some e ->
  (In tid e.(waitList) <-> task_event_registered t eid).
Proof.
  intros sg tasks events tid t eid e [Hentries [Hback Hclosed]] Ht He; split.
  - intros Hin; destruct (Hentries eid e He) as [_ Hphase].
    destruct (event_type_to_pend_type e.(eventType)); [|rewrite Hphase in Hin; contradiction].
    destruct (Hphase tid Hin) as [actual [Ha Hp]].
    assert (actual = t) by congruence; subst actual.
    eapply task_registered_wait_phase_implies_registered; exact Hp.
  - apply Hback with (t := t); assumption.
Qed.

Lemma event_registration_free_slot_unreferenced : forall sg tasks events eid,
  event_registration_consistency sg tasks events -> events.(inUsedEventStates) eid = None ->
  forall tid t, tasks.(inUsedTaskStates) tid = Some t -> ~ task_event_registered t eid.
Proof.
  intros sg tasks events eid [_ [_ Hclosed]] Hnone tid t Ht Href.
  destruct (Hclosed tid t eid Ht Href) as [e He]; congruence.
Qed.

(** A shared module may update profiling/link fields while preserving the
    actual registration and phase observations. This transports existing
    facts; it does not manufacture a new registered task. *)
Lemma event_registered_wait_entry_update_task : forall sg tasks tid old new eid e,
  tasks.(inUsedTaskStates) tid = Some old -> new.(curPrio) = old.(curPrio) ->
  (forall slot kind, task_registered_wait_phase old slot kind ->
    task_registered_wait_phase new slot kind) ->
  event_registered_wait_entry sg tasks eid e ->
  event_registered_wait_entry sg (glob_task_set_usedtask tasks tid new) eid e.
Proof.
  intros sg tasks tid old new eid e Hold Hp Hphase [Horder Hentries]; split.
  - eapply event_waitList_canonical_update_task; eassumption.
  - destruct (event_type_to_pend_type e.(eventType)); [|exact Hentries].
    intros member Hin; destruct (Hentries member Hin) as [t [Ht Hstage]].
    cbn [glob_task_set_usedtask inUsedTaskStates].
    destruct (Z.eqb member tid) eqn:E.
    + apply Z.eqb_eq in E; subst member; assert (t = old) by congruence; subst t.
      exists new; split; [reflexivity|apply Hphase; exact Hstage].
    + exists t; split; assumption.
Qed.

Lemma event_registration_update_task : forall sg tasks events tid old new,
  tasks.(inUsedTaskStates) tid = Some old -> new.(curPrio) = old.(curPrio) ->
  (forall eid, task_event_registered new eid <-> task_event_registered old eid) ->
  (forall eid kind, task_registered_wait_phase old eid kind ->
    task_registered_wait_phase new eid kind) ->
  event_registration_consistency sg tasks events ->
  event_registration_consistency sg (glob_task_set_usedtask tasks tid new) events.
Proof.
  intros sg tasks events tid old new Hold Hp Hrefs Hphases [Hentries [Hback Hclosed]]; split.
  - intros eid e He; eapply event_registered_wait_entry_update_task; eauto.
  - split.
    + intros member t eid e Ht He Href; cbn [glob_task_set_usedtask inUsedTaskStates] in Ht.
      destruct (Z.eqb member tid) eqn:E.
      * apply Z.eqb_eq in E; subst member; injection Ht as Ht; subst t.
        eapply Hback; [exact Hold|exact He|apply Hrefs; exact Href].
      * eapply Hback; eassumption.
    + intros member t eid Ht Href; cbn [glob_task_set_usedtask inUsedTaskStates] in Ht.
      destruct (Z.eqb member tid) eqn:E.
      * apply Z.eqb_eq in E; subst member; injection Ht as Ht; subst t.
        eapply Hclosed; [exact Hold|apply Hrefs; exact Href].
      * eapply Hclosed; eassumption.
Qed.

(** The ordinary ready test is the source PEND_ANY/Dly/SUSPEND test.
    A Multi wake may additionally insert a task with residual pending bits.
    Such a task is allowed, but not forced, to be ready: suspension followed
    by Resume does not insert it if a residual bit remains. No liveness or
    whole-register restoration promise is encoded by this relation. *)
Definition task_source_ready (t : TaskAbstractState) : Prop :=
  task_is_suspended t.(stat) = false /\ task_resume_ready_test t = true.

Definition task_multi_woken_ready (t : TaskAbstractState) : Prop :=
  task_is_suspended t.(stat) = false /\ t.(dly) = 0 /\
  t.(tcbEventMultiPtr) = 0 /\ t.(eventMultiRdy) <> None /\
  (t.(statPend) = PendOK \/ t.(statPend) = PendAbort) /\
  exists mask, 0 <= mask < 8 /\ encode_task_status t.(stat) = encode_multi_wait_status mask false.

Definition sched_registered_ready_in_range (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (s : SchedAbstractState) : Prop :=
  sched_ready_structure sg tasks s /\
  (forall tid t, In tid s.(readyList) -> tasks.(inUsedTaskStates) tid = Some t ->
    task_source_ready t \/ task_multi_woken_ready t) /\
  (forall tid t, tasks.(inUsedTaskStates) tid = Some t -> task_source_ready t ->
    In tid s.(readyList)).

(** Refreshing the two high-ready cache cells observes only the real ready
    list's live priorities. It does not change, or strengthen, the source
    phase that allowed any task to be on that list. *)
Lemma sched_refresh_high_preserves_registered_in_range : forall sg tasks s,
  task_pool_partition sg tasks ->
  sched_registered_ready_in_range sg tasks s /\ sched_metadata_in_range sg s ->
  sched_registered_ready_in_range sg tasks (sched_refresh_high tasks s) /\
    sched_metadata_in_range sg (sched_refresh_high tasks s).
Proof.
  intros sg tasks s Hpool [Hready [Hhigh [Hcounter Hcurrent]]].
  split; [exact Hready|]; split; [|split; [exact Hcounter|exact Hcurrent]].
  unfold sched_physical_cache_in_range, sched_refresh_high; simpl.
  destruct s.(readyList) as [|head tail] eqn:Hlist; [split; exact I|].
  destruct (proj1 (proj1 Hready) head ltac:(rewrite Hlist; left; reflexivity))
    as [t [Ht Hprio]].
  rewrite Ht; split; [|left; exact Hprio].
  apply (proj2 (proj1 Hpool head)); left; exists t; exact Ht.
Qed.

Lemma sched_increment_switch_counter_preserves_registered_in_range : forall sg tasks s,
  sched_registered_ready_in_range sg tasks s /\ sched_metadata_in_range sg s ->
  sched_registered_ready_in_range sg tasks (sched_increment_switch_counter s) /\
    sched_metadata_in_range sg (sched_increment_switch_counter s).
Proof.
  intros sg tasks s [Hready [Hhigh [Hcounter Hcurrent]]].
  split; [exact Hready|]; split; [exact Hhigh|]; split;
    [apply sched_increment_switch_counter_in_range|exact Hcurrent].
Qed.

Lemma cross_module_registration_sched_frame : forall sg s sched',
  sched'.(isRunning) = s.(SchedState).(isRunning) ->
  cross_module_registration_consistency sg s ->
  cross_module_registration_consistency sg (replace_SchedS sched' s).
Proof.
  intros sg s sched' Hrunning Hcross.
  unfold cross_module_registration_consistency, cross_module_consistency_with_wait,
    timer_running_initialization_consistency in *.
  cbn [replace_SchedS TskState EventState FlagState TimerState SchedState].
  rewrite Hrunning; exact Hcross.
Qed.

Lemma sched_registered_ready_boot : forall sg name,
  sched_registered_ready_in_range sg (task_boot sg name) sched_boot.
Proof.
  intros; split.
  - split; [intros tid Hin; contradiction|]. split; constructor.
  - split; [intros tid t Hin; contradiction|intros tid t H; discriminate].
Qed.

Lemma sched_registered_ready_update_task : forall sg tasks s tid old new,
  tasks.(inUsedTaskStates) tid = Some old -> new.(curPrio) = old.(curPrio) ->
  (task_source_ready new <-> task_source_ready old) ->
  (task_multi_woken_ready new <-> task_multi_woken_ready old) ->
  sched_registered_ready_in_range sg tasks s ->
  sched_registered_ready_in_range sg (glob_task_set_usedtask tasks tid new) s.
Proof.
  intros sg tasks s tid old new Hold Hp Hsource Hmulti [Hstructure [Hforward Hback]]; split.
  - eapply sched_ready_structure_update_task; eassumption.
  - split.
    + intros member t Hin Ht; cbn [glob_task_set_usedtask inUsedTaskStates] in Ht.
      destruct (Z.eqb member tid) eqn:E.
      * apply Z.eqb_eq in E; subst member; injection Ht as Ht; subst t.
        destruct (Hforward tid old Hin Hold); [left; apply Hsource|right; apply Hmulti]; assumption.
      * eapply Hforward; eassumption.
    + intros member t Ht Hr; cbn [glob_task_set_usedtask inUsedTaskStates] in Ht.
      destruct (Z.eqb member tid) eqn:E.
      * apply Z.eqb_eq in E; subst member; injection Ht as Ht; subst t.
        eapply Hback; [exact Hold|apply Hsource; exact Hr].
      * eapply Hback; eassumption.
Qed.

Lemma event_registered_in_range_update_task : forall sg tasks events tid old new,
  tasks.(inUsedTaskStates) tid = Some old -> new.(curPrio) = old.(curPrio) ->
  (forall eid kind, task_registered_wait_phase old eid kind ->
    task_registered_wait_phase new eid kind) ->
  event_registered_in_range sg tasks events ->
  event_registered_in_range sg (glob_task_set_usedtask tasks tid new) events.
Proof.
  intros sg tasks events tid old new Hold Hp Hphase
    [Hpool [Hfree [Hidentity [Hfields [Hpayload [Hqueue Hentries]]]]]].
  split; [exact Hpool|]. split; [exact Hfree|]. split; [exact Hidentity|].
  split; [exact Hfields|]. split; [exact Hpayload|]. split; [exact Hqueue|].
  intros eid e He; eapply event_registered_wait_entry_update_task; eauto.
Qed.

Lemma event_set_name_preserves_registered_in_range : forall sg tasks events eid old name,
  event_registered_in_range sg tasks events -> events.(inUsedEventStates) eid = Some old ->
  event_registered_in_range sg tasks
    (update_event_field_raw events eid (event_set_name old name)).
Proof.
  intros sg tasks events eid old name Hvalid Hget.
  pose proof Hvalid as [_ [_ [_ [Hfields [Hpayload [_ Hwait]]]]]].
  eapply event_update_preserves_in_range_with_wait;
    [exact Hvalid|exact Hget|reflexivity|exact (Hfields eid old Hget)|
     exact (Hpayload eid old Hget)|reflexivity|exact (Hwait eid old Hget)].
Qed.

Lemma event_registration_event_fields_update : forall sg tasks events eid old new,
  events.(inUsedEventStates) eid = Some old ->
  new.(eventType) = old.(eventType) -> new.(waitList) = old.(waitList) ->
  event_registration_consistency sg tasks events ->
  event_registration_consistency sg tasks (update_event_field_raw events eid new).
Proof.
  intros sg tasks events eid old new Hold Htype Hwait [Hentries [Hback Hclosed]].
  assert (Horigin : forall slot node,
    (update_event_field_raw events eid new).(inUsedEventStates) slot = Some node ->
    exists before, events.(inUsedEventStates) slot = Some before /\
      node.(eventType) = before.(eventType) /\ node.(waitList) = before.(waitList)).
  { intros slot node Hnode; cbn [update_event_field_raw inUsedEventStates] in Hnode.
    destruct (Z.eqb slot eid) eqn:E.
    - apply Z.eqb_eq in E; subst slot; injection Hnode as Hnode; subst node; exists old; auto.
    - exists node; auto. }
  split.
  - intros slot node Hnode; destruct (Horigin slot node Hnode) as [before [Hb [Ht Hw]]].
    unfold event_registered_wait_entry; rewrite Ht, Hw; exact (Hentries slot before Hb).
  - split.
    + intros tid t slot node Htask Hnode Href.
      destruct (Horigin slot node Hnode) as [before [Hb [_ Hw]]].
      rewrite Hw; eapply Hback; eassumption.
    + intros tid t slot Htask Href; destruct (Hclosed tid t slot Htask Href) as [before Hb].
      cbn [update_event_field_raw inUsedEventStates]; destruct (Z.eqb slot eid).
      * exists new; reflexivity.
      * exists before; exact Hb.
Qed.

Lemma cross_module_registration_event_fields_update : forall sg s eid old new,
  s.(EventState).(inUsedEventStates) eid = Some old ->
  new.(eventType) = old.(eventType) -> new.(mutexFields) = old.(mutexFields) ->
  new.(waitList) = old.(waitList) -> cross_module_registration_consistency sg s ->
  cross_module_registration_consistency sg
    (replace_EventS (update_event_field_raw s.(EventState) eid new) s).
Proof.
  intros sg s eid old new Hold Htype Hmutex Hwait Hcross.
  unfold cross_module_registration_consistency in *.
  eapply cross_module_consistency_with_wait_event_mutex_transport.
  - intros slot node Hnode Hismutex; cbn [update_event_field_raw inUsedEventStates] in Hnode.
    destruct (Z.eqb slot eid) eqn:E.
    + apply Z.eqb_eq in E; subst slot; injection Hnode as Hnode; subst node; exists old; auto.
    + exists node; auto.
  - intros slot before Hb Hismutex; cbn [update_event_field_raw inUsedEventStates].
    destruct (Z.eqb slot eid) eqn:E.
    + apply Z.eqb_eq in E; subst slot; assert (before = old) by congruence; subst before.
      exists new; auto.
    + exists before; auto.
  - eapply event_registration_event_fields_update;
      [exact Hold|exact Htype|exact Hwait|exact (proj1 (proj2 (proj2 Hcross)))].
  - reflexivity.
  - exact Hcross.
Qed.
