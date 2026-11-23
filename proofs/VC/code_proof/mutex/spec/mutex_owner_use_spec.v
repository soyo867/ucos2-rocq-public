Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Import ListNotations.
Local Open Scope Z_scope.

(** The Event-wait part of the already selected Mutex client-use protocol.
    These are existing TCB fields, not extra state or memory permissions.
    This is NOT a consequence of arbitrary kernel validity: the kernel's
    defensive cross-object owner-wait path remains in the raw semantics.
    In particular a suspended/noncurrent owner is allowed, and a ready
    timed-out task need not yet have cleared its old Event registration.

    ChangePrio/Delete of held owners are other client obligations; the
    predicate here must not be advertised as that entire protocol. *)
Definition mutex_owner_event_unlinked
  (tasks : Glob_TaskAbstractState) (events : Glob_EventAbstractState) : Prop :=
  forall eid event mutex owner node,
    events.(inUsedEventStates) eid = Some event ->
    event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
    mutex.(mfOwner) = Some owner -> tasks.(inUsedTaskStates) owner = Some node ->
    node.(eventPtr) = None /\ node.(eventMultiWaitEvents) = [].

Definition task_holds_no_mutex (events : Glob_EventAbstractState) (tid : TaskID) : Prop :=
  forall eid event mutex,
    events.(inUsedEventStates) eid = Some event ->
    event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
    mutex.(mfOwner) <> Some tid.

Lemma mutex_owner_event_unlinked_empty : forall tasks events,
  (forall eid, events.(inUsedEventStates) eid = None) ->
  mutex_owner_event_unlinked tasks events.
Proof. intros tasks events Hempty eid event mutex owner node He; rewrite Hempty in He; discriminate. Qed.

Lemma mutex_owner_event_unlinked_update_task : forall tasks events tid new,
  mutex_owner_event_unlinked tasks events ->
  (forall eid event mutex,
    events.(inUsedEventStates) eid = Some event ->
    event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
    mutex.(mfOwner) = Some tid ->
    new.(eventPtr) = None /\ new.(eventMultiWaitEvents) = []) ->
  mutex_owner_event_unlinked (glob_task_set_usedtask tasks tid new) events.
Proof.
  intros tasks events tid new Huse Hnew eid event mutex owner node He Htype Hmutex Howner Hnode.
  cbn [glob_task_set_usedtask inUsedTaskStates] in Hnode.
  destruct (Z.eqb owner tid) eqn:E.
  - apply Z.eqb_eq in E; subst owner; injection Hnode as Hnode; subst node.
    eapply Hnew; eassumption.
  - eapply Huse; eassumption.
Qed.

Lemma mutex_owner_event_unlinked_task_fields_frame : forall tasks events tid old new,
  tasks.(inUsedTaskStates) tid = Some old ->
  new.(eventPtr) = old.(eventPtr) ->
  new.(eventMultiWaitEvents) = old.(eventMultiWaitEvents) ->
  mutex_owner_event_unlinked tasks events ->
  mutex_owner_event_unlinked (glob_task_set_usedtask tasks tid new) events.
Proof.
  intros tasks events tid old new Hold Hptr Hmulti Huse.
  apply mutex_owner_event_unlinked_update_task; [exact Huse|].
  intros eid event mutex He Htype Hmutex Howner; rewrite Hptr, Hmulti.
  eapply Huse; eassumption.
Qed.

Lemma mutex_owner_event_unlinked_event_fields_frame : forall tasks events eid old new,
  events.(inUsedEventStates) eid = Some old ->
  new.(eventType) = old.(eventType) -> new.(mutexFields) = old.(mutexFields) ->
  mutex_owner_event_unlinked tasks events ->
  mutex_owner_event_unlinked tasks (update_event_field_raw events eid new).
Proof.
  intros tasks events eid old new Hold Htype Hmutex Huse mid event mutex owner node
    He Hty Hm Ho Hnode.
  cbn [update_event_field_raw inUsedEventStates] in He.
  destruct (Z.eqb mid eid) eqn:E.
  - injection He as He; subst event; rewrite Htype in Hty; rewrite Hmutex in Hm.
    eapply Huse; eassumption.
  - eapply Huse; eassumption.
Qed.

(** The actual owner/count update used by successful Accept/Pend. An
    immediate nested acquisition is allowed. The caller supplies its real
    pre-acquisition EventPtr/MultiWait observation, not readiness alone. *)
Lemma owner_acquire_update_preserves_event_unlinked : forall tasks events eid event mutex tid prio node,
  mutex_owner_event_unlinked tasks events ->
  tasks.(inUsedTaskStates) tid = Some node ->
  node.(eventPtr) = None -> node.(eventMultiWaitEvents) = [] ->
  mutex_owner_event_unlinked tasks (owner_acquire_update events eid event mutex tid prio).
Proof.
  intros tasks events eid event mutex tid prio node Huse Hnode Hptr Hmulti
    mid found held owner current He Htype Hmutex Howner Hcurrent.
  unfold owner_acquire_update in He; cbn [update_event_field_raw inUsedEventStates] in He.
  destruct (Z.eqb mid eid) eqn:E.
  - injection He as He; subst found; cbn in Hmutex; injection Hmutex as Hmutex; subst held.
    cbn in Howner; injection Howner as Howner; subst owner.
    rewrite Hnode in Hcurrent; injection Hcurrent as Hcurrent; subst current; auto.
  - eapply Huse; eassumption.
Qed.

(** This is the previously selected application/client restriction at the
    real blocking branch, not a new guard inserted into OS_EventTaskWait.
    Merely requiring that the waiter not own the TARGET Mutex is weaker:
    it could still hold a different Mutex. *)
Lemma event_wait_preserves_mutex_owner_event_unlinked : forall sg state eid event tid old,
  state.(EventState).(inUsedEventStates) eid = Some event ->
  task_holds_no_mutex state.(EventState) tid ->
  mutex_owner_event_unlinked state.(TskState) state.(EventState) ->
  let after := event_wait_state sg state eid event tid old in
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros sg state eid event tid old He Hfree Huse.
  cbn zeta; unfold event_wait_state; cbn zeta.
  change (mutex_owner_event_unlinked
    (glob_task_set_usedtask state.(TskState) tid (task_set_event_ptr old (Some eid)))
    (update_event_field_raw state.(EventState) eid
      (event_insert_waiter sg
        (glob_task_set_usedtask state.(TskState) tid (task_set_event_ptr old (Some eid))) event tid))).
  eapply mutex_owner_event_unlinked_event_fields_frame;
    [exact He|reflexivity|reflexivity|].
  apply mutex_owner_event_unlinked_update_task; [exact Huse|].
  intros mid other held Hother Htype Hmutex Howner.
  exfalso; exact (Hfree mid other held Hother Htype Hmutex Howner).
Qed.

Lemma event_pend_preserves_mutex_owner_event_unlinked : forall sg state eid event tid old kind timeout,
  state.(EventState).(inUsedEventStates) eid = Some event ->
  task_holds_no_mutex state.(EventState) tid ->
  mutex_owner_event_unlinked state.(TskState) state.(EventState) ->
  let after := event_pend_state sg state eid event tid old kind timeout in
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof. intros; apply event_wait_preserves_mutex_owner_event_unlinked; assumption. Qed.

Lemma event_wake_preserves_mutex_owner_event_unlinked : forall sg state eid event tid old kind message result,
  state.(EventState).(inUsedEventStates) eid = Some event ->
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  mutex_owner_event_unlinked state.(TskState) state.(EventState) ->
  let after := event_wake_state sg state eid event tid old kind message result in
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros sg state eid event tid old kind message result He Hold Huse.
  cbn zeta; unfold event_wake_state; cbn zeta.
  change (mutex_owner_event_unlinked
    (glob_task_set_usedtask state.(TskState) tid (task_event_wake_single old kind message result))
    (update_event_field_raw state.(EventState) eid
      (event_set_wait_list event (remove_Z_eqb tid event.(waitList))))).
  eapply mutex_owner_event_unlinked_event_fields_frame;
    [exact He|reflexivity|reflexivity|].
  apply mutex_owner_event_unlinked_update_task; [exact Huse|].
  intros mid other held Hother Htype Hmutex Howner.
  split; [reflexivity|].
  exact (proj2 (Huse mid other held tid old Hother Htype Hmutex Howner Hold)).
Qed.

Lemma task_suspend_preserves_mutex_owner_event_unlinked : forall state tid node,
  state.(TskState).(inUsedTaskStates) tid = Some node ->
  mutex_owner_event_unlinked state.(TskState) state.(EventState) ->
  let after := task_suspend_state state tid node in
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros state tid node Hnode Huse.
  eapply mutex_owner_event_unlinked_task_fields_frame;
    [exact Hnode|reflexivity|reflexivity|exact Huse].
Qed.

Lemma task_resume_preserves_mutex_owner_event_unlinked : forall sg state tid node,
  state.(TskState).(inUsedTaskStates) tid = Some node ->
  mutex_owner_event_unlinked state.(TskState) state.(EventState) ->
  let after := task_resume_state sg state tid node in
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros sg state tid node Hnode Huse.
  eapply mutex_owner_event_unlinked_task_fields_frame;
    [exact Hnode|reflexivity|reflexivity|exact Huse].
Qed.

(** Task publication can change the old list head's links as well as add
    the new TCB. Reuse the real commit observation, rather than claim that
    every pre-existing TCB is byte-for-byte unchanged. *)
Lemma task_commit_preserves_mutex_owner_event_unlinked : forall tasks events priority invocation node,
  mutex_owner_event_unlinked tasks events ->
  node.(eventPtr) = None -> node.(eventMultiWaitEvents) = [] ->
  mutex_owner_event_unlinked (task_commit tasks priority invocation node) events.
Proof.
  intros tasks events priority invocation node Huse Hptr Hmulti
    eid event mutex owner current He Htype Hmutex Howner Hcurrent.
  destruct (Z.eq_dec owner node.(taskID)) as [->|Hneq].
  - rewrite (proj1 (task_commit_publication_fields_eq tasks priority invocation node)) in Hcurrent.
    injection Hcurrent as Hcurrent; subst current; split; assumption.
  - destruct (task_commit_lookup_old_fields tasks priority invocation node owner current Hneq Hcurrent)
      as [old [Hold Hfields]].
    pose proof (f_equal eventPtr Hfields) as Hptr_eq.
    pose proof (f_equal eventMultiWaitEvents Hfields) as Hmulti_eq.
    cbn [task_set_links eventPtr] in Hptr_eq.
    cbn [task_set_links eventMultiWaitEvents] in Hmulti_eq.
    rewrite Hptr_eq, Hmulti_eq; eapply Huse; eassumption.
Qed.

(** A concrete registered source family, with no added guard or certificate
    field: private writes preserve the used map; Publish already initializes
    both Event fields; invocation retirement changes neither field. *)
Lemma task_creation_client_preserves_mutex_owner_event_unlinked : forall action sg before after,
  kernel_client_step (task_creation_client action) sg before after ->
  mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros action sg before after [Hguard [Hname ->]] Huse.
  destruct action; cbn [task_lifecycle_action_guard] in Hguard.
  - exact Huse.
  - exact Huse.
  - destruct Hguard as [Hidentity [Hready [Hptr [Hmulti Hflag]]]].
    apply task_commit_preserves_mutex_owner_event_unlinked; assumption.
  - exact Huse.
Qed.

(** Actual registered steps need their own source-specific preservation
    proofs, such as the blocking/wake/frame rules above. This theorem uses
    the SAME trace as the region interval; it does not add an endpoint
    validity filter or assert a certificate for arbitrary ISR/application
    code. The CPU/physical-heap producer is a separate obligation. *)
Lemma kernel_client_trace_preserves_mutex_owner_event_unlinked :
  forall clients sg observer event_observer before stopped after,
  (forall action, clients action -> KernelClientCertificate action) ->
  (forall action initial final,
    clients action -> UCOS2_state_inv sg initial ->
    mutex_owner_event_unlinked initial.(TskState) initial.(EventState) ->
    kernel_client_step action sg initial final ->
    mutex_owner_event_unlinked final.(TskState) final.(EventState)) ->
  kernel_client_resource_trace clients sg observer event_observer before stopped after ->
  UCOS2_state_inv sg before ->
  mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros clients sg observer event_observer before stopped after Hcert Huse Htrace.
  induction Htrace as [state|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intros Hvalid Hbefore; [exact Hbefore|].
  apply IH.
  - exact (kernel_client_preserves_validity action (Hcert action Hin) sg before middle Hvalid Hstep).
  - eapply Huse; eassumption.
Qed.

Lemma critical_region_interval_preserves_mutex_owner_event_unlinked :
  forall critical sg invocation before after,
  (forall action initial final,
    critical_region_clients critical action -> UCOS2_state_inv sg initial ->
    mutex_owner_event_unlinked initial.(TskState) initial.(EventState) ->
    kernel_client_step action sg initial final ->
    mutex_owner_event_unlinked final.(TskState) final.(EventState)) ->
  critical_region_interval critical sg invocation before after ->
  UCOS2_state_inv sg before ->
  mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros critical sg invocation before after Huse Hinterval Hvalid Hbefore.
  eapply kernel_client_trace_preserves_mutex_owner_event_unlinked.
  - exact (critical_region_client_certificates critical).
  - exact Huse.
  - exact (critical_region_interval_raw_trace critical sg invocation before after Hinterval).
  - exact Hvalid.
  - exact Hbefore.
Qed.

(** Consumer needed by native Del's priority relocation: use the current
    acquired owner, not an old cached TCB or a guessed ready/nonready fact.
    Existing Event consistency connects the actual EventPtr to all bitmaps.
    This selected-profile consumer does not claim a Multi C API proof. *)
Lemma mutex_owner_event_unlinked_not_waiter : forall sg tasks events eid event mutex owner node,
  event_in_range sg tasks events -> mutex_owner_event_unlinked tasks events ->
  events.(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> tasks.(inUsedTaskStates) owner = Some node ->
  forall mid other, events.(inUsedEventStates) mid = Some other -> ~ In owner other.(waitList).
Proof.
  intros sg tasks events eid event mutex owner node
    [_ [_ [_ [_ [_ [_ Hentries]]]]]] Huse He Htype Hmutex Howner Hnode.
  eapply event_unregistered_task_not_waiting; [exact Hentries|exact Hnode|].
  exact (proj1 (Huse eid event mutex owner node He Htype Hmutex Howner Hnode)).
Qed.

Lemma critical_region_interval_mutex_owner_not_waiter :
  forall critical sg invocation before entry eid event mutex owner node,
  (forall action initial final,
    critical_region_clients critical action -> UCOS2_state_inv sg initial ->
    mutex_owner_event_unlinked initial.(TskState) initial.(EventState) ->
    kernel_client_step action sg initial final ->
    mutex_owner_event_unlinked final.(TskState) final.(EventState)) ->
  critical_region_interval critical sg invocation before entry ->
  UCOS2_state_inv sg before ->
  mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> entry.(TskState).(inUsedTaskStates) owner = Some node ->
  forall mid other, entry.(EventState).(inUsedEventStates) mid = Some other ->
    ~ In owner other.(waitList).
Proof.
  intros critical sg invocation before entry eid event mutex owner node
    Hclients Hinterval Hvalid Hbefore He Htype Hmutex Howner Hnode.
  pose proof (critical_region_interval_preserves_mutex_owner_event_unlinked
    critical sg invocation before entry Hclients Hinterval Hvalid Hbefore) as Hentry.
  destruct (critical_region_interval_transports_resources critical sg invocation
    before entry Hinterval Hvalid) as [Hentryvalid _].
  destruct Hentryvalid as [_ [_ [_ [Hevents _]]]].
  eapply mutex_owner_event_unlinked_not_waiter; eassumption.
Qed.
