Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.helpers Ucos2Verify.lib.task Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.atomic_ops_lib Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.core.spec.kernel_boot_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_owner_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_publication_environment_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_owner_history_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Import TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.

(** A normal application-call point, not an arbitrary ready TCB. A Pend
    continuation reaches this point only after its returning cleanup;
    being scheduled while its old EventPtr remains is not sufficient.
    This local observation is distinct from the global held-owner invariant. *)
Definition mutex_task_call_point (tasks : Glob_TaskAbstractState) (tid : TaskID) : Prop :=
  exists node, tasks.(inUsedTaskStates) tid = Some node /\
    node.(eventPtr) = None /\ node.(eventMultiWaitEvents) = [].

Lemma mutex_task_call_point_after_pend_cleanup : forall tasks tid old multi clear_message,
  (multi = true \/ old.(eventMultiWaitEvents) = []) ->
  mutex_task_call_point
    (glob_task_set_usedtask tasks tid (task_event_pend_cleanup multi clear_message old)) tid.
Proof.
  intros tasks tid old multi clear_message Hmulti.
  exists (task_event_pend_cleanup multi clear_message old); split.
  - cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
  - destruct multi, clear_message; cbn in *; intuition congruence.
Qed.

Lemma atomic_mutex_acquire_preserves_owner_use : forall eid tid priority before after,
  mutex_task_call_point before.(TskState) tid ->
  atomic_mutex_acquire eid tid priority before tt after ->
  mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros eid tid priority before after [current [Hcurrent [Hptr Hmulti]]] Hstep Huse.
  destruct Hstep as (event & acquired & mutex & owned & node & He & Htype & Hfields & Hfree &
    Hcur & Hnode & Hpriority & Hready & -> & -> & ->).
  assert (node = current) by congruence; subst node.
  change (mutex_owner_event_unlinked before.(TskState)
    (owner_acquire_update before.(EventState) eid event mutex tid priority)).
  eapply owner_acquire_update_preserves_event_unlinked; eassumption.
Qed.

Lemma atomic_mutex_release_preserves_owner_use : forall sg eid before after,
  atomic_mutex_release sg eid before tt after ->
  mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros sg eid before after Hstep Huse.
  destruct Hstep as (event & released & mutex & empty & owner & events & tasks &
    He & Htype & Hfields & Hwait & Howner & -> & -> & -> & -> & ->).
  intros mid found held tid node Hget Hkind Hmutex Hheld Hnode.
  cbn [EventState update_event_field_raw inUsedEventStates] in Hget.
  destruct (Z.eqb mid eid).
  - injection Hget as <-; cbn in Hmutex; injection Hmutex as <-; discriminate Hheld.
  - eapply Huse; eassumption.
Qed.

Lemma atomic_mutex_handover_preserves_owner_use : forall sg eid before tid after,
  UCOS2_state_inv sg before ->
  atomic_mutex_release_with_handover sg eid before tid after ->
  mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros sg eid before tid after Hvalid Hstep Huse.
  destruct Hstep as (event & handed & mutex & owned & owner & old & awakened & events & tasks &
    scheduler & scheduled & ready & rest & He & Htype & Hfields & Howner & Hwait & Hold &
    Hawakened & Howned & Hhanded & Hevents & Hscheduler & Hready & Hscheduled & Htasks & Hafter).
  assert (Hmulti : old.(eventMultiWaitEvents) = []).
  { destruct Hvalid as [_ [_ [_ [Hevents_valid _]]]].
    destruct Hevents_valid as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
    destruct (event_waiter_task_fields sg before.(TskState) eid event tid
      (Hentries eid event He) ltac:(rewrite Hwait; left; reflexivity))
      as [node [kind [Hnode [_ [_ [Hnone _]]]]]].
    assert (node = old) by congruence; subst node; exact Hnone. }
  subst after tasks scheduled ready scheduler events handed owned awakened.
  intros mid found held task node Hget Hkind Hmutex Hheld Hnode.
  cbn [TskState inUsedTaskStates] in Hnode.
  cbn [EventState update_event_field_raw inUsedEventStates] in Hget.
  destruct (Z.eqb mid eid).
  - injection Hget as <-; cbn in Hmutex; injection Hmutex as <-.
    cbn in Hheld; injection Hheld as <-.
    rewrite Z.eqb_refl in Hnode; injection Hnode as <-; cbn; split; [reflexivity|exact Hmulti].
  - destruct (Z.eqb task tid).
    + injection Hnode as <-; cbn; split; [reflexivity|exact Hmulti].
    + eapply Huse; eassumption.
Qed.

Lemma task_pend_cleanup_preserves_owner_use : forall state tid old multi clear_message,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  mutex_owner_event_unlinked state.(TskState) state.(EventState) ->
  mutex_owner_event_unlinked
    (glob_task_set_usedtask state.(TskState) tid (task_event_pend_cleanup multi clear_message old))
    state.(EventState).
Proof.
  intros state tid old multi clear_message Hold Huse.
  apply mutex_owner_event_unlinked_update_task; [exact Huse|].
  intros eid event mutex He Htype Hfields Howner.
  pose proof (proj2 (Huse eid event mutex tid old He Htype Hfields Howner Hold)) as Hmulti.
  destruct multi, clear_message; cbn; split; try reflexivity; exact Hmulti.
Qed.

(** Source-operation classification for the approved client-use protocol.
    There is no "poststate satisfies owner-use" constructor. The only
    application restriction at a new blocking publication is that its
    task owns no Mutex; immediate nested acquisition remains allowed.

    The field-frame constructors are explicit write footprints, not a
    claim that arbitrary IRQs are harmless. A source adapter must prove
    the actual maps/fields equal before using them. Error returns use the
    unchanged-map constructor and are not erased. This relation covers
    this owner-use projection, not all kernel correctness properties. *)
Inductive mutex_owner_source_step (sg : StableGlobVars) :
  UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| MutexOwnerSourceFrame : forall before after,
    after.(TskState).(inUsedTaskStates) = before.(TskState).(inUsedTaskStates) ->
    after.(EventState).(inUsedEventStates) = before.(EventState).(inUsedEventStates) ->
    mutex_owner_source_step sg before after
| MutexOwnerSourceTaskField : forall before after tid old new,
    before.(TskState).(inUsedTaskStates) tid = Some old ->
    new.(eventPtr) = old.(eventPtr) -> new.(eventMultiWaitEvents) = old.(eventMultiWaitEvents) ->
    after.(TskState) = glob_task_set_usedtask before.(TskState) tid new ->
    after.(EventState) = before.(EventState) -> mutex_owner_source_step sg before after
| MutexOwnerSourceEventField : forall before after eid old new,
    before.(EventState).(inUsedEventStates) eid = Some old ->
    new.(eventType) = old.(eventType) -> new.(mutexFields) = old.(mutexFields) ->
    after.(EventState) = update_event_field_raw before.(EventState) eid new ->
    after.(TskState) = before.(TskState) -> mutex_owner_source_step sg before after
| MutexOwnerSourceTaskLifecycle : forall before after action,
    kernel_client_step (task_creation_client action) sg before after -> mutex_owner_source_step sg before after
| MutexOwnerSourceTaskPublication : forall before after publication,
    kernel_client_step (task_create_stack_publication_client publication) sg before after ->
    mutex_owner_source_step sg before after
| MutexOwnerSourceCreate : forall before after pcp result,
    MutexCreatePublication.critical_operation sg pcp before result after ->
    mutex_owner_source_step sg before after
| MutexOwnerSourceAcquire : forall before after eid tid priority,
    mutex_task_call_point before.(TskState) tid ->
    atomic_mutex_acquire eid tid priority before tt after -> mutex_owner_source_step sg before after
| MutexOwnerSourceWait : forall before eid event tid old kind timeout,
    before.(EventState).(inUsedEventStates) eid = Some event ->
    task_holds_no_mutex before.(EventState) tid ->
    mutex_owner_source_step sg before (event_pend_state sg before eid event tid old kind timeout)
| MutexOwnerSourceWake : forall before eid event tid old kind message result,
    before.(EventState).(inUsedEventStates) eid = Some event ->
    before.(TskState).(inUsedTaskStates) tid = Some old ->
    mutex_owner_source_step sg before (event_wake_state sg before eid event tid old kind message result)
| MutexOwnerSourceCleanup : forall before tid old multi clear_message,
    before.(TskState).(inUsedTaskStates) tid = Some old ->
    mutex_owner_source_step sg before
      (replace_TskS (glob_task_set_usedtask before.(TskState) tid
        (task_event_pend_cleanup multi clear_message old)) before)
| MutexOwnerSourceRelease : forall before after eid,
    atomic_mutex_release sg eid before tt after -> mutex_owner_source_step sg before after
| MutexOwnerSourceHandover : forall before after eid tid,
    UCOS2_state_inv sg before -> atomic_mutex_release_with_handover sg eid before tid after ->
    mutex_owner_source_step sg before after
| MutexOwnerSourcePrepare : forall before after mutex,
    mutex_del_prepare sg mutex before after -> mutex_owner_source_step sg before after
| MutexOwnerSourceRecycle : forall before eid event,
    mutex_owner_source_step sg before (mutex_del_recycle_state sg eid event before)
| MutexOwnerSourceCreator : forall creator cut before next after,
    kernel_client_heap_state_step (mutex_del_creator_publication_effect creator) sg cut before next after ->
    mutex_owner_source_step sg before after
| MutexOwnerSourceNonMutexPublication : forall before eid event,
    event.(eventType) <> OS_EVENT_TYPE_MUTEX ->
    mutex_owner_source_step sg before
      (replace_EventS (event_publish before.(EventState) eid event) before).

Lemma mutex_owner_source_step_preserves_owner_use : forall sg before after,
  mutex_owner_source_step sg before after ->
  mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros sg before after Hsource Huse; destruct Hsource.
  - unfold mutex_owner_event_unlinked in *; rewrite H, H0; exact Huse.
  - rewrite H2, H3; eapply mutex_owner_event_unlinked_task_fields_frame; eassumption.
  - rewrite H2, H3; eapply mutex_owner_event_unlinked_event_fields_frame; eassumption.
  - eapply task_creation_client_preserves_mutex_owner_event_unlinked; eassumption.
  - eapply mutex_del_stack_publication_preserves_owner_use; eassumption.
  - eapply mutex_del_publication_preserves_owner_use; eassumption.
  - eapply atomic_mutex_acquire_preserves_owner_use; eassumption.
  - apply event_pend_preserves_mutex_owner_event_unlinked; assumption.
  - apply event_wake_preserves_mutex_owner_event_unlinked; assumption.
  - exact (task_pend_cleanup_preserves_owner_use before tid old multi clear_message H Huse).
  - eapply atomic_mutex_release_preserves_owner_use; eassumption.
  - eapply atomic_mutex_handover_preserves_owner_use; eassumption.
  - eapply mutex_del_prepare_preserves_owner_use; eassumption.
  - apply mutex_del_recycle_preserves_owner_use; exact Huse.
  - eapply mutex_del_creator_state_step_preserves_owner_use; eassumption.
  - intros mid found mutex owner node He Htype Hfields Howner Hnode.
    cbn [replace_EventS EventState event_publish inUsedEventStates] in He.
    unfold kernel_map_set in He; destruct (Z.eq_dec mid eid).
    + injection He as <-; contradiction.
    + eapply Huse; eassumption.
Qed.

Inductive mutex_owner_source_history (sg : StableGlobVars) (boot : UCOS2_Verify_State) :
  UCOS2_Verify_State -> Prop :=
| MutexOwnerHistoryBoot : mutex_owner_source_history sg boot boot
| MutexOwnerHistoryStep : forall before after,
    mutex_owner_source_history sg boot before -> mutex_owner_source_step sg before after ->
    mutex_owner_source_history sg boot after.

Lemma mutex_owner_source_history_trans : forall sg first middle last,
  mutex_owner_source_history sg first middle ->
  mutex_owner_source_history sg middle last ->
  mutex_owner_source_history sg first last.
Proof.
  intros sg first middle last Hfirst Hlast; induction Hlast.
  - exact Hfirst.
  - econstructor; eassumption.
Qed.

Lemma mutex_owner_source_step_history : forall sg before after,
  mutex_owner_source_step sg before after -> mutex_owner_source_history sg before after.
Proof. intros; econstructor; [constructor|eassumption]. Qed.

Lemma mutex_owner_source_history_establishes_owner_use : forall sg boot state,
  (forall eid, boot.(EventState).(inUsedEventStates) eid = None) ->
  mutex_owner_source_history sg boot state ->
  mutex_owner_event_unlinked state.(TskState) state.(EventState).
Proof.
  intros sg boot state Hempty Hhistory; induction Hhistory.
  - apply mutex_owner_event_unlinked_empty; exact Hempty.
  - eapply mutex_owner_source_step_preserves_owner_use; eassumption.
Qed.

(** This is the already approved external calling/source protocol. It
    classifies each ACTUAL registered edge in the same region trace; it
    does not assert endpoint owner-use, CPU permission or arbitrary handler
    preservation. Application/ISR implementations are outside this proof.
    Kernel source adapters above and their physical producers justify the
    classified operations; adding a new operation requires its own case. *)
Definition mutex_owner_region_source_protocol (critical : CriticalRegionResources)
  (sg : StableGlobVars) : Prop :=
  forall action before after,
    critical.(critical_region_clients) action -> UCOS2_state_inv sg before ->
    kernel_client_step action sg before after ->
    mutex_owner_source_history sg before after.

Lemma mutex_owner_region_interval_history : forall critical sg boot invocation before after,
  mutex_owner_region_source_protocol critical sg ->
  mutex_owner_source_history sg boot before ->
  UCOS2_state_inv sg before ->
  critical_region_interval critical sg invocation before after ->
  mutex_owner_source_history sg boot after.
Proof.
  intros critical sg boot invocation before after Hprotocol Hhistory Hvalid Hinterval.
  pose proof (critical_region_interval_raw_trace critical sg invocation before after Hinterval) as Htrace.
  clear Hinterval.
  revert Hhistory Hvalid; induction Htrace; intros Hhistory Hvalid; [exact Hhistory|].
  apply IHHtrace.
  - eapply mutex_owner_source_history_trans; [exact Hhistory|]. eapply Hprotocol; eassumption.
  - exact (kernel_client_preserves_validity action
      (critical_region_client_certificates critical action H) sg before middle Hvalid H2).
Qed.

Lemma mutex_owner_region_interval_establishes_owner_use :
  forall critical sg task_name flag_name memory_name names invocation before entry,
  mutex_owner_region_source_protocol critical sg ->
  mutex_owner_source_history sg
    (UCOS2_boot_state sg task_name flag_name memory_name names) before ->
  UCOS2_state_inv sg before ->
  critical_region_interval critical sg invocation before entry ->
  mutex_owner_event_unlinked entry.(TskState) entry.(EventState).
Proof.
  intros critical sg task_name flag_name memory_name names invocation before entry
    Hprotocol Hhistory Hvalid Hinterval.
  eapply mutex_owner_source_history_establishes_owner_use with
    (sg := sg) (boot := UCOS2_boot_state sg task_name flag_name memory_name names).
  - intros; reflexivity.
  - eapply mutex_owner_region_interval_history; eassumption.
Qed.

Definition mutex_owner_program_history sg state : Prop :=
  exists task_name flag_name memory_name names,
    mutex_owner_source_history sg
      (UCOS2_boot_state sg task_name flag_name memory_name names) state.

Lemma mutex_owner_save_source_establishes_owner_use :
  forall external port critical sg original returned mask saved before entry,
  mutex_owner_region_source_protocol critical sg ->
  mutex_owner_program_history sg before -> UCOS2_state_inv sg before ->
  kernel_call_save_source external port critical sg original returned mask saved before entry ->
  mutex_owner_event_unlinked entry.(TskState) entry.(EventState).
Proof.
  intros external port critical sg original returned mask saved before entry Hprotocol
    [task_name [flag_name [memory_name [names Hhistory]]]] Hvalid Hsource.
  eapply mutex_owner_region_interval_establishes_owner_use; try eassumption.
  eapply kernel_call_save_source_region_interval; eassumption.
Qed.
