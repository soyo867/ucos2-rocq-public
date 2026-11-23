Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_handle_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_wake_source_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.event Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.mutex_query_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** These local frames are consumed by the actual MutexDeleteAlways heap
    constructor below. They require neither quiescent ready membership nor
    an invented validity premise at the owner's intermediate priority cut. *)
Local Lemma tmr_task_mutex_delete_prepare_timer_eq : forall sg mutex before after,
  mutex_del_prepare sg mutex before after -> after.(TimerState) = before.(TimerState).
Proof.
  intros sg mutex before after Hprepare; unfold mutex_del_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis));
    [subst after; reflexivity|].
  destruct mutex.(mfOwner) as [owner|].
  - destruct Hprepare as [node [priority [_ [_ ->]]]].
    unfold mutex_del_owner_priority_state; destruct Z.eq_dec; reflexivity.
  - subst after; reflexivity.
Qed.

Local Lemma tmr_task_mutex_delete_ready_other_event :
  forall sg before selected kind message result priority after eid previous,
  event_task_rdy sg before selected kind message result = Some (priority, after) ->
  eid <> selected -> mutex_query_lookup before eid previous ->
  after.(TimerState) = before.(TimerState) /\ mutex_query_lookup after eid previous.
Proof.
  intros sg before selected kind message result priority after eid previous Hstep Hneq Hlookup.
  unfold event_task_rdy in Hstep.
  destruct (before.(EventState).(inUsedEventStates) selected) as [event|] eqn:Hselected;
    [|discriminate].
  destruct (before.(TskState).(prioTbl) (event_wait_priority before.(TskState) event))
    as [| |tid] eqn:Htable; try discriminate.
  destruct (before.(TskState).(inUsedTaskStates) tid) as [old|] eqn:Hold;
    [|discriminate].
  inversion Hstep; subst after; split; [reflexivity|].
  unfold mutex_query_lookup in *.
  cbn [event_wake_state replace_SchedS replace_EventS replace_TskS EventState
    update_event_field_raw inUsedEventStates].
  rewrite (proj2 (Z.eqb_neq eid selected) Hneq); exact Hlookup.
Qed.

Local Lemma tmr_task_mutex_delete_broadcast_other_event :
  forall sg selected kind message result before priorities after,
  event_broadcast sg selected kind message result before priorities after ->
  after.(TimerState) = before.(TimerState) /\
  forall eid previous, eid <> selected -> mutex_query_lookup before eid previous ->
    mutex_query_lookup after eid previous.
Proof.
  intros sg selected kind message result before priorities after Hrun.
  induction Hrun as [state event Hlookup Hzero|
    state event priority middle priorities after Hlookup Hnonzero Hstep Htail [Htimer Hother]].
  - split; [reflexivity|]; intros; assumption.
  - assert (Hmiddle_timer : middle.(TimerState) = state.(TimerState)).
    { unfold event_task_rdy in Hstep; rewrite Hlookup in Hstep.
      destruct (state.(TskState).(prioTbl) (event_wait_priority state.(TskState) event))
        as [| |tid] eqn:Htable; try discriminate.
      destruct (state.(TskState).(inUsedTaskStates) tid) as [old|] eqn:Hold;
        [|discriminate].
      inversion Hstep; reflexivity. }
    split; [rewrite Htimer; exact Hmiddle_timer|].
    intros eid previous Hneq Hprevious; apply Hother; [exact Hneq|].
    exact (proj2 (tmr_task_mutex_delete_ready_other_event sg state selected kind
      message result priority middle eid previous Hstep Hneq Hprevious)).
Qed.

(** The selected deletion target is a MUTEX. A live SEM therefore has a
    different key, by the two real map lookups and their actual types.
    The theorem covers all critical result branches, including errors. *)
Lemma tmr_task_mutex_delete_critical_signal_frame :
  forall sg selected option before result after,
  mutex_del_critical sg selected option before result after ->
  after.(TimerState) = before.(TimerState) /\
  forall eid previous, mutex_query_lookup before eid previous ->
    previous.(eventType) = OS_EVENT_TYPE_SEM -> mutex_query_lookup after eid previous.
Proof.
  intros sg selected option before result after
    [event [mutex [Hselected [Htype [Hfields Hsource]]]]].
  assert (Hdifferent : forall eid previous,
    mutex_query_lookup before eid previous -> previous.(eventType) = OS_EVENT_TYPE_SEM ->
    eid <> selected).
  { intros eid previous Hlookup Hsem Hequal; subst eid.
    unfold mutex_query_lookup in Hlookup.
    assert (previous = event) by congruence; subst previous; congruence. }
  assert (Hprepared : forall prepared,
    mutex_del_prepare sg mutex before prepared ->
    prepared.(TimerState) = before.(TimerState) /\
    forall eid previous, mutex_query_lookup before eid previous ->
      mutex_query_lookup prepared eid previous).
  { intros prepared Hprepare; split.
    - eapply tmr_task_mutex_delete_prepare_timer_eq; exact Hprepare.
    - intros eid previous Hlookup; unfold mutex_query_lookup in *.
      rewrite (mutex_del_prepare_event_state_eq sg mutex before prepared Hprepare);
        exact Hlookup. }
  destruct (Z.eq_dec option 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
    + destruct Hsource as [prepared [Hprepare [-> Hresult]]].
      destruct (Hprepared prepared Hprepare) as [Htimer Hlookup].
      split; [exact Htimer|]. intros eid previous Hprevious Hsem.
      eapply tmr_task_signal_recycle_other_preserves_lookup.
      * eapply Hdifferent; eassumption.
      * apply Hlookup; exact Hprevious.
    + destruct Hsource as [-> Hresult]; split; [reflexivity|]; intros; assumption.
  - destruct (Z.eq_dec option 1).
    + destruct Hsource as [prepared [priorities [drained
        [Hprepare [Hbroadcast [-> Hresult]]]]]].
      destruct (Hprepared prepared Hprepare) as [Htimer Hlookup].
      destruct (tmr_task_mutex_delete_broadcast_other_event sg selected PendMutex
        0 PendAbort prepared priorities drained Hbroadcast) as [Hdrained Hother].
      split; [change (drained.(TimerState) = before.(TimerState));
        rewrite Hdrained; exact Htimer|]. intros eid previous Hprevious Hsem.
      eapply tmr_task_signal_recycle_other_preserves_lookup.
      * eapply Hdifferent; eassumption.
      * apply Hother; [eapply Hdifferent; eassumption|apply Hlookup; exact Hprevious].
    + destruct Hsource as [-> Hresult]; split; [reflexivity|]; intros; assumption.
Qed.

(** Direct consumer for SchedTaskPhaseHeapMutexDeleteAlways. The exact
    prepare/loop/recycle execution produces Hcritical; no endpoint property
    is added to its relation or to its original C contract. *)
Lemma tmr_task_mutex_delete_heap_source_preserves_signal_identity :
  forall (external : OsSchedExternalResources) critical sg invocation selected entry prepared event mutex
    before_heap after_heap (frame : Assertion),
  mutex_del_parent_layout sg -> event_object_layout_prop sg selected ->
  mutex_del_parent_entry sg selected entry event mutex ->
  (kernel_program_inv sg entry ** frame) before_heap ->
  sched_task_mutex_del_always_execution sg selected entry prepared before_heap after_heap ->
  tmr_task_signal_lifetime critical sg invocation entry ->
  tmr_task_signal_identity_preserved sg entry
    (mutex_del_always_checkpoint sg selected event prepared).
Proof.
  intros external critical sg invocation selected entry prepared event mutex before_heap after_heap
    frame Hlayout Hobject Hentry Hheap Hsource Hlife.
  destruct (sched_task_mutex_del_always_source_resources external sg selected entry prepared event mutex
    before_heap after_heap frame Hlayout Hobject Hentry Hheap Hsource)
    as [Hphase [Hcritical Hafter]].
  destruct (tmr_task_mutex_delete_critical_signal_frame sg selected 1 entry
    (0, (OS_ERR_NONE, negb (Z.eqb (encode_event_wait_grp event.(waitList) entry.(TskState)) 0)))
    (mutex_del_always_checkpoint sg selected event prepared) Hcritical) as [Htimer Hlookup].
  split; [rewrite Htimer; reflexivity|].
  intros eid previous Hnonnull Haddress Hprevious.
  destruct Hlife as [Hnull|[signal [node
    [Hsignal_nonnull [Hsignal_address [Hvalid [Hnode [Hsem Hprotocol]]]]]]]];
    [contradiction|].
  assert (Hequal : eid = signal).
  { apply (event_addr_injective sg); congruence. }
  subst eid; assert (previous = node) by (unfold mutex_query_lookup in *; congruence).
  subst previous; exists node; split; [apply Hlookup; assumption|]. split; reflexivity.
Qed.

Lemma tmr_task_mutex_delete_heap_source_preserves_signal_lifetime :
  forall (external : OsSchedExternalResources) critical sg invocation selected entry prepared event mutex
    before_heap after_heap (frame : Assertion),
  mutex_del_parent_layout sg -> event_object_layout_prop sg selected ->
  mutex_del_parent_entry sg selected entry event mutex ->
  (kernel_program_inv sg entry ** frame) before_heap ->
  sched_task_mutex_del_always_execution sg selected entry prepared before_heap after_heap ->
  tmr_task_signal_lifetime critical sg invocation entry ->
  tmr_task_signal_lifetime critical sg invocation
    (mutex_del_always_checkpoint sg selected event prepared).
Proof.
  intros external critical sg invocation selected entry prepared event mutex before_heap after_heap
    frame Hlayout Hobject Hentry Hheap Hsource Hlife.
  eapply tmr_task_signal_lifetime_preserved; [exact Hlife|].
  eapply (tmr_task_mutex_delete_heap_source_preserves_signal_identity external); eassumption.
Qed.

(** Each actual TaskDel environment interval retains its own observer.
    Its resumption source also records the real public Timer trace. This
    establishes the signal value even at Prepared, without claiming that
    the live Event object has been preserved. *)
Lemma tmr_task_delete_environment_source_signal_value :
  forall environment critical saved_local requested sg completed phase loan
    original before returned after mask initial_heap final_heap frame,
  sched_task_delete_environment_execution environment critical saved_local requested
    sg completed phase loan original before returned after mask initial_heap final_heap frame ->
  after.(TimerState).(timerSignalSem) = before.(TimerState).(timerSignalSem).
Proof.
  intros environment critical saved_local requested sg completed phase loan original
    before returned after mask initial_heap final_heap frame Hsource.
  destruct (sched_task_delete_environment_source_resources environment critical saved_local
    requested sg completed phase loan original before returned after mask initial_heap
    final_heap frame Hsource) as [Htrace Hrest].
  eapply tmr_task_signal_public_trace_value.
  eapply kernel_resumption_resource_trace_timer_projection.
  exact (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)).
Qed.

(** The actual Restore and Save environment calls remain distinct. The
    established window producer supplies their two original source traces
    on the same middle state/heap; no observer is renamed or reconstructed. *)
Lemma tmr_task_delete_window_source_signal_value : forall environment critical sg
  before initial_heap after final_heap,
  sched_task_delete_window_execution environment critical sg before initial_heap after final_heap ->
  after.(TimerState).(timerSignalSem) = before.(TimerState).(timerSignalSem).
Proof.
  intros environment critical sg before initial_heap after final_heap Hsource.
  destruct Hsource as [saved_local requested completed arch restore save original initial
    first acquired priority tid node prepared loan saved cursor initial_heap written
    prefix_heap middle between restore_environment_heap final_cursor middle_heap registers
    returned resumed save_environment_heap final_registers reacquired final_heap frame
    Henv Hprep Hr0 Hmask Hpre Hprefix Hactual_restore Hsuffix_restore Hactual_save
    Hreturn Hvalid Hsave_mask Hsuffix_save].
  destruct (task_delete_prepared_restore_save_window environment critical saved_local
    requested sg completed arch restore save original initial first acquired priority
    tid node prepared loan saved cursor initial_heap written prefix_heap middle between
    restore_environment_heap final_cursor middle_heap registers returned resumed
    save_environment_heap final_registers reacquired final_heap frame Henv Hprep Hr0 Hmask
    Hpre Hprefix Hactual_restore Hsuffix_restore Hactual_save Hreturn Hvalid Hsave_mask Hsuffix_save)
    as [Hreturn_word [Hstate [Hrestore_history [Hsave_history Hrest]]]].
  destruct Hrestore_history as [Hrestore_trace Hrestore_rest].
  destruct Hsave_history as [Hsave_trace Hsave_rest].
  assert (Hfirst : between.(TimerState).(timerSignalSem) =
    (task_delete_locked prepared).(TimerState).(timerSignalSem)).
  { eapply tmr_task_signal_public_trace_value.
    eapply kernel_resumption_resource_trace_timer_projection.
    exact (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Hrestore_trace)). }
  assert (Hlast : resumed.(TimerState).(timerSignalSem) = between.(TimerState).(timerSignalSem)).
  { eapply tmr_task_signal_public_trace_value.
    eapply kernel_resumption_resource_trace_timer_projection.
    exact (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Hsave_trace)). }
  congruence.
Qed.

Lemma tmr_task_phase_heap_step_signal_value : forall environment critical sg
  before before_heap after after_heap,
  sched_task_phase_heap_step environment critical sg before before_heap after after_heap ->
  after.(TimerState).(timerSignalSem) = before.(TimerState).(timerSignalSem).
Proof.
  intros environment critical sg before before_heap after after_heap Hsource.
  destruct Hsource.
  - destruct (sched_task_mutex_del_always_source_resources environment.(task_stack_call_external)
      sg eid entry prepared event mutex before_heap after_heap frame H H0 H1 H2 H3)
      as [Hphase [Hcritical Hafter]].
    rewrite (proj1 (tmr_task_mutex_delete_critical_signal_frame _ _ _ _ _ _ Hcritical)); reflexivity.
  - eapply tmr_task_delete_environment_source_signal_value; exact H.
  - eapply tmr_task_delete_window_source_signal_value; exact H.
Qed.

Lemma tmr_task_phase_heap_source_signal_value : forall environment critical sg
  before before_heap after after_heap,
  sched_task_phase_heap_source environment critical sg before before_heap after after_heap ->
  after.(TimerState).(timerSignalSem) = before.(TimerState).(timerSignalSem).
Proof.
  intros environment critical sg before before_heap after after_heap Hsource.
  induction Hsource.
  - reflexivity.
  - rewrite IHHsource; eapply tmr_task_phase_heap_step_signal_value; exact H.
Qed.

(** NULL is a complete branch through all three actual heap constructors,
    including either Prepared environment interval. No public ECB owner,
    stable-state assumption, or foreign-actor proof is required for NULL. *)
Lemma tmr_task_phase_heap_source_null_signal_lifetime : forall environment critical sg invocation
  before before_heap after after_heap,
  sched_task_phase_heap_source environment critical sg before before_heap after after_heap ->
  before.(TimerState).(timerSignalSem) = 0 ->
  tmr_task_signal_lifetime critical sg invocation after.
Proof.
  intros environment critical sg invocation before before_heap after after_heap Hsource Hnull.
  left; rewrite (tmr_task_phase_heap_source_signal_value _ _ _ _ _ _ _ Hsource); exact Hnull.
Qed.
