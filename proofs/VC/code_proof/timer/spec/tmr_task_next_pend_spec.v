Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_annotation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.kernel_runtime_inv.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.

(** Consequences for OSTmr_Task's next literal OSSemPend call.  These
    lemmas neither modify its public domain nor assert a law of arbitrary
    callbacks.  In particular the signal's current public-slot ownership
    and guarded handle protocol remain explicit inputs of that call.

    A non-NULL signal may now name a FREE or wrong-type public ECB.  It is
    not required to retain its old generation throughout a callback.  The
    live-handle protocol is consumed only by the next SEM/clear-counter
    acquisition.  Private creator-owned storage is not a public ECB. *)

Lemma tmr_task_pend_owned_runtime_nonblocking :
  forall environment critical sg call signal before eid,
  sem_pend_runtime_nonblocking critical sg call (Some environment)
    signal before eid.
Proof. intros environment critical sg call signal before eid Hnone; discriminate. Qed.

(** Acquired layout is static program interpretation, not a future-ready
    premise.  The very same acquisition observation supplies both current
    validity and current live lookup; the pool owner supplies the ID bound.
    Thus this implication also covers a NULL/error entry without demanding
    an arbitrary dummy eid be valid at that entry. *)
Lemma tmr_task_pend_acquired_layout_from_table :
  forall environment critical sg call before eid,
  event_table_layout_prop sg ->
  sem_pend_observed_blocking_layout environment critical sg call before eid
    sg.(g_OSTCBCur) sg.(g_OSRdyGrp) sg.(g_OSRdyTbl).
Proof.
  intros environment critical sg call before eid Htable
    returned mask saved acquired observed current Hacquire Hzero.
  destruct (sem_pend_optional_acquire_fields environment critical sg call returned
    mask saved before acquired eid observed current Hacquire)
    as [Hsame [Hsaved [Hvalid [Hbefore [Hcurrent Hrest]]]]].
  pose proof Hvalid as [_ [_ [_ [[Hpool _] _]]]].
  pose proof (proj1 (event_pool_used_not_free sg acquired.(EventState) eid current
    Hpool Hcurrent)) as Hid.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  exact (event_table_layout_select sg eid Htable Hid).
Qed.

Lemma tmr_task_pend_input_null : forall critical sg invocation before eid observed,
  sem_pend_call_input critical sg invocation 0 before eid observed.
Proof. intros; left; reflexivity. Qed.

Lemma tmr_task_pend_input_public_used :
  forall critical sg invocation signal before eid observed,
  UCOS2_state_inv sg before ->
  signal <> 0 -> signal = event_addr sg eid ->
  mutex_query_lookup before eid observed ->
  (event_slot_type_value before.(EventState) eid = 3 ->
   before.(IntrState).(intNesting) <= 0 -> before.(IntrState).(lockNesting) <= 0 ->
   mutex_query_handle_protocol critical sg invocation eid) ->
  sem_pend_call_input critical sg invocation signal before eid observed.
Proof.
  intros critical sg invocation signal before eid observed Hvalid Hnonnull Haddress
    Hlookup Hprotocol.
  pose proof Hvalid as [_ [_ [_ [[Hpool _] _]]]].
  pose proof (proj1 (event_pool_used_not_free sg before.(EventState) eid observed
    Hpool Hlookup)) as Hid.
  right; split; [exact Hnonnull|]. split; [exact Haddress|].
  split; [exact Hid|]. split; [left; exact Hlookup|exact Hprotocol].
Qed.

(** Recycling is not rejected.  It returns EVENT_TYPE before Save, so no
    live-incarnation protocol, Task readiness or stack admission is used. *)
Lemma tmr_task_pend_input_public_free :
  forall critical sg invocation signal before eid observed,
  UCOS2_state_inv sg before ->
  signal <> 0 -> signal = event_addr sg eid ->
  In eid before.(EventState).(unUsedEventStates) ->
  sem_pend_call_input critical sg invocation signal before eid observed /\
  sem_pend_precritical_error signal (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) =
    Some OS_ERR_EVENT_TYPE.
Proof.
  intros critical sg invocation signal before eid observed Hvalid Hnonnull Haddress Hfree.
  pose proof Hvalid as [_ [_ [_ [[Hpool _] _]]]].
  pose proof (proj1 (event_pool_free_unallocated sg before.(EventState) eid Hpool Hfree))
    as Hnone.
  pose proof Hpool as [[Hnodup [Hrange Hpartition]] Hprivate].
  assert (Hid : valid_event_id sg eid) by exact (Hrange eid Hfree).
  assert (Htype : event_slot_type_value before.(EventState) eid = 0).
  { unfold event_slot_type_value; rewrite Hnone; reflexivity. }
  split.
  - right; split; [exact Hnonnull|]. split; [exact Haddress|]. split; [exact Hid|].
    split; [right; split; assumption|]. intros Hsem; rewrite Htype in Hsem; discriminate.
  - rewrite Htype; apply sem_pend_precritical_free; exact Hnonnull.
Qed.

Lemma tmr_task_pend_input_wrong_type :
  forall critical sg invocation signal before eid observed,
  signal <> 0 -> signal = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  event_slot_type_value before.(EventState) eid <> 3 ->
  sem_pend_call_input critical sg invocation signal before eid observed /\
  sem_pend_precritical_error signal (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) =
    Some OS_ERR_EVENT_TYPE.
Proof.
  intros critical sg invocation signal before eid observed Hnonnull Haddress Hid Hslot Htype.
  split.
  - right; split; [exact Hnonnull|]. split; [exact Haddress|]. split; [exact Hid|].
    split; [exact Hslot|]. intros Hsem; contradiction.
  - apply sem_pend_precritical_type; assumption.
Qed.

Lemma tmr_task_pend_input_isr :
  forall critical sg invocation signal before eid observed,
  signal <> 0 -> signal = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  event_slot_type_value before.(EventState) eid = 3 ->
  0 < before.(IntrState).(intNesting) ->
  sem_pend_call_input critical sg invocation signal before eid observed /\
  sem_pend_precritical_error signal (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) =
    Some OS_ERR_PEND_ISR.
Proof.
  intros critical sg invocation signal before eid observed Hnonnull Haddress Hid Hslot Htype Hint.
  split.
  - right; split; [exact Hnonnull|]. split; [exact Haddress|]. split; [exact Hid|].
    split; [exact Hslot|]. intros Hsem Hzero; lia.
  - rewrite Htype; apply sem_pend_precritical_isr; assumption.
Qed.

Lemma tmr_task_pend_input_locked :
  forall critical sg invocation signal before eid observed,
  signal <> 0 -> signal = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  event_slot_type_value before.(EventState) eid = 3 ->
  before.(IntrState).(intNesting) = 0 -> 0 < before.(IntrState).(lockNesting) ->
  sem_pend_call_input critical sg invocation signal before eid observed /\
  sem_pend_precritical_error signal (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) =
    Some OS_ERR_PEND_LOCKED.
Proof.
  intros critical sg invocation signal before eid observed Hnonnull Haddress Hid Hslot
    Htype Hint Hlock.
  split.
  - right; split; [exact Hnonnull|]. split; [exact Haddress|]. split; [exact Hid|].
    split; [exact Hslot|]. intros Hsem Hints Hlocks; lia.
  - rewrite Htype, Hint; apply sem_pend_precritical_locked; assumption.
Qed.

Lemma tmr_task_pend_admission_early_error :
  forall environment critical sg call signal before eid error,
  sem_pend_precritical_error signal (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = Some error ->
  sem_pend_observed_admission environment critical sg call signal before eid.
Proof. intros environment critical sg call signal before eid error Herror Hclear; congruence. Qed.

Lemma tmr_task_pend_admission_task_boundary :
  forall environment critical sg call signal before eid,
  sem_pend_task_call_stage sg call before ->
  kernel_running_idle_ready sg before -> kernel_call_stack_available call before ->
  sem_pend_observed_admission (Some environment) critical sg call signal before eid.
Proof.
  intros environment critical sg call signal before eid Hstage Hidle Havailable Hclear.
  left; split; [exact Hstage|]. split; assumption.
Qed.

(** A current-ready SOURCE receipt supplies the actual selected node and
    generation.  The separate fields are only this invocation's non-Idle
    and unregistered observations; neither equality of task maps nor an
    all-future-ready law is used. *)
Lemma tmr_task_pend_stage_from_ready_source :
  forall environment sg call state,
  kernel_call_task_source call state -> state.(SchedState).(isRunning) = true ->
  os_sched_task_ready_source environment sg call state ->
  (forall node,
    state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
    node.(curPrio) <> sg.(osLowestPrio) /\ sem_pend_task_unregistered node) ->
  sem_pend_task_call_stage sg call state.
Proof.
  intros environment sg call state Hsource Hrunning Hready_source Hfields.
  destruct (os_sched_task_ready_source_current_ready environment sg call state Hready_source)
    as [node [Hready Hgeneration]].
  destruct (Hfields node (proj1 Hready)) as [Hnonidle [Hevent [Hmulti Hflag]]].
  split; [exact Hsource|]. split; [exact Hrunning|]. exists node.
  split; [exact Hready|]. split; [exact Hgeneration|].
  repeat split; assumption.
Qed.

(** A genuine producer composition for a REGISTERED normal-return segment.
    It consumes the very same returned history and ready receipt.  The
    existing projected-client family proves the changed task's fields;
    Suspend/Resume/ChangePrio are allowed and task maps need not be equal.
    This family does not cover arbitrary callbacks or arbitrary Create/Del
    traces.  No theorem asserts that those histories belong to this family. *)
Lemma tmr_task_pend_stage_registered_return :
  forall environment critical sg original returned before after,
  (forall action, critical.(critical_region_clients) action ->
    sem_pend_projected_source_client action) ->
  UCOS2_state_inv sg before -> sem_pend_task_call_stage sg original before ->
  sem_pend_modular_call_history environment critical sg original before returned after ->
  os_sched_task_ready_source environment sg returned after ->
  sem_pend_task_call_stage sg returned after.
Proof.
  intros environment critical sg original returned before after Hclients Hvalid
    [Hsource [Hrunning [old [Hready [Hgeneration [Hnonidle Hnone]]]]]]
    [Htrace [Hsame Havailable]] Hreturned_ready.
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)
    as [Hinterval Hcontrol].
  pose proof (proj1 (critical_region_interval_transports_resources critical sg
    original.(os_sched_call_invocation) before after Hinterval Hvalid)) as Hvalid_after.
  destruct (sem_pend_resumption_trace_preserves_call_fields
    critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
    before false after original.(os_sched_call_stack).(stackLeaseSlot) old
    Hclients Hinterval Hvalid Hvalid_after Hrunning (proj1 Hready) Hnonidle Hnone)
    as [Hrunning_after [current [Hcurrent [Hnonidle_after Hnone_after]]]].
  assert (Hsource_after : kernel_call_task_source returned after).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff returned original after Hsame)).
    exact (task_tcb_init_stack_registered_source_preserved
      environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical sg original returned before after Hvalid Hsame Htrace Hsource). }
  eapply tmr_task_pend_stage_from_ready_source;
    [exact Hsource_after|exact Hrunning_after|exact Hreturned_ready|].
  intros node Hnode.
  rewrite (proj2 (proj2 Hsame)) in Hnode.
  assert (node = current) by congruence; subst node; split; assumption.
Qed.

Lemma tmr_task_pend_registered_return_available :
  forall environment critical sg original returned before after,
  sem_pend_modular_call_history environment critical sg original before returned after ->
  kernel_call_stack_available original before -> kernel_call_stack_available returned after.
Proof.
  intros environment critical sg original returned before after [_ [_ Havailable]] Hbefore.
  apply Havailable; exact Hbefore.
Qed.

(** Actual Pend cleanup establishes EventPtr=None; it retains the other
    disabled registration fields from the cleanup entry.  This is only
    the literal pre-Restore endpoint, not a claim about arbitrary later
    callbacks or a source receipt erased by the legacy public post. *)
Lemma tmr_task_pend_cleanup_unregistered : forall sg state tid node,
  sem_pend_cleanup_entry sg state tid node ->
  let cleaned := task_event_pend_cleanup sg.(osKernelConfig).(cfgEventMultiEnabled) false node in
  (event_pend_cleanup_state sg false state tid node).(TskState).(inUsedTaskStates) tid = Some cleaned /\
  sem_pend_task_unregistered cleaned.
Proof.
  intros sg state tid node [_ [_ [Hnode [Hevent [Hmulti [Hflag Hready]]]]]] cleaned.
  split.
  - cbn [event_pend_cleanup_state replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
    rewrite Z.eqb_refl; reflexivity.
  - unfold cleaned, sem_pend_task_unregistered.
    destruct sg.(osKernelConfig).(cfgEventMultiEnabled); repeat split; assumption || reflexivity.
Qed.

(** Timer writes preserve precisely these endpoint observations.  The
    observed-admission predicate also has a nonblocking history arm, so
    it is NOT blindly rewritten across arbitrary Timer replacement. *)
Lemma tmr_task_pend_stage_replace_timers_iff : forall sg call timers state,
  sem_pend_task_call_stage sg call (replace_TimerS timers state) <->
  sem_pend_task_call_stage sg call state.
Proof. reflexivity. Qed.

Lemma tmr_task_pend_boundary_replace_timers : forall sg call timers state,
  sem_pend_task_call_stage sg call state ->
  kernel_running_idle_ready sg state -> kernel_call_stack_available call state ->
  sem_pend_task_call_stage sg call (replace_TimerS timers state) /\
  kernel_running_idle_ready sg (replace_TimerS timers state) /\
  kernel_call_stack_available call (replace_TimerS timers state).
Proof.
  intros sg call timers state Hstage Hidle Havailable.
  split; [exact Hstage|]. split; [exact Hidle|exact Havailable].
Qed.

(** These two consumers rebuild the EXACT existing Task wait instance.
    X and the actual high-level program are unchanged: after the real
    SemPend post, tmr_task_pend_source_continue consumes its source result
    (including every error) and advances the same arbitrary product X.
    The consumers here prove admission only; they create no heap owner. *)
Lemma tmr_task_wait_instance_task_boundary :
  forall Application environment critical sg call (world : tmr_task_scan_world Application) eid observed,
  sem_pend_call_input critical sg call.(os_sched_call_invocation)
    (tmr_task_timers world).(timerSignalSem) (fst world) eid observed ->
  sem_pend_task_call_stage sg call (fst world) ->
  kernel_running_idle_ready sg (fst world) -> kernel_call_stack_available call (fst world) ->
  event_table_layout_prop sg ->
  tmr_task_wait_instance environment critical sg call world eid observed.
Proof.
  intros Application environment critical sg call world eid observed Hinput Hstage Hidle Havailable Hlayout.
  split; [exact Hinput|]. split; [apply tmr_task_pend_owned_runtime_nonblocking|].
  split.
  - apply tmr_task_pend_admission_task_boundary; assumption.
  - apply tmr_task_pend_acquired_layout_from_table; exact Hlayout.
Qed.

Lemma tmr_task_wait_instance_early_error :
  forall Application environment critical sg call (world : tmr_task_scan_world Application) eid observed error,
  sem_pend_call_input critical sg call.(os_sched_call_invocation)
    (tmr_task_timers world).(timerSignalSem) (fst world) eid observed ->
  sem_pend_precritical_error (tmr_task_timers world).(timerSignalSem)
    (event_slot_type_value (fst world).(EventState) eid)
    (fst world).(IntrState).(intNesting) (fst world).(IntrState).(lockNesting) = Some error ->
  event_table_layout_prop sg ->
  tmr_task_wait_instance environment critical sg call world eid observed.
Proof.
  intros Application environment critical sg call world eid observed error Hinput Herror Hlayout.
  split; [exact Hinput|]. split; [apply tmr_task_pend_owned_runtime_nonblocking|].
  split.
  - eapply tmr_task_pend_admission_early_error; exact Herror.
  - apply tmr_task_pend_acquired_layout_from_table; exact Hlayout.
Qed.
