Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare safeexec_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_start Ucos2Verify.lib.kernel_runtime_inv.
Require Import Ucos2Verify.lib.timer Ucos2Verify.lib.event Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_boot_stack_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_start_stack_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_idle_ready_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_api_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_checkpoint_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_call_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_call_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_annotation_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_next_pend_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_handle_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_protocol_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fresh_fields_spec.
Import TaskStateDef ListNotations.
Local Open Scope Z_scope.

(** A receipt for ONE current first Pend call, not every future iteration.
    The first conjunct spells out the actual signal-address/public-slot
    domain. NULL carries no dummy-id validity or ECB ownership requirement.
    FREE/wrong-type/ISR/locked paths stop at the real precritical error.

    On a successful precritical test, the existing proved nonblocking
    acquisition protocol is an alternative to the Task/Idle/available
    branch. Thus a positive count observed BEFORE Save is not mistaken
    for guaranteed nonblocking acquisition, and Task conditions are not
    imposed on early errors or on a proved nonblocking call. The spatial
    fields/capsule owner remains a separate actual resource obligation. *)
Definition tmr_task_fields_entry environment critical sg call
  (state : UCOS2_Verify_State) eid observed : Prop :=
  let signal := state.(TimerState).(timerSignalSem) in
  (signal = 0 \/
    (signal <> 0 /\ signal = event_addr sg eid /\ valid_event_id sg eid /\
     sem_query_public_slot state eid observed /\
     (event_slot_type_value state.(EventState) eid = 3 ->
      state.(IntrState).(intNesting) <= 0 -> state.(IntrState).(lockNesting) <= 0 ->
      mutex_query_handle_protocol critical sg call.(os_sched_call_invocation) eid))) /\
  match sem_pend_precritical_error signal (event_slot_type_value state.(EventState) eid)
      state.(IntrState).(intNesting) state.(IntrState).(lockNesting) with
  | Some _ => True
  | None => sem_pend_observed_nonblocking (Some environment) critical sg call state eid \/
      (sem_pend_task_call_stage sg call state /\ kernel_running_idle_ready sg state /\
       kernel_call_stack_available call state)
  end.

Lemma tmr_task_fields_entry_call_input : forall environment critical sg call state eid observed,
  tmr_task_fields_entry environment critical sg call state eid observed ->
  sem_pend_call_input critical sg call.(os_sched_call_invocation)
    state.(TimerState).(timerSignalSem) state eid observed.
Proof. intros environment critical sg call state eid observed [Hsignal Hbranch]; exact Hsignal. Qed.

Lemma tmr_task_fields_entry_observed_admission : forall environment critical sg call state eid observed,
  tmr_task_fields_entry environment critical sg call state eid observed ->
  sem_pend_observed_admission (Some environment) critical sg call
    state.(TimerState).(timerSignalSem) state eid.
Proof.
  intros environment critical sg call state eid observed [Hsignal Hbranch] Hclear.
  rewrite Hclear in Hbranch; destruct Hbranch as [Hnonblocking|Htask].
  - right; exact Hnonblocking.
  - left; exact Htask.
Qed.

(** Reuse the fixed profile and actual acquired-layout producer. Neither
    runtime_nonblocking nor a forall-acquired-layout condition is added to
    the entry receipt. The actual acquire observation supplies the live
    slot/id needed to specialize the fixed event table layout. *)
Lemma tmr_task_fields_entry_call_domain : forall environment critical sg call state eid observed,
  tmr_task_profile sg -> event_table_layout_prop sg ->
  tmr_task_fields_entry environment critical sg call state eid observed ->
  sem_pend_fields_call_domain environment critical sg call
    state.(TimerState).(timerSignalSem) state eid observed.
Proof.
  intros environment critical sg call state eid observed Hprofile Hlayout Hentry.
  unfold sem_pend_fields_call_domain.
  split; [unfold tmr_task_profile in Hprofile; tauto|].
  split; [unfold tmr_task_profile in Hprofile; tauto|].
  split; [eapply tmr_task_fields_entry_call_input; exact Hentry|].
  split; [apply tmr_task_pend_owned_runtime_nonblocking|].
  split; [eapply tmr_task_fields_entry_observed_admission; exact Hentry|].
  intros Hnonnull Hclear; apply tmr_task_pend_acquired_layout_from_table; exact Hlayout.
Qed.

Lemma tmr_task_fields_entry_early_error : forall environment critical sg call state eid observed error,
  sem_pend_call_input critical sg call.(os_sched_call_invocation)
    state.(TimerState).(timerSignalSem) state eid observed ->
  sem_pend_precritical_error state.(TimerState).(timerSignalSem)
    (event_slot_type_value state.(EventState) eid)
    state.(IntrState).(intNesting) state.(IntrState).(lockNesting) = Some error ->
  tmr_task_fields_entry environment critical sg call state eid observed.
Proof.
  intros environment critical sg call state eid observed error Hinput Herror.
  split; [exact Hinput|rewrite Herror; exact I].
Qed.

Lemma tmr_task_fields_entry_null : forall environment critical sg call state eid observed,
  state.(TimerState).(timerSignalSem) = 0 ->
  tmr_task_fields_entry environment critical sg call state eid observed.
Proof.
  intros environment critical sg call state eid observed Hnull.
  eapply tmr_task_fields_entry_early_error.
  - rewrite Hnull; apply tmr_task_pend_input_null.
  - rewrite Hnull; apply sem_pend_precritical_null.
Qed.

Lemma tmr_task_fields_entry_free : forall environment critical sg call state eid observed,
  UCOS2_state_inv sg state -> state.(TimerState).(timerSignalSem) <> 0 ->
  state.(TimerState).(timerSignalSem) = event_addr sg eid ->
  In eid state.(EventState).(unUsedEventStates) ->
  tmr_task_fields_entry environment critical sg call state eid observed.
Proof.
  intros environment critical sg call state eid observed Hvalid Hnonnull Haddress Hfree.
  destruct (tmr_task_pend_input_public_free critical sg call.(os_sched_call_invocation)
    state.(TimerState).(timerSignalSem) state eid observed Hvalid Hnonnull Haddress Hfree)
    as [Hinput Herror].
  eapply tmr_task_fields_entry_early_error; eassumption.
Qed.

Lemma tmr_task_fields_entry_wrong_type : forall environment critical sg call state eid observed,
  state.(TimerState).(timerSignalSem) <> 0 ->
  state.(TimerState).(timerSignalSem) = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot state eid observed -> event_slot_type_value state.(EventState) eid <> 3 ->
  tmr_task_fields_entry environment critical sg call state eid observed.
Proof.
  intros environment critical sg call state eid observed Hnonnull Haddress Hid Hpublic Htype.
  destruct (tmr_task_pend_input_wrong_type critical sg call.(os_sched_call_invocation)
    state.(TimerState).(timerSignalSem) state eid observed Hnonnull Haddress Hid Hpublic Htype)
    as [Hinput Herror].
  eapply tmr_task_fields_entry_early_error; eassumption.
Qed.

Lemma tmr_task_fields_entry_isr : forall environment critical sg call state eid observed,
  state.(TimerState).(timerSignalSem) <> 0 ->
  state.(TimerState).(timerSignalSem) = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot state eid observed -> event_slot_type_value state.(EventState) eid = 3 ->
  0 < state.(IntrState).(intNesting) ->
  tmr_task_fields_entry environment critical sg call state eid observed.
Proof.
  intros environment critical sg call state eid observed Hnonnull Haddress Hid Hpublic Htype Hints.
  destruct (tmr_task_pend_input_isr critical sg call.(os_sched_call_invocation)
    state.(TimerState).(timerSignalSem) state eid observed Hnonnull Haddress Hid Hpublic Htype Hints)
    as [Hinput Herror].
  eapply tmr_task_fields_entry_early_error; eassumption.
Qed.

Lemma tmr_task_fields_entry_locked : forall environment critical sg call state eid observed,
  state.(TimerState).(timerSignalSem) <> 0 ->
  state.(TimerState).(timerSignalSem) = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot state eid observed -> event_slot_type_value state.(EventState) eid = 3 ->
  state.(IntrState).(intNesting) = 0 -> 0 < state.(IntrState).(lockNesting) ->
  tmr_task_fields_entry environment critical sg call state eid observed.
Proof.
  intros environment critical sg call state eid observed Hnonnull Haddress Hid Hpublic Htype Hints Hlocks.
  destruct (tmr_task_pend_input_locked critical sg call.(os_sched_call_invocation)
    state.(TimerState).(timerSignalSem) state eid observed Hnonnull Haddress Hid Hpublic Htype Hints Hlocks)
    as [Hinput Herror].
  eapply tmr_task_fields_entry_early_error; eassumption.
Qed.

Lemma tmr_task_fields_entry_nonblocking : forall environment critical sg call state eid observed,
  sem_pend_call_input critical sg call.(os_sched_call_invocation)
    state.(TimerState).(timerSignalSem) state eid observed ->
  sem_pend_observed_nonblocking (Some environment) critical sg call state eid ->
  tmr_task_fields_entry environment critical sg call state eid observed.
Proof.
  intros environment critical sg call state eid observed Hinput Hnonblocking.
  split; [exact Hinput|].
  destruct (sem_pend_precritical_error state.(TimerState).(timerSignalSem)
    (event_slot_type_value state.(EventState) eid)
    state.(IntrState).(intNesting) state.(IntrState).(lockNesting)); [exact I|left; exact Hnonblocking].
Qed.

Lemma tmr_task_fields_entry_task_boundary : forall environment critical sg call state eid observed,
  sem_pend_call_input critical sg call.(os_sched_call_invocation)
    state.(TimerState).(timerSignalSem) state eid observed ->
  sem_pend_task_call_stage sg call state -> kernel_running_idle_ready sg state ->
  kernel_call_stack_available call state ->
  tmr_task_fields_entry environment critical sg call state eid observed.
Proof.
  intros environment critical sg call state eid observed Hinput Hstage Hidle Havailable.
  split; [exact Hinput|].
  destruct (sem_pend_precritical_error state.(TimerState).(timerSignalSem)
    (event_slot_type_value state.(EventState) eid)
    state.(IntrState).(intNesting) state.(IntrState).(lockNesting)); [exact I|right; auto].
Qed.

(** The scheduled Unlock post already carries Fresh at its actual returned
    descriptor. This extracts the registration fields from that receipt;
    it does not infer them from a current-task lookup or a closed owner. *)
Lemma tmr_task_fields_fresh_return_unregistered : forall reference returned state,
  flag_active_fresh_registration reference returned state ->
  forall node, state.(TskState).(inUsedTaskStates)
    returned.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
    sem_pend_task_unregistered node.
Proof.
  intros reference returned state [task [Hfields Hflag]] node Hnode.
  destruct Hfields as [Hsame [Horigin [Htask [Hgeneration [Hactive Hclear]]]]].
  rewrite (proj2 (proj2 Hsame)) in Hnode.
  assert (node = task) by congruence; subst node.
  destruct Hclear as [Hevent [Hmulti Hpointer]].
  repeat split; assumption.
Qed.

(** One current entry assembled from the real callee's normal-return,
    source, CURRENT_READY and Fresh receipts. Idle/non-Idle and the public
    signal slot are observations at THIS endpoint. Their source producers
    remain separate, so this lemma cannot turn an arbitrary callback into
    an all-future-entry contract. Early errors keep their existing domain. *)
Lemma tmr_task_fields_entry_after_service_return :
  forall environment critical sg original returned reference before current eid observed,
  kernel_call_normal_return original before returned current ->
  (kernel_call_task_source original before -> kernel_call_task_source returned current) ->
  kernel_call_task_source original before -> kernel_call_stack_available original before ->
  current.(SchedState).(isRunning) = true -> os_sched_task_current_ready returned current ->
  flag_active_fresh_registration reference returned current ->
  (forall node, current.(TskState).(inUsedTaskStates)
    returned.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
    node.(curPrio) <> sg.(osLowestPrio)) ->
  kernel_running_idle_ready sg current ->
  tmr_task_service_frame before.(TimerState) current.(TimerState) ->
  before.(TimerState).(timerSignalSem) <> 0 ->
  before.(TimerState).(timerSignalSem) = event_addr sg eid -> valid_event_id sg eid ->
  mutex_query_handle_protocol critical sg original.(os_sched_call_invocation) eid ->
  sem_query_public_slot current eid observed ->
  tmr_task_fields_entry environment critical sg returned current eid observed.
Proof.
  intros environment critical sg original returned reference before current eid observed
    Hnormal Hsource Hbefore Havailable Hrunning Hready Hfresh Hnonidle Hidle
    Hframe Hnonnull Haddress Hid Hprotocol Hpublic.
  eapply tmr_task_fields_entry_task_boundary.
  - exact (tmr_task_signal_input_after_service critical sg original returned
      before.(TimerState) current eid observed (proj1 Hnormal) Hframe
      Hnonnull Haddress Hid Hprotocol Hpublic).
  - eapply tmr_task_pend_stage_from_current_ready;
      [apply Hsource; exact Hbefore|exact Hrunning|exact Hready|].
    intros node Hnode; split; [apply Hnonidle; exact Hnode|].
    eapply tmr_task_fields_fresh_return_unregistered; eassumption.
  - exact Hidle.
  - apply (proj2 Hnormal); exact Havailable.
Qed.

(** Actual Create and signal-store endpoint, including failed Create.
    fallback is merely an unused logical witness on NULL; it grants no
    ECB bytes. Registration is targeted at the service invocation, which
    need not be the initializer's create_invocation. *)
Lemma tmr_task_fields_created_signal_input : forall critical sg create_invocation service_invocation
  count before signal current timers (fallback : OSEventAbstractState),
  sem_create_api_program critical sg create_invocation count before signal current ->
  UCOS2_state_inv sg current -> timer_record_signal_result current.(TimerState) signal = Some timers ->
  (forall eid, signal = event_addr sg eid ->
    mutex_query_handle_protocol critical sg service_invocation eid) ->
  exists eid observed, sem_pend_call_input critical sg service_invocation timers.(timerSignalSem)
    (replace_TimerS timers current) eid observed.
Proof.
  intros critical sg create_invocation service_invocation count before signal current timers fallback
    Hcreate Hvalid Hstore Hprotocol.
  destruct (Z.eq_dec signal 0) as [->|Hnonnull].
  - exists 0, fallback; eapply tmr_task_signal_null_store_call_input; exact Hstore.
  - eapply tmr_task_signal_create_store_call_input; eassumption.
Qed.

(** Create supplies the actual address and valid pool id. The two current
    endpoint inputs below are deliberately explicit: the signal value must
    survive the real initialization path, and its slot must be public at
    THIS startup cut. Recycle/reuse/wrong type remain allowed. The guarded
    owner protocol is consumed only if the current precritical arm can Save.
    No equality of Event/Task maps, full final world, or future entry law is
    assumed. A source proof of the intervening initialization dispatch must
    produce Hpublic and Hsignal; Create alone cannot establish them later. *)
Lemma tmr_task_fields_created_signal_current_input : forall critical sg create_invocation service_invocation
  count before signal created timers startup (fallback : OSEventAbstractState),
  sem_create_api_program critical sg create_invocation count before signal created ->
  UCOS2_state_inv sg created -> timer_record_signal_result created.(TimerState) signal = Some timers ->
  startup.(TimerState).(timerSignalSem) = timers.(timerSignalSem) ->
  (forall eid, signal = event_addr sg eid -> exists observed, sem_query_public_slot startup eid observed) ->
  (forall eid, signal = event_addr sg eid -> event_slot_type_value startup.(EventState) eid = 3 ->
    startup.(IntrState).(intNesting) <= 0 -> startup.(IntrState).(lockNesting) <= 0 ->
    mutex_query_handle_protocol critical sg service_invocation eid) ->
  exists eid observed, sem_pend_call_input critical sg service_invocation
    startup.(TimerState).(timerSignalSem) startup eid observed.
Proof.
  intros critical sg create_invocation service_invocation count before signal created timers startup fallback
    Hcreate Hvalid Hstore Hsignal Hpublic Hprotocol.
  rewrite (tmr_task_signal_recorded_value _ _ _ Hstore) in Hsignal.
  destruct (Z.eq_dec signal 0) as [->|Hnonnull].
  - exists 0, fallback; rewrite Hsignal; apply tmr_task_pend_input_null.
  - destruct (tmr_task_signal_create_published_slot critical sg create_invocation count
      before signal created Hcreate Hnonnull) as [eid [old [Haddress [Hlookup Htype]]]].
    pose proof Hvalid as [_ [_ [_ [[Hpool _] _]]]].
    pose proof (proj1 (event_pool_used_not_free sg created.(EventState) eid old Hpool Hlookup)) as Hid.
    destruct (Hpublic eid Haddress) as [observed Hslot].
    exists eid, observed; rewrite Hsignal.
    right; split; [exact Hnonnull|]. split; [exact Haddress|]. split; [exact Hid|].
    split; [exact Hslot|]. intros Hsem Hint Hlock; exact (Hprotocol eid Haddress Hsem Hint Hlock).
Qed.

(** The initial invocation ledger is established by the existing actual
    task_begin_invocation transition. CPU/stack ABI ownership is supplied
    separately by tmr_task_entry_call_resources; no source fact is obtained
    from an opaque running token. *)
Lemma tmr_task_fields_initial_call_stage : forall sg state saved node fragments,
  sched_current_ready_at state.(TskState) state.(SchedState)
    saved.(armv7a_continuation_stack).(stackLeaseSlot) node ->
  node.(taskGeneration) = saved.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  state.(SchedState).(isRunning) = true -> node.(curPrio) <> sg.(osLowestPrio) ->
  node.(eventPtr) = None -> node.(eventMultiWaitEvents) = [] -> node.(tcbFlagNode) = 0 ->
  sem_pend_task_call_stage sg
    (armv7a_initial_call saved state.(TskState).(taskLifecycle).(taskNextInvocation) fragments)
    (armv7a_initial_call_registered saved state).
Proof.
  intros sg state saved node fragments Hready Hgen Hrunning Hnonidle Hevent Hmulti Hflag.
  assert (Hcurrent : task_current_at state saved.(armv7a_continuation_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_stack).(stackLeaseGeneration)).
  { split; [exact (proj1 (proj2 Hready))|].
    exists node; split; [exact (proj1 Hready)|exact Hgen]. }
  destruct (task_current_at_begin_invocation state
    saved.(armv7a_continuation_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_stack).(stackLeaseGeneration) Hcurrent) as [Hregistered Hactive].
  split.
  - unfold kernel_call_task_source, armv7a_initial_call.
    split; [reflexivity|]. split; [exact Hactive|exact (proj1 Hregistered)].
  - split; [exact Hrunning|]. exists node.
    split; [exact Hready|]. split; [exact Hgen|]. repeat split; assumption.
Qed.

(** The OSStart selector supplies current_ready; taking its actual stack
    removes that key from parkedTaskStacks; initial-call registration adds
    the invocation token. The maintained Idle witness is a real live TCB
    property from Idle creation, not merely task_idle_tail. *)
Lemma tmr_task_fields_start_call_boundary : forall sg state saved node fragments rest,
  UCOS2_state_inv sg state ->
  state.(SchedState).(readyList) = saved.(armv7a_continuation_stack).(stackLeaseSlot) :: rest ->
  state.(TskState).(inUsedTaskStates) saved.(armv7a_continuation_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = saved.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  node.(curPrio) <> sg.(osLowestPrio) -> node.(eventPtr) = None ->
  node.(eventMultiWaitEvents) = [] -> node.(tcbFlagNode) = 0 ->
  task_idle_ready sg state.(TskState) ->
  let selected := kernel_start_take_stack_state
    (kernel_running_store (kernel_start_ready_state state)) saved.(armv7a_continuation_stack) in
  let entered := armv7a_initial_call_registered saved selected in
  let call := armv7a_initial_call saved selected.(TskState).(taskLifecycle).(taskNextInvocation) fragments in
  sem_pend_task_call_stage sg call entered /\ kernel_running_idle_ready sg entered /\
    kernel_call_stack_available call entered.
Proof.
  intros sg state saved node fragments rest Hvalid Hhead Hnode Hgen Hnonidle Hevent Hmulti Hflag Hidle
    selected entered call.
  pose proof (tmr_task_selected_current_ready sg state
    saved.(armv7a_continuation_stack).(stackLeaseSlot) rest node Hvalid Hhead Hnode) as Hready.
  split.
  - apply tmr_task_fields_initial_call_stage with (node := node).
    + exact Hready.
    + exact Hgen.
    + reflexivity.
    + exact Hnonidle.
    + exact Hevent.
    + exact Hmulti.
    + exact Hflag.
  - split.
    + intro Hrunning; exact Hidle.
    + unfold kernel_call_stack_available, call, armv7a_initial_call.
      change (task_stack_take state.(TskState).(parkedTaskStacks)
        saved.(armv7a_continuation_stack) (task_stack_key saved.(armv7a_continuation_stack)) = None).
      apply task_stack_take_lookup.
Qed.

(** Specialize the initial node to the actual Timer CreateExt commit.
    Hnode and Hgen are the exact remaining publication/selected-descriptor
    correspondence, to be supplied at the real post-hook OSStart cut. *)
Lemma tmr_task_fields_commit_start_boundary : forall sg state saved fragments rest pc stack_pointer
  initial_name acquired image previous next,
  let node := task_set_links (task_tcb_init_commit_node
    (task_create_tcb_args (kernel_boot_timer_args sg pc) stack_pointer initial_name)
    acquired saved.(armv7a_continuation_stack).(stackLeaseSlot) image) previous next in
  UCOS2_state_inv sg state ->
  state.(SchedState).(readyList) = saved.(armv7a_continuation_stack).(stackLeaseSlot) :: rest ->
  state.(TskState).(inUsedTaskStates) saved.(armv7a_continuation_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = saved.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  task_idle_ready sg state.(TskState) ->
  let selected := kernel_start_take_stack_state
    (kernel_running_store (kernel_start_ready_state state)) saved.(armv7a_continuation_stack) in
  let entered := armv7a_initial_call_registered saved selected in
  let call := armv7a_initial_call saved selected.(TskState).(taskLifecycle).(taskNextInvocation) fragments in
  sem_pend_task_call_stage sg call entered /\ kernel_running_idle_ready sg entered /\
    kernel_call_stack_available call entered /\ flag_active_fresh_registration call call entered.
Proof.
  intros sg state saved fragments rest pc stack_pointer initial_name acquired image previous next node
    Hvalid Hhead Hnode Hgen Hidle selected entered call.
  destruct (tmr_task_initialized_wait_fields sg pc stack_pointer initial_name acquired
    saved.(armv7a_continuation_stack).(stackLeaseSlot) image previous next)
    as [Hpriority [Hnonidle [Hevent [Hmulti [Hflag Hready]]]]].
  destruct (tmr_task_fields_start_call_boundary sg state saved node fragments rest
    Hvalid Hhead Hnode Hgen Hnonidle Hevent Hmulti Hflag Hidle) as [Hstage [Hidle' Havailable]].
  split; [exact Hstage|]. split; [exact Hidle'|]. split; [exact Havailable|].
  apply tmr_task_stage_multi_zero_fresh with (sg := sg); [exact Hstage|].
  intros current Hcurrent.
  change (state.(TskState).(inUsedTaskStates)
    saved.(armv7a_continuation_stack).(stackLeaseSlot) = Some current) in Hcurrent.
  rewrite Hnode in Hcurrent.
  assert (Hsame : current = node) by congruence; subst current; reflexivity.
Qed.

(** At the actual publication cut the node lookup is produced by the
    existing task_commit theorem. It is not an additional premise there.
    A later startup cut still needs the real intervening source transport. *)
Lemma tmr_task_fields_timer_publication_node : forall sg invocation acquired current
  slot pc stack_pointer initial_name image,
  let args := task_create_tcb_args (kernel_boot_timer_args sg pc) stack_pointer initial_name in
  (task_tcb_init_published_state sg args invocation acquired current slot image).(TskState).(inUsedTaskStates)
    slot = Some (task_set_links (task_tcb_init_commit_node args acquired slot image)
      current.(TskState).(tcbListHead) None).
Proof.
  intros sg invocation acquired current slot pc stack_pointer initial_name image args.
  exact (proj1 (task_commit_publication_fields_eq current.(TskState) args.(initPrio)
    invocation (task_tcb_init_commit_node args acquired slot image))).
Qed.

(** A complete pure publication-to-initial-call composition for the case
    where OSStart selects this actually published Timer task. The source
    creation proof supplies validity and commit binding; its registered
    startup path supplies the real ready head and selected generation.
    This is not a claim that the Timer task must be the first ready task. *)
Lemma tmr_task_fields_timer_publication_start_boundary : forall sg invocation origin acquired current
  saved fragments rest pc stack_pointer initial_name image,
  let args := task_create_tcb_args (kernel_boot_timer_args sg pc) stack_pointer initial_name in
  let published := task_tcb_init_published_state sg args invocation acquired current
    saved.(armv7a_continuation_stack).(stackLeaseSlot) image in
  UCOS2_state_inv sg current ->
  task_tcb_init_commit_binding args invocation origin acquired current
    saved.(armv7a_continuation_stack).(stackLeaseSlot) ->
  task_idle_ready sg current.(TskState) -> UCOS2_state_inv sg published ->
  published.(SchedState).(readyList) = saved.(armv7a_continuation_stack).(stackLeaseSlot) :: rest ->
  acquired.(TskState).(taskLifecycle).(taskNextGeneration) =
    saved.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  let selected := kernel_start_take_stack_state
    (kernel_running_store (kernel_start_ready_state published)) saved.(armv7a_continuation_stack) in
  let entered := armv7a_initial_call_registered saved selected in
  let call := armv7a_initial_call saved selected.(TskState).(taskLifecycle).(taskNextInvocation) fragments in
  sem_pend_task_call_stage sg call entered /\ kernel_running_idle_ready sg entered /\
    kernel_call_stack_available call entered /\ flag_active_fresh_registration call call entered.
Proof.
  intros sg invocation origin acquired current saved fragments rest pc stack_pointer initial_name image
    args published Hcurrent Hbinding Hidle Hpublished Hhead Hgeneration selected entered call.
  pose proof (tmr_task_fields_timer_publication_node sg invocation acquired current
    saved.(armv7a_continuation_stack).(stackLeaseSlot) pc stack_pointer initial_name image) as Hnode.
  pose proof (task_tcb_init_publication_preserves_idle_ready sg args invocation origin acquired current
    saved.(armv7a_continuation_stack).(stackLeaseSlot) image Hcurrent Hbinding Hidle) as Hpublished_idle.
  apply (tmr_task_fields_commit_start_boundary sg published saved fragments rest pc stack_pointer
    initial_name acquired image current.(TskState).(tcbListHead) None).
  - exact Hpublished.
  - exact Hhead.
  - exact Hnode.
  - exact Hgeneration.
  - exact Hpublished_idle.
Qed.

Lemma tmr_task_fields_start_signal_input : forall critical sg state saved fragments eid observed,
  let selected := kernel_start_take_stack_state
    (kernel_running_store (kernel_start_ready_state state)) saved.(armv7a_continuation_stack) in
  let entered := armv7a_initial_call_registered saved selected in
  let call := armv7a_initial_call saved selected.(TskState).(taskLifecycle).(taskNextInvocation) fragments in
  sem_pend_call_input critical sg call.(os_sched_call_invocation)
    state.(TimerState).(timerSignalSem) state eid observed ->
  sem_pend_call_input critical sg call.(os_sched_call_invocation)
    entered.(TimerState).(timerSignalSem) entered eid observed.
Proof.
  intros critical sg state saved fragments eid observed selected entered call Hinput.
  exact Hinput.
Qed.

Lemma tmr_task_fields_started_entry : forall environment critical sg state saved node fragments rest eid observed,
  UCOS2_state_inv sg state ->
  state.(SchedState).(readyList) = saved.(armv7a_continuation_stack).(stackLeaseSlot) :: rest ->
  state.(TskState).(inUsedTaskStates) saved.(armv7a_continuation_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = saved.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  node.(curPrio) <> sg.(osLowestPrio) -> node.(eventPtr) = None ->
  node.(eventMultiWaitEvents) = [] -> node.(tcbFlagNode) = 0 -> task_idle_ready sg state.(TskState) ->
  let selected := kernel_start_take_stack_state
    (kernel_running_store (kernel_start_ready_state state)) saved.(armv7a_continuation_stack) in
  let entered := armv7a_initial_call_registered saved selected in
  let call := armv7a_initial_call saved selected.(TskState).(taskLifecycle).(taskNextInvocation) fragments in
  sem_pend_call_input critical sg call.(os_sched_call_invocation)
    state.(TimerState).(timerSignalSem) state eid observed ->
  tmr_task_fields_entry environment critical sg call entered eid observed.
Proof.
  intros environment critical sg state saved node fragments rest eid observed Hvalid Hhead Hnode Hgen
    Hnonidle Hevent Hmulti Hflag Hidle selected entered call Hsignal.
  destruct (tmr_task_fields_start_call_boundary sg state saved node fragments rest
    Hvalid Hhead Hnode Hgen Hnonidle Hevent Hmulti Hflag Hidle) as [Hstage [Hidle' Havailable]].
  apply tmr_task_fields_entry_task_boundary; assumption.
Qed.

(** This ordinary partial-correctness fact is diagnostic only. It explains
    why arbitrary-X prefix safety cannot create signal addresses or source
    admission: True constrains no completed outcome. The actual C proof
    keeps its same arbitrary X and must still prove every source/call rule. *)

