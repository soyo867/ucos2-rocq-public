Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.event Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_client_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_sem_source_projection_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_save_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_wait_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_wake_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The finite EventReady C producer is reused under this module
    identity. Definitions and theorem statements match their main
    sources; only the explicit spatial proof bodies are adapted.
    The old aggregate SemPost/phase return chain is not imported. *)
Module SemPendEventReadySource.

Definition sem_post_waiter_prefix_execution (pointer : Z) (before after : model) : Prop :=
  exists delayed messaged status_written bits,
    kernel_heap_execution (pointer_store_writes (tcb_field_address pointer TCBDly) 0) before delayed /\
    kernel_heap_execution (pointer_store_writes (tcb_field_address pointer TCBMsg) 0) delayed messaged /\
    uchar_load (tcb_field_address pointer TCBStat) bits messaged /\
    kernel_heap_execution [(tcb_field_address pointer TCBStat, event_task_remove_cleared bits 1)]
      messaged status_written /\
    kernel_heap_execution [(tcb_field_address pointer TCBStatPend, 0)] status_written after.

Lemma sem_post_waiter_prefix_resources : forall sg task pointer before after (frame : Assertion),
  (tcb64_storage_rep pointer (task_tcb64_image sg task) ** frame) before ->
  sem_post_waiter_prefix_execution pointer before after ->
  (tcb64_storage_rep pointer (event_task_rdy_before_remove_image sg task 0 1 0) ** frame) after.
Proof.
  intros sg task pointer before after frame Hpre
    (delayed & messaged & status_written & bits & Hdly & Hmsg & Hbits & Hstat & Hpend).
  pose proof (mutex_del_wake_tcb_store pointer (task_tcb64_image sg task) TCBDly 0 before delayed frame
    ltac:(unfold mutex_del_wake_tcb_writable; cbn; auto)
    ltac:(unfold mutex_del_wake_tcb_value_in_range; cbn; lia) Hpre Hdly) as Hd.
  pose proof (mutex_del_wake_tcb_store pointer (tcb_write (task_tcb64_image sg task) TCBDly (Some 0))
    TCBMsg 0 delayed messaged frame ltac:(unfold mutex_del_wake_tcb_writable; cbn; auto)
    ltac:(unfold mutex_del_wake_tcb_value_in_range; cbn; lia) Hd Hmsg) as Hm.
  pose proof (mutex_del_wake_tcb_byte_load pointer
    (tcb_write (tcb_write (task_tcb64_image sg task) TCBDly (Some 0)) TCBMsg (Some 0))
    TCBStat (encode_task_status task.(stat)) messaged frame ltac:(cbn; auto) eq_refl Hm) as Hactual.
  assert (bits = encode_task_status task.(stat)) by (eapply uchar_load_deterministic; eassumption); subst bits.
  assert (Eclear : event_task_remove_cleared (encode_task_status task.(stat)) 1 =
    task_status_clear_wait (encode_task_status task.(stat)) 1).
  { symmetry; apply task_status_clear_wait_byte_complement; lia. }
  rewrite Eclear in Hstat.
  pose proof (mutex_del_wake_tcb_store pointer
    (tcb_write (tcb_write (task_tcb64_image sg task) TCBDly (Some 0)) TCBMsg (Some 0))
    TCBStat (task_status_clear_wait (encode_task_status task.(stat)) 1) messaged status_written frame
    ltac:(unfold mutex_del_wake_tcb_writable; cbn; auto)
    (task_status_clear_wait_in_range _ _ (proj1 Hactual)) Hm Hstat) as Hs.
  exact (mutex_del_wake_tcb_store pointer _ TCBStatPend 0 status_written after frame
    ltac:(unfold mutex_del_wake_tcb_writable; cbn; auto)
    ltac:(unfold mutex_del_wake_tcb_value_in_range; cbn; lia) Hs Hpend).
Qed.

Definition sem_post_waiter_execution (sg : StableGlobVars) (pe returned : Z)
  (before after : model) : Prop :=
  exists pointer row prefixed readied,
    mutex_del_wake_selection_execution sg pe pointer row returned before /\
    sem_post_waiter_prefix_execution pointer before prefixed /\
    mutex_del_waiter_ready_execution pointer sg.(g_OSRdyGrp) sg.(g_OSRdyTbl) row prefixed readied /\
    mutex_del_waiter_remove_execution pointer (pe + OSEventGrp_off) (pe + OSEventTbl_off) readied after.

Lemma sem_post_waiter_source_post : forall sg tasks eid event tid task group rows returned
  before after (frame : Assertion),
  (event_task_rdy_pre sg tasks eid event tid task 1 0 group rows ** frame) before ->
  sem_post_waiter_execution sg (event_addr sg eid) returned before after ->
  (event_task_rdy_post sg tasks eid event tid task 0 1 0 group rows returned ** frame) after.
Proof.
  intros sg tasks eid event tid task group rows returned before after frame Hpre
    (pointer & row & prefixed & readied & Hselection & Hprefix & Hready & Hremove).
  assert (Hselection_pre : (event_task_rdy_pre sg tasks eid event tid task 16 2 group rows ** frame) before).
  { assert (Hbounds : event_task_rdy_pre sg tasks eid event tid task 1 0 group rows ** frame |--
      event_task_rdy_pre sg tasks eid event tid task 16 2 group rows ** frame).
    { unfold event_task_rdy_pre; entailer!; lia. }
    exact (Hbounds before Hpre). }
  destruct (mutex_del_wake_selection_resources sg tasks eid event tid task group rows pointer row returned
    before frame Hselection_pre Hselection) as [Epointer [Erow Ereturned]].
  subst pointer row returned.
  set (image := event_task_rdy_before_remove_image sg task 0 1 0).
  set (bits := task_status_clear_wait (encode_task_status task.(stat)) 1).
  set (ready_group := event_task_rdy_ready_group bits group (tcb_bit_y_of_prio task.(curPrio))).
  set (ready_rows := event_task_rdy_ready_rows bits (tcb_y_of_prio task.(curPrio))
    (tcb_bit_x_of_prio task.(curPrio)) rows).
  set (prefix_frame := event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
      (event_image sg tasks event) ** unmap_table_rep sg ** store_prio_tbl sg tasks.(prioTbl) **
    sg.(g_OSRdyGrp) # UChar |-> group ** UCharArray.full sg.(g_OSRdyTbl) 8 rows ** frame).
  assert (Hopen : event_task_rdy_pre sg tasks eid event tid task 1 0 group rows ** frame |--
    coq_prop (event_task_rdy_entry sg tasks eid event tid task) &&
    (tcb64_storage_rep (task_slot_addr sg tid) (task_tcb64_image sg task) ** prefix_frame)).
  { unfold event_task_rdy_pre, prefix_frame; entailer!; tauto. }
  destruct (Hopen before Hpre) as [Hentry Howned].
  pose proof (sem_post_waiter_prefix_resources sg task (task_slot_addr sg tid) before prefixed
    prefix_frame Howned Hprefix) as Hprefixed.
  destruct (event_task_rdy_selection sg tasks eid event tid task Hentry)
    as [Hpriority [Htable [Hvalid [Hrange _]]]].
  pose proof (proj1 (proj2 (priority_coordinates_in_range_and_encoding_eq__priority_encoding
    task.(curPrio) Hrange))) as Hrow.
  set (ready_frame := event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
      (event_image sg tasks event) ** unmap_table_rep sg ** store_prio_tbl sg tasks.(prioTbl) ** frame).
  assert (Hready_order : tcb64_storage_rep (task_slot_addr sg tid) image ** prefix_frame |--
    tcb64_storage_rep (task_slot_addr sg tid) image ** sg.(g_OSRdyGrp) # UChar |-> group **
    UCharArray.full sg.(g_OSRdyTbl) 8 rows ** ready_frame)
    by (unfold prefix_frame, ready_frame; entailer!).
  pose proof (mutex_del_waiter_ready_resources (task_slot_addr sg tid) image sg.(g_OSRdyGrp) sg.(g_OSRdyTbl)
    (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio)) (tcb_bit_y_of_prio task.(curPrio))
    bits group rows prefixed readied ready_frame Hrow eq_refl eq_refl eq_refl
    (Hready_order prefixed Hprefixed) Hready) as Hreadied.
  set (remove_frame := unmap_table_rep sg ** store_prio_tbl sg tasks.(prioTbl) **
    sg.(g_OSRdyGrp) # UChar |-> ready_group ** UCharArray.full sg.(g_OSRdyTbl) 8 ready_rows ** frame).
  set (remove_rest :=
    event_task_remove_tcb_frame (task_slot_addr sg tid) image **
    event_task_remove_ecb_frame sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
      (event_image sg tasks event) (tcb_y_of_prio task.(curPrio)) ** remove_frame).
  set (remove_pre := event_task_remove_pre (task_slot_addr sg tid) (event_addr sg eid + 10)
    (event_addr sg eid + 11) (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio))
    (tcb_bit_y_of_prio task.(curPrio))
    (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
    (encode_event_wait_grp event.(waitList) tasks)).
  assert (Hremove_open : tcb64_storage_rep (task_slot_addr sg tid) image **
      sg.(g_OSRdyGrp) # UChar |-> ready_group ** UCharArray.full sg.(g_OSRdyTbl) 8 ready_rows ** ready_frame |--
    remove_pre ** remove_rest).
  { match goal with |- ?P |-- ?Q => assert (Horder : P |--
      (tcb64_storage_rep (task_slot_addr sg tid) image **
       event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid) (event_image sg tasks event)) **
      remove_frame) end.
    { unfold ready_frame, remove_frame; entailer!. }
    match type of Horder with _ |-- ?R => match goal with |- _ |-- ?Q =>
      assert (Hfinish : R |-- Q) end end.
    {
    unfold remove_pre, remove_rest.
    sep_apply_l_atomic (event_task_remove_storage_split sg.(osKernelConfig).(cfgEventNames)
      (task_slot_addr sg tid) (event_addr sg eid) image (event_image sg tasks event)
      (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio)) (tcb_bit_y_of_prio task.(curPrio))
      (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
      (encode_event_wait_grp event.(waitList) tasks) Hrow eq_refl eq_refl eq_refl
      (event_table_image_eq sg tasks event _ Hrow) eq_refl); entailer!. }
    intros cut_heap Hcut_heap; exact (Hfinish cut_heap (Horder cut_heap Hcut_heap)). }
  pose proof (mutex_del_waiter_remove_resources (task_slot_addr sg tid) (event_addr sg eid + 10)
    (event_addr sg eid + 11) (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio))
    (tcb_bit_y_of_prio task.(curPrio))
    (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
    (encode_event_wait_grp event.(waitList) tasks) readied after remove_rest
    (Hremove_open readied Hreadied) Hremove) as Hremoved.
  destruct Hentry as [Hsg [Hlayout [Hmulti [Htasks [Hconsistency [Hhead Hlookup]]]]]].
  assert (Hunique : task_priority_unique tasks) by (unfold task_in_range in Htasks; tauto).
  assert (Hcanonical : event_waitList_canonical sg tasks event.(waitList)) by (exact (proj1 Hconsistency)).
  assert (Hclose : event_task_remove_post (task_slot_addr sg tid) (event_addr sg eid + 10)
      (event_addr sg eid + 11) (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio))
      (tcb_bit_y_of_prio task.(curPrio))
      (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
      (encode_event_wait_grp event.(waitList) tasks) ** remove_rest |--
    event_task_rdy_post sg tasks eid event tid task 0 1 0 group rows task.(curPrio) ** frame).
  { unfold remove_rest.
    match goal with |- ?P |-- ?Q => assert (Horder : P |--
      (event_task_remove_post (task_slot_addr sg tid) (event_addr sg eid + 10)
        (event_addr sg eid + 11) (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio))
        (tcb_bit_y_of_prio task.(curPrio))
        (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
        (encode_event_wait_grp event.(waitList) tasks) **
       event_task_remove_tcb_frame (task_slot_addr sg tid) image **
       event_task_remove_ecb_frame sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
         (event_image sg tasks event) (tcb_y_of_prio task.(curPrio))) ** remove_frame) end.
    { entailer!. }
    match type of Horder with _ |-- ?R => match goal with |- _ |-- ?Q =>
      assert (Hfinish : R |-- Q) end end.
    {
    unfold remove_frame, event_task_rdy_post.
    sep_apply_l_atomic (event_task_remove_storage_merge_updated sg.(osKernelConfig).(cfgEventNames)
      (task_slot_addr sg tid) (event_addr sg eid) image (event_image sg tasks event)
      (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio)) (tcb_bit_y_of_prio task.(curPrio))
      (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
      (encode_event_wait_grp event.(waitList) tasks) eq_refl eq_refl eq_refl eq_refl).
    unfold tcb_bit_x_of_prio, tcb_bit_y_of_prio, tcb_x_of_prio, tcb_y_of_prio.
    rewrite <- (event_remove_waiter_image_eq sg tasks event tid task Hsg Hunique Hcanonical Hvalid Hlookup).
    unfold image, ready_group, ready_rows, bits, event_task_rdy_task_image; entailer!; lia. }
    intros cut_heap Hcut_heap; exact (Hfinish cut_heap (Horder cut_heap Hcut_heap)). }
  exact (Hclose after Hremoved).
Qed.

Lemma sem_post_wake_preserves_continuations : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg entry eid event tid old local active,
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  task_stack_live_coverage entry.(TskState) active ->
  let after := event_wake_state sg entry eid event tid old PendSem 0 PendOK in
  store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
    entry.(TskState).(parkedTaskStacks) |--
  coq_prop (task_stack_live_coverage after.(TskState) active) &&
  store_parked_continuations (kernel_saved_continuation_entry abi after.(TskState) local)
    after.(TskState).(parkedTaskStacks).
Proof.
  intros external platform port abi sg entry eid event tid old local active Hold Hcoverage after.
  assert (Hnodes : forall slot node, after.(TskState).(inUsedTaskStates) slot = Some node ->
    exists previous, entry.(TskState).(inUsedTaskStates) slot = Some previous /\
      previous.(taskGeneration) = node.(taskGeneration) /\ previous.(tcbStkPtr) = node.(tcbStkPtr)).
  { intros slot node Hnode.
    change ((if Z.eqb slot tid then Some (task_event_wake_single old PendSem 0 PendOK)
      else entry.(TskState).(inUsedTaskStates) slot) = Some node) in Hnode.
    destruct (Z.eqb slot tid) eqn:Hslot.
    - apply Z.eqb_eq in Hslot; subst slot; injection Hnode as Hnode; subst node.
      exists old; repeat split; assumption || reflexivity.
    - exists node; repeat split; assumption || reflexivity. }
  assert (Hcovered : task_stack_live_coverage after.(TskState) active).
  { eapply task_stack_live_coverage_used_map_frame with (before := entry.(TskState));
      [|reflexivity|exact Hcoverage].
    intros slot node Hnode; destruct (Hnodes slot node Hnode) as [previous [Hprevious [Hgen Hsp]]].
    exists previous; auto. }
  assert (Htransport :
    store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
      entry.(TskState).(parkedTaskStacks) |--
    store_parked_continuations (kernel_saved_continuation_entry abi after.(TskState) local)
      after.(TskState).(parkedTaskStacks)).
  { change (store_parked_continuations
      (kernel_saved_continuation_entry abi entry.(TskState) local) entry.(TskState).(parkedTaskStacks) |--
      store_parked_continuations
      (kernel_saved_continuation_entry abi after.(TskState) local) entry.(TskState).(parkedTaskStacks)).
    apply kernel_saved_continuation_map_reindex.
    intros key payload node Hpayload Hnode Hgen; apply Hnodes; exact Hnode. }
  sep_apply_l_atomic Htransport; entailer!.
Qed.

End SemPendEventReadySource.
Import SemPendEventReadySource.

(** This is only the additional fact at THIS classified call. All source
    constructors remain available. The raw EventReady case needs its real
    caller's type/result observation; every other classifier already has
    the input required by its receipt constructor in the actual step. *)
Inductive sem_pend_source_client_call_input external :
  forall action, StableGlobVars -> UCOS2_Verify_State ->
    tmr_task_source_client external action -> Prop :=
| SemPendCallInputNontimer : forall action sg before source,
    sem_pend_source_client_call_input external action sg before
      (TmrTaskSourceScheduler external action (TmrTaskSchedulerNontimer external action source))
| SemPendCallInputProfile : forall cut sg before,
    sem_pend_source_client_call_input external _ sg before
      (TmrTaskSourceScheduler external _ (TmrTaskSchedulerProfile external cut))
| SemPendCallInputChangePrio : forall actor requested priority sg before,
    sem_pend_source_client_call_input external _ sg before
      (TmrTaskSourceScheduler external _ (TmrTaskSchedulerChangePrio external actor requested priority))
| SemPendCallInputFlagReady : forall actor pointer bits result sg before,
    sem_pend_source_client_call_input external _ sg before
      (TmrTaskSourceScheduler external _ (TmrTaskSchedulerFlagReady external actor pointer bits result))
| SemPendCallInputEventReady : forall actor event kind message result sg before,
    tmr_task_sem_event_ready_call_input sg before event kind result ->
    sem_pend_source_client_call_input external _ sg before
      (TmrTaskSourceScheduler external _ (TmrTaskSchedulerEventReady external actor event kind message result))
| SemPendCallInputTickTask : forall slot previous sg before,
    sem_pend_source_client_call_input external _ sg before
      (TmrTaskSourceScheduler external _ (TmrTaskSchedulerTickTask external slot previous))
| SemPendCallInputInstall : forall context outgoing incoming resumed sg before,
    sem_pend_source_client_call_input external _ sg before
      (TmrTaskSourceScheduler external _ (TmrTaskSchedulerTaskInstall external context outgoing incoming resumed))
| SemPendCallInputSem : forall action sg before source,
    sem_pend_source_client_call_input external action sg before
      (TmrTaskSourceSem external action source)
| SemPendCallInputCritical : forall action sg before source,
    sem_pend_source_client_call_input external action sg before
      (TmrTaskSourceCritical external action source)
| SemPendCallInputTick : forall actor cut sg before,
    sem_pend_source_client_call_input external _ sg before (TmrTaskSourceTick external actor cut)
| SemPendCallInputTimer : forall actor cut sg before,
    sem_pend_source_client_call_input external _ sg before (TmrTaskSourceTimer external actor cut)
| SemPendCallInputTimerCall : forall actor source_sg cut entry timers sg before,
    sem_pend_source_client_call_input external _ sg before
      (TmrTaskSourceTimerCall external actor source_sg cut entry timers)
| SemPendCallInputSemAbort : forall actor event option result sg before,
    sem_pend_source_client_call_input external _ sg before
      (TmrTaskSourceSemAbortCall external actor event option result)
| SemPendCallInputSuspend : forall actor source_sg priority result entry returned sg before,
    sem_pend_source_client_call_input external _ sg before
      (TmrTaskSourceSuspendCall external actor source_sg priority result entry returned).

Lemma sem_pend_source_client_call_receipt :
  forall external action sg before after (source : tmr_task_source_client external action),
  sem_pend_source_client_call_input external action sg before source ->
  kernel_client_step action sg before after ->
  tmr_task_source_call_receipt external action sg before after.
Proof.
  intros external action sg before after source Hinput Hstep; destruct Hinput.
  - apply TmrTaskCallNontimer; assumption.
  - apply TmrTaskCallProfile; assumption.
  - apply TmrTaskCallChangePrio; assumption.
  - apply TmrTaskCallFlagReady; assumption.
  - apply TmrTaskCallEventReady; assumption.
  - apply TmrTaskCallTickTask; assumption.
  - apply TmrTaskCallInstall; assumption.
  - apply TmrTaskCallSem; assumption.
  - apply TmrTaskCallCritical; assumption.
  - apply TmrTaskCallTick; assumption.
  - apply TmrTaskCallTimer; assumption.
  - apply TmrTaskCallTimerCall; assumption.
  - apply TmrTaskCallSemAbort; assumption.
  - apply TmrTaskCallSuspend; assumption.
Qed.

(** The three existing concrete Wake effects preserve the current
    pointer and Timer fields. No such frame is asserted for a generic
    registered action or a scheduler/interrupt installation. *)
Lemma sem_pend_wake_source_current_timer_frame : forall sg entry returned,
  WakeComponent.kernel_wake_c_source sg entry returned ->
  entry.(SchedState).(curTaskID) = returned.(SchedState).(curTaskID) /\
  entry.(TimerState) = returned.(TimerState).
Proof.
  intros sg entry returned Hsource; destruct Hsource.
  - destruct (flag_task_rdy_result _ _ _ _ _ _ _ H)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    split; reflexivity.
  - unfold event_task_rdy in H.
    destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
    destruct (entry.(TskState).(prioTbl) (event_wait_priority entry.(TskState) event))
      as [| |slot]; try discriminate.
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|]; [|discriminate].
    injection H as Hpriority Hreturned; subst returned.
    split; [|reflexivity].
    cbn [event_wake_state replace_SchedS SchedState].
    symmetry; apply (proj1 (sched_wake_by_status_current_cache_frame _ _ _ _ _)).
  - unfold tick_task_step, sched_wake_by_status; cbn zeta;
      repeat match goal with |- context [if ?c then _ else _] => destruct c end;
      split; reflexivity.
Qed.

(** The input and output heaps are the actual helper call's. The segment,
    receipt, annotated source and raw output owner all name the SAME wake.
    This producer does not assert a fields/continuation reassembly. *)
Lemma sem_pend_event_ready_c_post_source_receipt :
  forall external port clients sg observer event_observer origin actor entry event node
    selected old kind message result returned frame before after,
  clients (event_task_rdy_source_client actor event kind message result) ->
  actor <> Some observer ->
  entry.(EventState).(inUsedEventStates) event = Some node ->
  event_type_to_pend_type node.(eventType) = Some kind -> result <> PendTimeout ->
  (WakeComponent.event_ready_c_input sg entry event node selected old kind result ** frame) before ->
  (WakeComponent.event_ready_c_output sg entry event node selected old kind message result returned ** frame) after ->
  let wake := event_wake_state sg entry event node selected old kind message result in
  WakeComponent.kernel_wake_c_segment sg entry before
    (WakeComponent.event_ready_c_input sg entry event node selected old kind result ** frame)
    wake after
    (WakeComponent.event_ready_c_output sg entry event node selected old kind message result returned ** frame) /\
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event kind message result) sg entry wake /\
  (exists trace : kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin entry false origin wake,
    sem_pend_resumption_source_calls external port clients sg observer event_observer
      origin entry false origin wake trace) /\
  (WakeComponent.event_ready_c_output sg entry event node selected old kind message result returned ** frame) after.
Proof.
  intros external port clients sg observer event_observer origin actor entry event node selected old kind
    message result returned frame before after Hmember Hforeign Hnode Hkind Hresult Hpre Hpost wake.
  destruct (tmr_task_event_ready_c_post_receipt external actor sg entry event node selected old kind
    message result returned frame before after Hnode Hkind Hresult Hpre Hpost) as [Hsegment Hreceipt].
  destruct (sem_pend_wake_source_current_timer_frame sg entry wake
    (WakeComponent.kernel_wake_c_segment_source _ _ _ _ _ _ _ Hsegment)) as [Hcurrent Htimer].
  split; [exact Hsegment|]. split; [exact Hreceipt|]. split; [|exact Hpost].
  change (exists trace : kernel_resumption_task_source_trace external port clients sg observer event_observer
    origin entry (kernel_client_stops (event_task_rdy_source_client actor event kind message result) observer) origin wake,
    sem_pend_resumption_source_calls external port clients sg observer event_observer origin entry
      (kernel_client_stops (event_task_rdy_source_client actor event kind message result) observer) origin wake trace).
  eapply sem_pend_framed_source_step_calls with
    (action := event_task_rdy_source_client actor event kind message result).
  - exact Hmember.
  - exact Hforeign.
  - intros; discriminate.
  - eapply tmr_task_source_call_receipt_step; exact Hreceipt.
  - exact Hcurrent.
  - exact Htimer.
  - exact Hreceipt.
Qed.

(** Flag's existing post selects checkpoint/schedule once. Its node-return
    loan and outer frame remain the actual successor owner. *)
Lemma sem_pend_flag_ready_c_post_source_receipt :
  forall external port clients sg observer event_observer origin actor entry pointer waiter old bits result
    returned frame before after,
  clients (flag_task_rdy_source_client actor pointer bits result) -> actor <> Some observer ->
  (flag_task_rdy_pre sg entry pointer waiter old bits ** frame) before ->
  (flag_task_rdy_post sg entry pointer waiter bits result returned ** frame) after ->
  exists checkpoint, exists schedule : bool,
    WakeComponent.kernel_wake_c_segment sg entry before
      (flag_task_rdy_pre sg entry pointer waiter old bits ** frame) checkpoint after
      ((coq_prop (returned = (if schedule then 1 else 0) /\ valid_flag_state sg checkpoint.(FlagState)) &&
        (flag_task_rdy_resources sg checkpoint ** flag_node_return_loan sg.(osKernelConfig) waiter)) ** frame) /\
    (exists trace : kernel_resumption_task_source_trace external port clients sg observer event_observer
        origin entry false origin checkpoint,
      sem_pend_resumption_source_calls external port clients sg observer event_observer
        origin entry false origin checkpoint trace) /\
    ((coq_prop (returned = (if schedule then 1 else 0) /\ valid_flag_state sg checkpoint.(FlagState)) &&
      (flag_task_rdy_resources sg checkpoint ** flag_node_return_loan sg.(osKernelConfig) waiter)) ** frame) after.
Proof.
  intros external port clients sg observer event_observer origin actor entry pointer waiter old bits result
    returned frame before after Hmember Hforeign Hpre
    [hbody [hframe [Hjoin [[checkpoint [schedule [[Hstep [Hreturned Hvalid]] Hbody]]] Hframe]]]].
  assert (Hpost : ((coq_prop (returned = (if schedule then 1 else 0) /\
      valid_flag_state sg checkpoint.(FlagState)) &&
      (flag_task_rdy_resources sg checkpoint ** flag_node_return_loan sg.(osKernelConfig) waiter)) ** frame) after).
  { exists hbody, hframe; split; [exact Hjoin|]. split; [split; [split; assumption|exact Hbody]|exact Hframe]. }
  assert (Hsegment : WakeComponent.kernel_wake_c_segment sg entry before
    (flag_task_rdy_pre sg entry pointer waiter old bits ** frame) checkpoint after
    ((coq_prop (returned = (if schedule then 1 else 0) /\ valid_flag_state sg checkpoint.(FlagState)) &&
      (flag_task_rdy_resources sg checkpoint ** flag_node_return_loan sg.(osKernelConfig) waiter)) ** frame)).
  { eapply WakeComponent.KernelWakeCFlagSegment; eassumption. }
  assert (Hreceipt : tmr_task_source_call_receipt external
    (flag_task_rdy_source_client actor pointer bits result) sg entry checkpoint).
  { eapply sem_pend_source_client_call_receipt with
      (source := TmrTaskSourceScheduler external _ (TmrTaskSchedulerFlagReady external actor pointer bits result)).
    - constructor.
    - exists schedule; exact Hstep. }
  destruct (sem_pend_wake_source_current_timer_frame sg entry checkpoint
    (WakeComponent.kernel_wake_c_segment_source _ _ _ _ _ _ _ Hsegment)) as [Hcurrent Htimer].
  exists checkpoint, schedule; split; [exact Hsegment|]. split; [|exact Hpost].
  eapply sem_pend_framed_source_step_calls with (action := flag_task_rdy_source_client actor pointer bits result).
  - exact Hmember.
  - exact Hforeign.
  - intros; discriminate.
  - exists schedule; exact Hstep.
  - exact Hcurrent.
  - exact Htimer.
  - exact Hreceipt.
Qed.

(** Tick consumes its existing body merge at the actual heap, retaining
    the original UCOS2 owner and frame. It is not converted to fields. *)
Lemma sem_pend_tick_c_post_source_receipt :
  forall external port clients sg observer event_observer origin entry slot old frame before after,
  clients (time_tick_task_source_client slot old) ->
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  time_tick_lookup entry slot old ->
  (UCOS2_inv sg entry ** frame) before ->
  ((time_tick_body_cells sg slot (tick_task_update old)
       (time_tick_ready_group (tick_task_step sg slot old entry))
       (time_tick_ready_rows (tick_task_step sg slot old entry)) **
     time_tick_body_residual sg entry slot old) ** frame) after ->
  WakeComponent.kernel_wake_c_segment sg entry before (UCOS2_inv sg entry ** frame)
    (tick_task_step sg slot old entry) after (UCOS2_inv sg (tick_task_step sg slot old entry) ** frame) /\
  (exists trace : kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin entry false origin (tick_task_step sg slot old entry),
    sem_pend_resumption_source_calls external port clients sg observer event_observer
      origin entry false origin (tick_task_step sg slot old entry) trace) /\
  (UCOS2_inv sg (tick_task_step sg slot old entry) ** frame) after.
Proof.
  intros external port clients sg observer event_observer origin entry slot old frame before after
    Hmember Hmulti Hlookup Hpre Hpost.
  pose proof (WakeComponent.time_tick_body_c_post_segment sg entry slot old frame before after
    Hmulti Hlookup Hpre Hpost) as Hsegment.
  pose proof (proj2 (WakeComponent.kernel_wake_c_segment_resources _ _ _ _ _ _ _ Hsegment)) as Howned.
  assert (Hreceipt : tmr_task_source_call_receipt external (time_tick_task_source_client slot old)
    sg entry (tick_task_step sg slot old entry)).
  { eapply sem_pend_source_client_call_receipt with
      (source := TmrTaskSourceScheduler external _ (TmrTaskSchedulerTickTask external slot old)).
    - constructor.
    - split; [exact Hlookup|reflexivity]. }
  destruct (sem_pend_wake_source_current_timer_frame sg entry (tick_task_step sg slot old entry)
    (WakeComponent.kernel_wake_c_segment_source _ _ _ _ _ _ _ Hsegment)) as [Hcurrent Htimer].
  split; [exact Hsegment|]. split; [|exact Howned].
  eapply sem_pend_framed_source_step_calls with (action := time_tick_task_source_client slot old).
  - exact Hmember.
  - discriminate.
  - intros; discriminate.
  - split; [exact Hlookup|reflexivity].
  - exact Hcurrent.
  - exact Htimer.
  - exact Hreceipt.
Qed.

(** Concrete EventReady resource producer: reuse the real SemPost merge
    on its original helper post and residual. Determinism identifies the
    merge's existential result with the SAME wake used for the receipt.
    The full UCOS2/unmap owner is retained; no fields owner is invented. *)
Lemma sem_pend_sem_post_wake_source_resources :
  forall external port clients sg observer event_observer origin actor entry event node selected old
    returned frame before after,
  clients (event_task_rdy_source_client actor event PendSem 0 PendOK) -> actor <> Some observer ->
  UCOS2_state_inv sg entry -> sem_post_lookup entry event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  (WakeComponent.event_ready_c_input sg entry event node selected old PendSem PendOK **
    (sem_post_wake_frame sg entry event selected ** frame)) before ->
  (WakeComponent.event_ready_c_output sg entry event node selected old PendSem 0 PendOK returned **
    (sem_post_wake_frame sg entry event selected ** frame)) after ->
  let wake := event_wake_state sg entry event node selected old PendSem 0 PendOK in
  WakeComponent.kernel_wake_c_segment sg entry before
    (WakeComponent.event_ready_c_input sg entry event node selected old PendSem PendOK **
      (sem_post_wake_frame sg entry event selected ** frame)) wake after
    (WakeComponent.event_ready_c_output sg entry event node selected old PendSem 0 PendOK returned **
      (sem_post_wake_frame sg entry event selected ** frame)) /\
  (exists trace : kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin entry false origin wake,
    sem_pend_resumption_source_calls external port clients sg observer event_observer
      origin entry false origin wake trace) /\
  (UCOS2_inv sg wake ** unmap_table_rep sg ** frame) after.
Proof.
  intros external port clients sg observer event_observer origin actor entry event node selected old
    returned frame before after Hmember Hforeign Hvalid Hlookup Htype Hpre Hpost wake.
  pose proof Hpre as [body [rest [Hjoin [[[Hentry Hbytes] Hbody] Hrest]]]].
  assert (Hkind : event_type_to_pend_type node.(eventType) = Some PendSem)
    by (rewrite Htype; reflexivity).
  destruct (sem_pend_event_ready_c_post_source_receipt external port clients sg observer event_observer origin
    actor entry event node selected old PendSem 0 PendOK returned
    (sem_post_wake_frame sg entry event selected ** frame) before after
    Hmember Hforeign Hlookup Hkind ltac:(discriminate) Hpre Hpost)
    as [Hsegment [Hreceipt [Hcalls Hraw]]].
  assert (Hmerge :
    WakeComponent.event_ready_c_output sg entry event node selected old PendSem 0 PendOK returned **
      (sem_post_wake_frame sg entry event selected ** frame) |--
    EX final, coq_prop (sem_post_wake_result sg event entry final returned) &&
      (UCOS2_inv sg final ** unmap_table_rep sg ** frame)).
  { unfold WakeComponent.event_ready_c_output.
    cbn [task_pend_mask encode_pend_status]; sepcon_assoc_change.
    sep_apply_l_atomic (sem_post_wake_merge_full sg entry event node selected old returned
      Hvalid Hlookup Htype Hentry).
    Intros final; Exists final; entailer!. }
  destruct (Hmerge after Hraw) as [final [Hresult Howned]].
  pose proof (WakeComponent.event_task_rdy_c_entry_source sg entry event node selected old PendSem 0 PendOK
    Hlookup Hentry) as Hactual.
  unfold sem_post_wake_result in Hresult.
  assert (Hsame : final = wake) by (unfold wake; congruence).
  subst final; split; [exact Hsegment|]. split; assumption.
Qed.

(** Consume the concrete SemPost packet in the actual prefix constructor.
    Its source is appended before any module result hides it; its owner
    remains the actual after heap and can feed the next module. *)
Lemma sem_pend_sem_post_wake_append_resources :
  forall external port clients sg observer event_observer first initial stopped origin entry
    (prefix : kernel_resumption_task_source_trace external port clients sg observer event_observer
      first initial stopped origin entry),
  sem_pend_resumption_source_calls external port clients sg observer event_observer
    first initial stopped origin entry prefix ->
  forall actor event node selected old returned frame before after,
  clients (event_task_rdy_source_client actor event PendSem 0 PendOK) -> actor <> Some observer ->
  UCOS2_state_inv sg entry -> sem_post_lookup entry event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  (WakeComponent.event_ready_c_input sg entry event node selected old PendSem PendOK **
    (sem_post_wake_frame sg entry event selected ** frame)) before ->
  (WakeComponent.event_ready_c_output sg entry event node selected old PendSem 0 PendOK returned **
    (sem_post_wake_frame sg entry event selected ** frame)) after ->
  let wake := event_wake_state sg entry event node selected old PendSem 0 PendOK in
  (exists trace : kernel_resumption_task_source_trace external port clients sg observer event_observer
      first initial stopped origin wake,
    sem_pend_resumption_source_calls external port clients sg observer event_observer
      first initial stopped origin wake trace) /\
  (UCOS2_inv sg wake ** unmap_table_rep sg ** frame) after.
Proof.
  intros external port clients sg observer event_observer first initial stopped origin entry prefix Hprefix
    actor event node selected old returned frame before after Hmember Hforeign Hvalid Hlookup Htype Hpre Hpost wake.
  destruct (sem_pend_sem_post_wake_source_resources external port clients sg observer event_observer origin actor
    entry event node selected old returned frame before after Hmember Hforeign Hvalid Hlookup Htype Hpre Hpost)
    as [Hsegment [[suffix Hsuffix] Howned]].
  split; [|exact Howned].
  rewrite <- (Bool.orb_false_r stopped).
  exact (sem_pend_resumption_source_calls_append external port clients sg observer event_observer
    first initial stopped origin entry prefix Hprefix false origin wake suffix Hsuffix).
Qed.

(** The fields footprint uses the existing Event/Task/Scheduler residual
    from SemPend. Flag padding is absent from both sides, while the actual
    six-field Flag owner and every other module remain owned. *)
Definition sem_pend_event_ready_fields_frame sg entry event selected : Assertion :=
  sem_post_task_frame sg entry.(TskState) selected **
  sched_physical_rep sg entry.(SchedState) **
  event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) event **
  sem_pend_fields_task_sched_event_frame sg entry.

Lemma sem_pend_event_ready_fields_residual : forall sg entry event node selected old kind message result,
  entry.(EventState).(inUsedEventStates) event = Some node ->
  sem_pend_fields_task_sched_event_frame sg entry |--
  sem_pend_fields_task_sched_event_frame sg
    (event_wake_state sg entry event node selected old kind message result).
Proof.
  intros sg entry event node selected old kind message result Hnode.
  unfold sem_pend_fields_task_sched_event_frame, event_wake_state; simpl.
  sep_apply_l_atomic (queue_set_event_wait_list_preserves_storage sg entry.(EventState)
    event node (remove_Z_eqb selected node.(waitList)) Hnode); entailer!.
Qed.

Lemma sem_pend_event_ready_fields_merge_state : forall sg entry event node selected old kind message result,
  UCOS2_state_inv sg entry -> entry.(EventState).(inUsedEventStates) event = Some node ->
  In selected node.(waitList) -> entry.(TskState).(inUsedTaskStates) selected = Some old ->
  event_type_to_pend_type node.(eventType) = Some kind ->
  let wake := event_wake_state sg entry event node selected old kind message result in
  task_public_storage sg wake.(TskState) ** sched_raw_rep sg wake.(TskState) wake.(SchedState) **
  event_raw_rep sg entry.(TskState) wake.(EventState) **
  sem_pend_fields_task_sched_event_frame sg entry |-- UCOS2_fields_inv sg wake.
Proof.
  intros sg entry event node selected old kind message result Hvalid Hnode Hin Hold Hkind wake.
  pose proof (UCOS2_event_wake_preserves_validity sg entry event node selected old kind message result
    Hvalid Hnode Hin Hold Hkind) as Hwake; fold wake in Hwake.
  assert (Hindex : event_raw_rep sg entry.(TskState) wake.(EventState) =
    event_raw_rep sg wake.(TskState) wake.(EventState)).
  { apply event_raw_rep_change_task_index; apply event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hold|reflexivity]. }
  rewrite Hindex.
  sep_apply_l_atomic (sem_pend_event_ready_fields_residual sg entry event node selected old kind message result Hnode).
  fold wake; rewrite sem_pend_fields_inv_split_task_sched_event.
  repeat match goal with |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro end.
  entailer!; try match goal with
    | |- ?left |-- coq_prop ?fact && ?right =>
        let Hspatial := fresh "Hspatial" in
        assert (Hspatial : left |-- right) by entailer!;
        let heap := fresh "heap" in let Hheap := fresh "Hheap" in
        intros heap Hheap; split; [change fact; tauto|exact (Hspatial heap Hheap)]
    end.
Qed.

Lemma sem_pend_event_ready_fields_split : forall sg entry event node,
  UCOS2_state_inv sg entry -> sem_post_lookup entry event node ->
  node.(eventType) = OS_EVENT_TYPE_SEM -> sem_post_group entry node <> 0 ->
  event_object_layout_prop sg event ->
  UCOS2_fields_inv sg entry ** unmap_table_rep sg |-- EX selected old,
    coq_prop (event_task_rdy_entry sg entry.(TskState) event node selected old) &&
    (WakeComponent.event_ready_c_input sg entry event node selected old PendSem PendOK **
      sem_pend_event_ready_fields_frame sg entry event selected).
Proof.
  intros sg entry event node Hvalid Hlookup Htype Hnonempty Hlayout.
  pose proof Hvalid as [Hprofile [Htasks [_ [Hevents _]]]].
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hkind : event_type_to_pend_type node.(eventType) = Some PendSem)
    by (rewrite Htype; reflexivity).
  destruct node.(waitList) as [|selected tail] eqn:Hlist;
    [contradiction Hnonempty; unfold sem_post_group; rewrite Hlist; reflexivity|].
  destruct (event_wake_head sg entry event node selected tail PendSem 0 PendOK
    Hvalid Hlookup Hkind Hlist) as [old [Hold [Hstep [Hafter Hlast]]]].
  pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  assert (Hentry : event_task_rdy_entry sg entry.(TskState) event node selected old).
  { unfold event_task_rdy_entry; split; [exact Hsg|]. split; [exact Hlayout|].
    split; [exact Hmulti|]. split; [exact Htasks|]. split; [exact (Hentries event node Hlookup)|].
    split; [rewrite Hlist; reflexivity|exact Hold]. }
  rewrite sem_pend_fields_inv_split_task_sched_event; Intros.
  sep_apply_l_atomic (sem_post_task_storage_split sg entry.(TskState) selected old Hmulti Hprofiling Hold).
  sep_apply_l_atomic (event_raw_rep_split_eid sg entry.(TskState) entry.(EventState) event node Hlookup).
  unfold sched_raw_rep; rewrite sched_rows_array_equiv.
  Exists selected old; unfold WakeComponent.event_ready_c_input, event_task_rdy_pre,
    sem_pend_event_ready_fields_frame, used_event_rep.
  cbn [task_pend_mask encode_pend_status].
  entailer!; unfold sched_row_values; reflexivity.
Qed.

Lemma sem_pend_event_ready_fields_merge : forall sg entry event node selected old returned,
  UCOS2_state_inv sg entry -> sem_post_lookup entry event node ->
  node.(eventType) = OS_EVENT_TYPE_SEM ->
  event_task_rdy_entry sg entry.(TskState) event node selected old ->
  let wake := event_wake_state sg entry event node selected old PendSem 0 PendOK in
  WakeComponent.event_ready_c_output sg entry event node selected old PendSem 0 PendOK returned **
    sem_pend_event_ready_fields_frame sg entry event selected |--
  coq_prop (sem_post_wake_result sg event entry wake returned) &&
    (UCOS2_fields_inv sg wake ** unmap_table_rep sg).
Proof.
  intros sg entry event node selected old returned Hvalid Hlookup Htype Hentry wake.
  pose proof Hentry as [Hsg [Hlayout [Hmulti [Htasks [Hwait [Hhead Hold]]]]]].
  pose proof (proj1 Hvalid) as Hprofile.
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  pose proof (event_task_rdy_selection sg entry.(TskState) event node selected old Hentry)
    as [_ [_ [_ [Hprio _]]]].
  assert (Hkind : event_type_to_pend_type node.(eventType) = Some PendSem)
    by (rewrite Htype; reflexivity).
  destruct node.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
  inversion Hhead; subst head.
  destruct (event_wake_head sg entry event node selected tail PendSem 0 PendOK
    Hvalid Hlookup Hkind Hlist) as [found [Hfound [Hstep [Hafter Hlast]]]].
  assert (found = old) by congruence; subst found.
  unfold WakeComponent.event_ready_c_output, event_task_rdy_post, sem_pend_event_ready_fields_frame;
    cbn [task_pend_mask encode_pend_status]; Intros.
  assert (Hreturned : returned = old.(curPrio)) by tauto; subst returned.
  rewrite (event_task_rdy_typed_image_eq sg old 0 1 0 PendSem PendOK eq_refl eq_refl).
  rewrite (event_task_rdy_scheduler_group_eq sg entry.(TskState) entry.(SchedState) selected old _ Hold).
  rewrite (event_task_rdy_scheduler_rows_eq sg entry.(TskState) entry.(SchedState) selected old _ Hold Hprio).
  sep_apply_l_atomic (sem_post_task_storage_merge sg entry.(TskState) selected
    (task_event_wake_single old PendSem 0 PendOK) Hmulti Hprofiling).
  fold (used_event_rep sg entry.(TskState) event (event_set_wait_list node (remove_Z_eqb selected node.(waitList)))).
  sep_apply_l_atomic (event_raw_rep_merge_updated_eid sg entry.(TskState) entry.(EventState) event
    (event_set_wait_list node (remove_Z_eqb selected node.(waitList)))).
  rewrite <- sched_rows_array_equiv.
  rewrite <- (sched_wake_by_status_physical_rep_eq sg entry.(TskState) entry.(SchedState) selected
    (task_status_clear_wait (encode_task_status old.(stat)) 1)).
  assert (Hstatus : task_status_clear_wait (encode_task_status old.(stat)) 1 =
    encode_task_status (task_event_wake_single old PendSem 0 PendOK).(stat)).
  { change (task_status_clear_wait (encode_task_status old.(stat)) 1 =
      encode_task_status (task_clear_pending_status old.(stat) PendSem)).
    rewrite task_clear_pending_status_encoding; reflexivity. }
  rewrite Hstatus.
  assert (Hindex : forall s, sched_raw_rep sg entry.(TskState) s =
    sched_raw_rep sg (glob_task_set_usedtask entry.(TskState) selected
      (task_event_wake_single old PendSem 0 PendOK)) s).
  { intro s; apply sched_raw_rep_priority_ext; intros slot Hin.
    simpl; destruct (Z.eqb slot selected) eqn:E;
      [apply Z.eqb_eq in E; subst slot; rewrite Hold|]; reflexivity. }
  set (woken_sched := sched_wake_by_status sg entry.(TskState) entry.(SchedState) selected
    (encode_task_status (task_event_wake_single old PendSem 0 PendOK).(stat))).
  assert (Hsched :
    sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp woken_sched.(readyList) entry.(TskState) **
    sched_rows_rep sg entry.(TskState) woken_sched.(readyList) [0;1;2;3;4;5;6;7] **
    sched_physical_rep sg woken_sched |--
    sched_raw_rep sg (glob_task_set_usedtask entry.(TskState) selected
      (task_event_wake_single old PendSem 0 PendOK)) woken_sched).
  { rewrite <- Hindex; unfold sched_raw_rep; reflexivity. }
  sep_apply_l_atomic Hsched.
  pose proof (sem_pend_event_ready_fields_merge_state sg entry event node selected old PendSem 0 PendOK
    Hvalid Hlookup ltac:(rewrite Hlist; left; reflexivity) Hold Hkind) as Hmerge.
  cbn zeta in Hmerge.
  cbn [event_wake_state replace_SchedS replace_EventS replace_TskS TskState SchedState EventState] in Hmerge.
  fold woken_sched in Hmerge; sep_apply_l_atomic Hmerge.
  unfold sem_post_wake_result, wake; entailer!.
Qed.

(** Reindex the real saved continuation map with the already proved wake
    transport. The local predicate is arbitrary and no padding is added. *)
Lemma sem_pend_event_ready_fields_merge_continuations : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg entry event node selected old returned local active,
  UCOS2_state_inv sg entry -> sem_post_lookup entry event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  event_task_rdy_entry sg entry.(TskState) event node selected old ->
  task_stack_live_coverage entry.(TskState) active ->
  let wake := event_wake_state sg entry event node selected old PendSem 0 PendOK in
  WakeComponent.event_ready_c_output sg entry event node selected old PendSem 0 PendOK returned **
    sem_pend_event_ready_fields_frame sg entry event selected **
    store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
      entry.(TskState).(parkedTaskStacks) |--
  coq_prop (sem_post_wake_result sg event entry wake returned /\
    task_stack_live_coverage wake.(TskState) active) &&
  (kernel_program_fields_inv sg wake **
    store_parked_continuations (kernel_saved_continuation_entry abi wake.(TskState) local)
      wake.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi sg entry event node selected old returned local active
    Hvalid Hlookup Htype Hentry Hcoverage wake.
  pose proof Hentry as [_ [_ [_ [_ [_ [_ Hold]]]]]].
  pose proof (sem_pend_event_ready_fields_merge sg entry event node selected old returned
    Hvalid Hlookup Htype Hentry) as Hmerge.
  cbn zeta in Hmerge; sep_apply_l_atomic Hmerge.
  pose proof (sem_post_wake_preserves_continuations external platform port abi sg entry event node
    selected old local active Hold Hcoverage) as Hstacks.
  cbn zeta in Hstacks; sep_apply_l_atomic Hstacks.
  unfold wake; rewrite kernel_program_fields_inv_split_unmap; entailer!.
Qed.

(** Actual Extra module instance at OSSemPost's nonempty-waiter C body.
    The literal execution produces Hpost from Hpre with an arbitrary frame.
    The helper receipt and registered Post receipt refer to that one wake;
    the trace uses the caller's actual Post registration, without requiring
    or inventing a separate raw EventReady registry membership. *)
Lemma sem_pend_sem_post_fields_execution_source_receipt :
  forall external platform port (abi : Armv7aContinuationABI external platform port) local
    clients sg observer event_observer origin actor entry event node returned before after (frame : Assertion),
  clients (sem_pend_post_source_client actor event) -> actor <> observer ->
  sem_post_lookup entry event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry node <> 0 -> event_object_layout_prop sg event ->
  (kernel_client_continuation_fields_world abi local sg entry ** frame) before ->
  sem_post_waiter_execution sg (event_addr sg event) returned before after ->
  exists selected old,
    let wake := event_wake_state sg entry event node selected old PendSem 0 PendOK in
    event_task_rdy_entry sg entry.(TskState) event node selected old /\
    tmr_task_source_call_receipt external
      (event_task_rdy_source_client (Some actor) event PendSem 0 PendOK) sg entry wake /\
    tmr_task_source_call_receipt external (sem_pend_post_source_client actor event) sg entry wake /\
    (exists trace : kernel_resumption_task_source_trace external port clients sg observer event_observer
        origin entry false origin wake,
      sem_pend_resumption_source_calls external port clients sg observer event_observer
        origin entry false origin wake trace) /\
    (kernel_client_continuation_fields_world abi local sg wake ** frame) after.
Proof.
  intros external platform port abi local clients sg observer event_observer origin actor entry event node
    returned before after frame Hmember Hforeign Hlookup Htype Hgroup Hlayout Hpre Hexecution.
  set (stacks := store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
    entry.(TskState).(parkedTaskStacks)).
  assert (Hopen : kernel_client_continuation_fields_world abi local sg entry ** frame |--
    coq_prop (UCOS2_state_inv sg entry /\ task_stack_live_coverage entry.(TskState) None) &&
    (kernel_program_fields_inv sg entry ** stacks ** frame)).
  { unfold kernel_client_continuation_fields_world, kernel_continuation_inv,
      kernel_program_fields_inv, stacks; entailer!. }
  destruct (Hopen before Hpre) as [[Hvalid Hcoverage] Hworld].
  assert (Hsplit : kernel_program_fields_inv sg entry ** stacks ** frame |--
    EX selected old, coq_prop (event_task_rdy_entry sg entry.(TskState) event node selected old) &&
    (WakeComponent.event_ready_c_input sg entry event node selected old PendSem PendOK **
      (sem_pend_event_ready_fields_frame sg entry event selected ** stacks ** frame))).
  { rewrite kernel_program_fields_inv_split_unmap.
    sep_apply_l_atomic (sem_pend_event_ready_fields_split sg entry event node Hvalid Hlookup Htype Hgroup Hlayout).
    Intros selected old; Exists selected old; entailer!. }
  destruct (Hsplit before Hworld) as [selected [old [Hentry Howned]]].
  pose proof (sem_post_waiter_source_post sg entry.(TskState) event node selected old
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) returned before after
    (sem_pend_event_ready_fields_frame sg entry event selected ** stacks ** frame) Howned Hexecution) as Hpost.
  set (wake := event_wake_state sg entry event node selected old PendSem 0 PendOK).
  assert (Hkind : event_type_to_pend_type node.(eventType) = Some PendSem) by (rewrite Htype; reflexivity).
  destruct (tmr_task_event_ready_c_post_receipt external (Some actor) sg entry event node selected old PendSem
    0 PendOK returned (sem_pend_event_ready_fields_frame sg entry event selected ** stacks ** frame)
    before after Hlookup Hkind ltac:(discriminate) Howned Hpost) as [Hsegment Hhelper].
  assert (Hmerge : WakeComponent.event_ready_c_output sg entry event node selected old PendSem 0 PendOK returned **
      (sem_pend_event_ready_fields_frame sg entry event selected ** stacks ** frame) |--
    coq_prop (sem_post_wake_result sg event entry wake returned) &&
      (kernel_client_continuation_fields_world abi local sg wake ** frame)).
  { pose proof (sem_pend_event_ready_fields_merge_continuations external platform port abi sg entry event node
      selected old returned local None Hvalid Hlookup Htype Hentry Hcoverage) as Hjoin.
    cbn zeta in Hjoin; unfold stacks, wake; sepcon_assoc_change; sep_apply_l_atomic Hjoin.
    unfold kernel_client_continuation_fields_world, kernel_continuation_inv; entailer!. }
  destruct (Hmerge after Hpost) as [Hwake Hresources].
  assert (Hstep : kernel_client_step (sem_pend_post_source_client actor event) sg entry wake).
  { exists (OS_ERR_NONE, true); eapply sem_post_wake_result_critical; eassumption. }
  assert (Hreceipt : tmr_task_source_call_receipt external (sem_pend_post_source_client actor event) sg entry wake).
  { eapply sem_pend_source_client_call_receipt with
      (source := TmrTaskSourceSem external _ (TmrTaskSemPost actor event)); [constructor|exact Hstep]. }
  destruct (sem_pend_wake_source_current_timer_frame sg entry wake
    (WakeComponent.kernel_wake_c_segment_source _ _ _ _ _ _ _ Hsegment)) as [Hcurrent Htimer].
  exists selected, old; fold wake.
  split; [exact Hentry|]. split; [exact Hhelper|]. split; [exact Hreceipt|]. split; [|exact Hresources].
  eapply sem_pend_framed_source_step_calls with (action := sem_pend_post_source_client actor event).
  - exact Hmember.
  - cbn [sem_pend_post_source_client kernel_client_actor]; congruence.
  - intros; discriminate.
  - exact Hstep.
  - exact Hcurrent.
  - exact Htimer.
  - exact Hreceipt.
Qed.

(** The fields Flag sibling already has an actual helper interpretation
    and merge. Keep its returned node loan and reindexed map; the caller's
    later Next read/publication must still consume that real loan. *)
Lemma sem_pend_flag_ready_fields_call_source_receipt :
  forall external platform port (abi : Armv7aContinuationABI external platform port) local
    clients sg observer event_observer origin actor entry pointer waiter old bits result returned
    before after (frame : Assertion),
  clients (flag_task_rdy_source_client actor pointer bits result) -> actor <> Some observer ->
  UCOS2_state_inv sg entry -> flag_task_rdy_domain sg entry pointer waiter old bits ->
  (flag_task_rdy_fields_pre sg entry pointer waiter old bits **
    (UCOS2_raw_rep_missing_task_storage_sched_flag sg entry **
     store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
       entry.(TskState).(parkedTaskStacks) ** frame)) before ->
  flag_pend_sched_fields_task_rdy_call sg pointer bits result returned before after ->
  exists checkpoint schedule,
    flag_task_rdy sg entry pointer bits result = Some (schedule, checkpoint) /\
    returned = (if schedule then 1 else 0) /\
    tmr_task_source_call_receipt external
      (flag_task_rdy_source_client actor pointer bits result) sg entry checkpoint /\
    (exists trace : kernel_resumption_task_source_trace external port clients sg observer event_observer
        origin entry false origin checkpoint,
      sem_pend_resumption_source_calls external port clients sg observer event_observer
        origin entry false origin checkpoint trace) /\
    (UCOS2_fields_inv sg checkpoint ** flag_node_fields_return_loan sg.(osKernelConfig) waiter **
      store_parked_continuations (kernel_saved_continuation_entry abi checkpoint.(TskState) local)
        checkpoint.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi local clients sg observer event_observer origin actor entry pointer waiter old bits
    result returned before after frame Hmember Hforeign Hvalid Hdomain Hpre Hcall.
  pose proof (Hcall entry waiter old
    (UCOS2_raw_rep_missing_task_storage_sched_flag sg entry **
     store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
       entry.(TskState).(parkedTaskStacks) ** frame) Hpre) as Hpost.
  assert (Hmerge : flag_task_rdy_fields_post sg entry pointer waiter bits result returned **
      (UCOS2_raw_rep_missing_task_storage_sched_flag sg entry **
       store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
         entry.(TskState).(parkedTaskStacks) ** frame) |--
    EX checkpoint schedule,
      coq_prop (flag_task_rdy sg entry pointer bits result = Some (schedule, checkpoint) /\
        returned = (if schedule then 1 else 0)) &&
      (UCOS2_fields_inv sg checkpoint ** flag_node_fields_return_loan sg.(osKernelConfig) waiter **
       store_parked_continuations (kernel_saved_continuation_entry abi checkpoint.(TskState) local)
         checkpoint.(TskState).(parkedTaskStacks) ** frame)).
  { sep_apply_l_atomic (flag_wake_fields_returns_node_with_continuation_map external platform port abi
      sg entry pointer waiter old bits result returned local Hvalid Hdomain).
    Intros checkpoint schedule; Exists checkpoint schedule; entailer!. }
  destruct (Hmerge after Hpost) as [checkpoint [schedule [[Hstep Hresult] Howned]]].
  assert (Hreceipt : tmr_task_source_call_receipt external
    (flag_task_rdy_source_client actor pointer bits result) sg entry checkpoint).
  { eapply sem_pend_source_client_call_receipt with
      (source := TmrTaskSourceScheduler external _ (TmrTaskSchedulerFlagReady external actor pointer bits result)).
    - constructor.
    - exists schedule; exact Hstep. }
  assert (Hwake : WakeComponent.kernel_wake_c_source sg entry checkpoint)
    by (eapply WakeComponent.KernelWakeCFlagSource; exact Hstep).
  destruct (sem_pend_wake_source_current_timer_frame sg entry checkpoint Hwake) as [Hcurrent Htimer].
  exists checkpoint, schedule; split; [exact Hstep|]. split; [exact Hresult|].
  split; [exact Hreceipt|]. split; [|exact Howned].
  eapply sem_pend_framed_source_step_calls with (action := flag_task_rdy_source_client actor pointer bits result).
  - exact Hmember.
  - exact Hforeign.
  - intros; discriminate.
  - exists schedule; exact Hstep.
  - exact Hcurrent.
  - exact Htimer.
  - exact Hreceipt.
Qed.

(** Append the real fields module packet to the supplied annotated prefix.
    The complete previous stop bit survives; only this actual Post edge is
    non-stopping. Its successor is the existing fields world on after. *)
Lemma sem_pend_sem_post_fields_execution_append :
  forall external platform port (abi : Armv7aContinuationABI external platform port) local
    clients sg observer event_observer first initial stopped origin entry
    (prefix : kernel_resumption_task_source_trace external port clients sg observer event_observer
      first initial stopped origin entry),
  sem_pend_resumption_source_calls external port clients sg observer event_observer
    first initial stopped origin entry prefix ->
  forall actor event node returned before after (frame : Assertion),
  clients (sem_pend_post_source_client actor event) -> actor <> observer ->
  sem_post_lookup entry event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry node <> 0 -> event_object_layout_prop sg event ->
  (kernel_client_continuation_fields_world abi local sg entry ** frame) before ->
  sem_post_waiter_execution sg (event_addr sg event) returned before after ->
  exists selected old,
    let wake := event_wake_state sg entry event node selected old PendSem 0 PendOK in
    (exists trace : kernel_resumption_task_source_trace external port clients sg observer event_observer
        first initial stopped origin wake,
      sem_pend_resumption_source_calls external port clients sg observer event_observer
        first initial stopped origin wake trace) /\
    (kernel_client_continuation_fields_world abi local sg wake ** frame) after.
Proof.
  intros external platform port abi local clients sg observer event_observer first initial stopped origin entry
    prefix Hprefix actor event node returned before after frame Hmember Hforeign Hlookup Htype Hgroup Hlayout Hpre Hactual.
  destruct (sem_pend_sem_post_fields_execution_source_receipt external platform port abi local clients sg
    observer event_observer origin actor entry event node returned before after frame Hmember Hforeign
    Hlookup Htype Hgroup Hlayout Hpre Hactual)
    as [selected [old [Hentry [Hhelper [Hreceipt [[suffix Hsuffix] Howned]]]]]].
  exists selected, old; split; [|exact Howned].
  rewrite <- (Bool.orb_false_r stopped).
  exact (sem_pend_resumption_source_calls_append external port clients sg observer event_observer
    first initial stopped origin entry prefix Hprefix false origin
    (event_wake_state sg entry event node selected old PendSem 0 PendOK) suffix Hsuffix).
Qed.
