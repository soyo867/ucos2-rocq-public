Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.flag Ucos2Verify.lib.sched Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_source_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_event_ready_source_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_ready_endpoint_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_abort_source_api_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_del_source_api_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_wait_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_post_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef SemPendEventReadySource ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The endpoint association is obtained from the concrete call's existing
    waiter update proof. No effect history is exported to the C caller. *)
Lemma sem_pend_wait_continuation_timeout_pointer : forall eid generation node,
  sem_pend_wait_continuation eid generation node ->
  node.(statPend) = PendTimeout -> node.(eventPtr) = Some eid.
Proof.
  intros eid generation node [_ [_ [_ [[Hptr _]|[_ [_ Hresult]]]]]] Htimeout;
    [exact Hptr|contradiction].
Qed.

(** This is a single actual classified call, including all fourteen old
    classes. Retiring an invocation is not asserted to be normal return.
    The selected program's own Prepare/Recycle constructors are separate. *)
Lemma sem_pend_call_source_waiter : forall external action sg before after tid old eid generation,
  tmr_task_source_call_receipt external action sg before after ->
  sem_pend_source_state_facts sg before ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  exists current, after.(TskState).(inUsedTaskStates) tid = Some current /\
    sem_pend_wait_continuation eid generation current /\
    (current.(statPend) = PendTimeout -> current.(eventPtr) = Some eid).
Proof.
  intros external action sg before after tid old eid generation Hcall Hfacts Hold Hcont.
  destruct (sem_pend_source_call_local_projection external action sg before after tid old eid generation
    Hcall Hfacts Hold Hcont) as [current [Hcurrent Heffect]].
  pose proof (sem_pend_wait_trace_preserves_continuation eid generation old current Heffect Hcont) as Hnext.
  exists current; split; [exact Hcurrent|]. split; [exact Hnext|].
  eapply sem_pend_wait_continuation_timeout_pointer; exact Hnext.
Qed.

Lemma sem_pend_source_client_step_waiter :
  forall external action sg before after tid old eid generation
    (source : tmr_task_source_client external action),
  sem_pend_source_client_call_input external action sg before source ->
  kernel_client_step action sg before after ->
  sem_pend_source_state_facts sg before ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  kernel_client_step action sg before after /\
  exists current, after.(TskState).(inUsedTaskStates) tid = Some current /\
    sem_pend_wait_continuation eid generation current /\
    (current.(statPend) = PendTimeout -> current.(eventPtr) = Some eid).
Proof.
  intros external action sg before after tid old eid generation source Hinput Hstep Hfacts Hold Hcont.
  split; [exact Hstep|].
  eapply sem_pend_call_source_waiter; [|exact Hfacts|exact Hold|exact Hcont].
  eapply sem_pend_source_client_call_receipt; eassumption.
Qed.

(** These three literal Wake effects do not write the control counters.
    No such statement is made about Profile IntEnter/IntExit, or about an
    arbitrary registry action. Balanced control belongs to a completed call. *)
Lemma sem_pend_wake_source_control : forall sg entry returned,
  WakeComponent.kernel_wake_c_source sg entry returned ->
  kernel_call_control_rely sg entry returned.
Proof.
  intros sg entry returned Hsource; destruct Hsource; unfold kernel_call_control_rely.
  - destruct (flag_task_rdy_result _ _ _ _ _ _ _ H)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    split; reflexivity.
  - unfold event_task_rdy in H.
    destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
    destruct (entry.(TskState).(prioTbl) (event_wait_priority entry.(TskState) event))
      as [| |slot]; try discriminate.
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|]; [|discriminate].
    injection H as Hpriority Hreturned; subst returned.
    cbn [event_wake_state replace_SchedS SchedState IntrState].
    unfold sched_wake_by_status; destruct task_status_is_suspended; split; reflexivity.
  - unfold tick_task_step, sched_wake_by_status; cbn zeta;
      repeat match goal with |- context [if ?c then _ else _] => destruct c end;
      split; reflexivity.
Qed.

(** Consume the already verified helper's same pre/post. The selected
    Event, TCB, kind and result are the call's actual parameters. The raw
    post and its frame are retained, including at a Prepared local cut. *)
Lemma sem_pend_event_ready_c_post_waiter :
  forall (external : OsSchedExternalResources) actor sg entry event node selected old kind message result returned frame before after
    tid previous eid generation,
  entry.(EventState).(inUsedEventStates) event = Some node ->
  event_type_to_pend_type node.(eventType) = Some kind -> result <> PendTimeout ->
  sem_pend_source_state_facts sg entry ->
  entry.(TskState).(inUsedTaskStates) tid = Some previous ->
  sem_pend_wait_continuation eid generation previous ->
  (WakeComponent.event_ready_c_input sg entry event node selected old kind result ** frame) before ->
  (WakeComponent.event_ready_c_output sg entry event node selected old kind message result returned ** frame) after ->
  let wake := event_wake_state sg entry event node selected old kind message result in
  WakeComponent.kernel_wake_c_segment sg entry before
    (WakeComponent.event_ready_c_input sg entry event node selected old kind result ** frame)
    wake after
    (WakeComponent.event_ready_c_output sg entry event node selected old kind message result returned ** frame) /\
  kernel_client_step (event_task_rdy_source_client actor event kind message result) sg entry wake /\
  kernel_call_control_rely sg entry wake /\
  (exists current, wake.(TskState).(inUsedTaskStates) tid = Some current /\
    sem_pend_wait_continuation eid generation current /\
    (current.(statPend) = PendTimeout -> current.(eventPtr) = Some eid)) /\
  (WakeComponent.event_ready_c_output sg entry event node selected old kind message result returned ** frame) after.
Proof.
  intros external actor sg entry event node selected old kind message result returned frame before after
    tid previous eid generation Hnode Hkind Hresult Hfacts Hprevious Hcont Hpre Hpost wake.
  destruct (tmr_task_event_ready_c_post_receipt external actor sg entry event node selected old kind
    message result returned frame before after Hnode Hkind Hresult Hpre Hpost) as [Hsegment Hcall].
  fold wake in Hsegment, Hcall.
  split; [exact Hsegment|].
  split; [exact (tmr_task_source_call_receipt_step _ _ _ _ _ Hcall)|].
  split.
  - eapply sem_pend_wake_source_control.
    exact (WakeComponent.kernel_wake_c_segment_source _ _ _ _ _ _ _ Hsegment).
  - split; [|exact Hpost]. eapply sem_pend_call_source_waiter; eassumption.
Qed.

(** The actual Abort loop retains its CURRENT Event lookup and nonempty
    queue. No entry-snapshot head is reused after an earlier iteration. *)
Lemma sem_pend_abort_loop_waiter :
  forall (external : OsSchedExternalResources) actor environment critical sg caller active mask saved before acquired event
    observed initial state node processed count priority after tid old eid generation,
  sem_pend_abort_source_loop_facts environment critical sg caller active mask saved before acquired
    event observed initial state node processed count ->
  q_post_group state node <> 0 ->
  event_task_rdy sg state event PendSem 0 PendAbort = Some (priority, after) ->
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  kernel_client_step (event_task_rdy_source_client actor event PendSem 0 PendAbort) sg state after /\
  kernel_call_control_rely sg state after /\
  exists current, after.(TskState).(inUsedTaskStates) tid = Some current /\
    sem_pend_wait_continuation eid generation current /\
    (current.(statPend) = PendTimeout -> current.(eventPtr) = Some eid).
Proof.
  intros external actor environment critical sg caller active mask saved before acquired event
    observed initial state node processed count priority after tid old eid generation Hloop Hgroup Hcall Hold Hcont.
  pose proof (tmr_task_sem_abort_loop_call_receipt external actor environment critical sg caller active mask
    saved before acquired event observed initial state node processed count priority after Hloop Hgroup Hcall)
    as Hreceipt.
  split; [exact (tmr_task_source_call_receipt_step _ _ _ _ _ Hreceipt)|]. split.
  - eapply sem_pend_wake_source_control; econstructor 2; exact Hcall.
  - eapply sem_pend_call_source_waiter; [exact Hreceipt| |exact Hold|exact Hcont].
    apply sem_pend_source_state_facts_from_valid.
    destruct Hloop as [_ [_ [_ [_ [Hvalid _]]]]]; exact Hvalid.
Qed.

(** Delete's wake loop still owns the Event. Its later unlink/recycle
    operation is not silently replaced with this one wake-call result. *)
Lemma sem_pend_delete_loop_waiter :
  forall (external : OsSchedExternalResources) actor environment critical sg caller active mask saved before acquired event
    observed initial state node waiting priority after tid old eid generation,
  sem_del_source_api_loop_facts environment critical sg caller active mask saved before acquired
    event observed initial state node waiting ->
  q_post_group state node <> 0 ->
  event_task_rdy sg state event PendSem 0 PendAbort = Some (priority, after) ->
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  kernel_client_step (event_task_rdy_source_client actor event PendSem 0 PendAbort) sg state after /\
  kernel_call_control_rely sg state after /\
  exists current, after.(TskState).(inUsedTaskStates) tid = Some current /\
    sem_pend_wait_continuation eid generation current /\
    (current.(statPend) = PendTimeout -> current.(eventPtr) = Some eid).
Proof.
  intros external actor environment critical sg caller active mask saved before acquired event
    observed initial state node waiting priority after tid old eid generation Hloop Hgroup Hcall Hold Hcont.
  pose proof (tmr_task_sem_delete_loop_call_receipt external actor environment critical sg caller active mask
    saved before acquired event observed initial state node waiting priority after Hloop Hgroup Hcall)
    as Hreceipt.
  split; [exact (tmr_task_source_call_receipt_step _ _ _ _ _ Hreceipt)|]. split.
  - eapply sem_pend_wake_source_control; econstructor 2; exact Hcall.
  - eapply sem_pend_call_source_waiter; [exact Hreceipt| |exact Hold|exact Hcont].
    apply sem_pend_source_state_facts_from_valid.
    destruct Hloop as [_ [_ [_ [_ [_ [_ [_ [_ [_ Hvalid]]]]]]]]]; exact Hvalid.
Qed.

(** Tick's actual body merge supplies its own full owner. Expiration keeps
    the old Event pointer; this producer does not convert that owner to a
    fields owner or ask Tick to pretend it never returns PendTimeout. *)
Lemma sem_pend_tick_c_post_waiter :
  forall (external : OsSchedExternalResources) sg entry slot old frame before after tid previous eid generation,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  time_tick_lookup entry slot old ->
  entry.(TskState).(inUsedTaskStates) tid = Some previous ->
  sem_pend_wait_continuation eid generation previous ->
  (UCOS2_inv sg entry ** frame) before ->
  ((time_tick_body_cells sg slot (tick_task_update old)
       (time_tick_ready_group (tick_task_step sg slot old entry))
       (time_tick_ready_rows (tick_task_step sg slot old entry)) **
     time_tick_body_residual sg entry slot old) ** frame) after ->
  let next := tick_task_step sg slot old entry in
  WakeComponent.kernel_wake_c_segment sg entry before (UCOS2_inv sg entry ** frame)
    next after (UCOS2_inv sg next ** frame) /\
  kernel_client_step (time_tick_task_source_client slot old) sg entry next /\
  kernel_call_control_rely sg entry next /\
  (exists current, next.(TskState).(inUsedTaskStates) tid = Some current /\
    sem_pend_wait_continuation eid generation current /\
    (current.(statPend) = PendTimeout -> current.(eventPtr) = Some eid)) /\
  (UCOS2_inv sg next ** frame) after.
Proof.
  intros external sg entry slot old frame before after tid previous eid generation
    Hmulti Hlookup Hprevious Hcont Hpre Hpost next.
  pose proof (WakeComponent.time_tick_body_c_post_segment sg entry slot old frame before after
    Hmulti Hlookup Hpre Hpost) as Hsegment; fold next in Hsegment.
  assert (Hstep : kernel_client_step (time_tick_task_source_client slot old) sg entry next).
  { split; [exact Hlookup|reflexivity]. }
  assert (Hvalid : UCOS2_state_inv sg entry).
  { pose proof Hpre as [owned [rest [Hjoin [[Hvalid Hbody] Hframe]]]]; exact Hvalid. }
  split; [exact Hsegment|]. split; [exact Hstep|]. split.
  - eapply sem_pend_wake_source_control.
    exact (WakeComponent.kernel_wake_c_segment_source _ _ _ _ _ _ _ Hsegment).
  - split; [|exact (proj2 (WakeComponent.kernel_wake_c_segment_resources _ _ _ _ _ _ _ Hsegment))].
    eapply sem_pend_call_source_waiter with (external := external); [| |exact Hprevious|exact Hcont].
    + apply TmrTaskCallTickTask; exact Hstep.
    + apply sem_pend_source_state_facts_from_valid; exact Hvalid.
Qed.

(** This is the actual finite SemPost fields producer, with its real active
    key and local continuation map. Split, literal writes and merge refer
    to one selected TCB and the same before/after heaps. No actor/observer
    inequality is needed by these physical or endpoint deductions. *)
Lemma sem_pend_sem_post_fields_execution_waiter :
  forall external platform port (abi : Armv7aContinuationABI external platform port) local active
    sg actor entry event node returned before after (frame : Assertion) tid previous eid generation,
  sem_post_lookup entry event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry node <> 0 -> event_object_layout_prop sg event ->
  entry.(TskState).(inUsedTaskStates) tid = Some previous ->
  sem_pend_wait_continuation eid generation previous ->
  (kernel_continuation_inv abi kernel_program_fields_inv local sg active entry ** frame) before ->
  sem_post_waiter_execution sg (event_addr sg event) returned before after ->
  exists selected old,
    let wake := event_wake_state sg entry event node selected old PendSem 0 PendOK in
    let residual := sem_pend_event_ready_fields_frame sg entry event selected **
      store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
        entry.(TskState).(parkedTaskStacks) ** frame in
    event_task_rdy_entry sg entry.(TskState) event node selected old /\
    WakeComponent.kernel_wake_c_segment sg entry before
      (WakeComponent.event_ready_c_input sg entry event node selected old PendSem PendOK ** residual)
      wake after
      (WakeComponent.event_ready_c_output sg entry event node selected old PendSem 0 PendOK returned ** residual) /\
    kernel_client_step (sem_pend_post_source_client actor event) sg entry wake /\
    sem_post_wake_result sg event entry wake returned /\
    kernel_call_control_rely sg entry wake /\
    (exists current, wake.(TskState).(inUsedTaskStates) tid = Some current /\
      sem_pend_wait_continuation eid generation current /\
      (current.(statPend) = PendTimeout -> current.(eventPtr) = Some eid)) /\
    (kernel_continuation_inv abi kernel_program_fields_inv local sg active wake ** frame) after.
Proof.
  intros external platform port abi local active sg actor entry event node returned before after frame
    tid previous eid generation Hlookup Htype Hgroup Hlayout Hprevious Hcont Hpre Hactual.
  set (stacks := store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
    entry.(TskState).(parkedTaskStacks)).
  assert (Hopen : kernel_continuation_inv abi kernel_program_fields_inv local sg active entry ** frame |--
    coq_prop (UCOS2_state_inv sg entry /\ task_stack_live_coverage entry.(TskState) active) &&
    (kernel_program_fields_inv sg entry ** stacks ** frame)).
  { unfold kernel_continuation_inv, kernel_program_fields_inv, stacks; entailer!. }
  destruct (Hopen before Hpre) as [[Hvalid Hcoverage] Hworld].
  assert (Hsplit : kernel_program_fields_inv sg entry ** stacks ** frame |--
    EX selected old, coq_prop (event_task_rdy_entry sg entry.(TskState) event node selected old) &&
    (WakeComponent.event_ready_c_input sg entry event node selected old PendSem PendOK **
      (sem_pend_event_ready_fields_frame sg entry event selected ** stacks ** frame))).
  { rewrite kernel_program_fields_inv_split_unmap.
    sep_apply_l_atomic (sem_pend_event_ready_fields_split sg entry event node Hvalid Hlookup Htype Hgroup Hlayout).
    Intros selected old; Exists selected old; entailer!. }
  destruct (Hsplit before Hworld) as [selected [old [Hentry Howned]]].
  set (residual := sem_pend_event_ready_fields_frame sg entry event selected ** stacks ** frame).
  pose proof (sem_post_waiter_source_post sg entry.(TskState) event node selected old
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) returned before after residual
    Howned Hactual) as Hpost.
  set (wake := event_wake_state sg entry event node selected old PendSem 0 PendOK).
  assert (Hkind : event_type_to_pend_type node.(eventType) = Some PendSem) by (rewrite Htype; reflexivity).
  destruct (sem_pend_event_ready_c_post_waiter external (Some actor) sg entry event node selected old
    PendSem 0 PendOK returned residual before after tid previous eid generation Hlookup Hkind
    ltac:(discriminate) (sem_pend_source_state_facts_from_valid sg entry Hvalid)
    Hprevious Hcont Howned Hpost) as [Hsegment [Hrawstep [Hcontrol [Hwaiter Hrawpost]]]].
  cbn zeta in Hsegment, Hrawstep, Hcontrol, Hwaiter, Hrawpost; fold wake in Hsegment, Hrawstep, Hcontrol, Hwaiter.
  assert (Hmerge : WakeComponent.event_ready_c_output sg entry event node selected old PendSem 0 PendOK returned **
      residual |-- coq_prop (sem_post_wake_result sg event entry wake returned) &&
      (kernel_continuation_inv abi kernel_program_fields_inv local sg active wake ** frame)).
  { pose proof (sem_pend_event_ready_fields_merge_continuations external platform port abi sg entry event node
      selected old returned local active Hvalid Hlookup Htype Hentry Hcoverage) as Hjoin.
    cbn zeta in Hjoin; unfold residual, stacks, wake; sepcon_assoc_change; sep_apply_l_atomic Hjoin.
    unfold kernel_continuation_inv; entailer!. }
  destruct (Hmerge after Hpost) as [Hwake Hresources].
  assert (Hstep : kernel_client_step (sem_pend_post_source_client actor event) sg entry wake).
  { exists (OS_ERR_NONE, true); eapply sem_post_wake_result_critical; eassumption. }
  exists selected, old; fold wake; fold stacks; fold residual.
  split; [exact Hentry|]. split; [exact Hsegment|]. split; [exact Hstep|].
  split; [exact Hwake|]. split; [exact Hcontrol|]. split; assumption.
Qed.

(** At a real return, the existing TaskSource selects the current node.
    The endpoint proof above supplies only the missing Timeout association;
    readiness and stable validity remain observations of this actual return. *)
Lemma sem_pend_call_source_returned_ready_waiter :
  forall external action sg before after original returned old eid,
  tmr_task_source_call_receipt external action sg before after ->
  sem_pend_source_state_facts sg before ->
  before.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some old ->
  sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) old ->
  UCOS2_state_inv sg after -> kernel_call_task_source returned after ->
  kernel_stack_call_same_call returned original ->
  In original.(os_sched_call_stack).(stackLeaseSlot) after.(SchedState).(readyList) ->
  exists node,
    sem_pend_resume_entry sg after eid original.(os_sched_call_stack).(stackLeaseSlot) node /\
    node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) /\
    sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) node.
Proof.
  intros external action sg before after original returned old eid Hcall Hfacts Hold Hcont
    Hvalid Hsource Hsame Hready.
  destruct (sem_pend_call_source_waiter external action sg before after
    original.(os_sched_call_stack).(stackLeaseSlot) old eid original.(os_sched_call_stack).(stackLeaseGeneration)
    Hcall Hfacts Hold Hcont) as [current [Hcurrent [Hnext Htimeout]]].
  eapply sem_pend_returned_ready_waiter; [exact Hvalid|exact Hsource|exact Hsame|exact Hready|].
  intros node Hnode; assert (node = current) by congruence; subst node; exact Htimeout.
Qed.
