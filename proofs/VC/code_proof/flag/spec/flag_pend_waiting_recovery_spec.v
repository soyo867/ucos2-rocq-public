Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.flag_execution.
Require Import Ucos2Verify.lib.flag_node_fields.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations FlagPendSchedulerResources.
Import PrimitiveComponent PendPhaseCandidate.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagWaitingRecovery.

(** This is the observation and node owner produced at the CURRENT source
    cut.  It is not the old active assertion transported unchanged.  While
    linked, the node fields remain in the public Flag representation; after
    Post/Del, the actual helper loan supplies those fields.  Padding and all
    other private bytes remain in the separate, unchanged [frame]. *)
Definition flag_pend_waiting_receipt sg original node call state : Assertion :=
  coq_prop (flag_pend_wait_outcome original node state) &&
  flag_active_waiting sg original node call state.

Lemma flag_pend_wait_active_receipt : forall sg original node call state,
  flag_pend_wait_active sg original node call state |--
  flag_pend_waiting_receipt sg original node call state.
Proof.
  intros; unfold flag_pend_wait_active, flag_pend_waiting_receipt; entailer!.
Qed.

Lemma flag_pend_waiting_receipt_active :
  forall sg original node call returned current (frame : Assertion),
  task_tcb_init_stack_same_call returned call ->
  task_idle_ready sg current.(TskState) ->
  flag_pend_non_idle_at sg original current ->
  flag_pend_waiting_receipt sg original node call current ** frame |--
  flag_pend_wait_active sg original node returned current ** frame.
Proof.
  intros sg original node call returned current frame Hsame Hidle Hnonidle.
  unfold flag_pend_waiting_receipt; Intros.
  sep_apply_l_atomic (proj1 (flag_active_waiting_call_equiv sg original node call returned current Hsame)).
  unfold flag_pend_wait_active; entailer!.
Qed.

(** The endpoint observations here are the already produced observations of
    this same C return.  They transport Idle/non-Idle; no waiting outcome or
    node ownership is obtained from that endpoint packet. *)
Lemma flag_pend_waiting_receipt_endpoint_active :
  forall environment sg original node call returned entry current (frame : Assertion),
  kernel_call_task_source original entry ->
  task_tcb_init_stack_same_call returned call ->
  task_tcb_init_stack_same_call returned original ->
  flag_pend_call_endpoint_observations environment sg
    (FlagPendTaskCaller original) original entry returned current ->
  task_idle_ready sg entry.(TskState) ->
  flag_pend_non_idle_at sg original entry ->
  flag_pend_waiting_receipt sg original node call current ** frame |--
  flag_pend_wait_active sg original node returned current ** frame.
Proof.
  intros environment sg original node call returned entry current frame Hsource Hcall
    [_ [_ Hstack]] Hendpoint Hidle Hnonidle.
  destruct Hendpoint as [Hready [Hidle_after [Hnonidle_after Hrest]]].
  apply flag_pend_waiting_receipt_active;
    [exact Hcall|exact (Hidle_after (conj Hsource Hidle))|].
  specialize (Hnonidle_after (conj Hsource Hnonidle)).
  unfold flag_pend_non_idle_at in Hnonidle_after; rewrite Hstack in Hnonidle_after.
  exact Hnonidle_after.
Qed.

(** The initial receipt is a projection of OS_FlagBlock's actual field post.
    The output still names the same block result, node and private frame. *)
Lemma flag_block_fields_post_waiting_receipt :
  forall sg state original call waiter old group image timeout (frame : Assertion),
  flag_active_fresh_registration original call state ->
  task_stack_key original.(os_sched_call_stack) = (waiter.(flagTask), waiter.(flagTaskGeneration)) ->
  task_idle_ready sg state.(TskState) ->
  flag_pend_non_idle_at sg original state ->
  UCOS2_state_inv sg state ->
  valid_flag_state sg state.(FlagState) ->
  flag_block_call_protocol sg state waiter old group image timeout ->
  flag_block_call_fields_post sg state waiter old timeout ** frame |--
  EX flags,
    coq_prop (flag_block_node sg state.(FlagState) waiter (flag_block_call_tcb sg waiter) = Some flags /\
      flag_block_spec.flag_block sg state waiter timeout =
        Some (flag_execution.flag_block_state state waiter flags old timeout)) &&
    (UCOS2_fields_inv sg (flag_execution.flag_block_state state waiter flags old timeout) **
     flag_pend_waiting_receipt sg original waiter.(flagNodeAddr) call
       (flag_execution.flag_block_state state waiter flags old timeout) ** frame).
Proof.
  intros sg state original call waiter old group image timeout frame
    Hfresh Hkey Hidle Hnonidle Hstate Hvalid Hprotocol.
  sep_apply_l_atomic (flag_pend_block_fields_wait_outcome sg state original call waiter old group image
    timeout Hfresh Hkey Hidle Hnonidle Hstate Hvalid Hprotocol).
  Intros flags; Exists flags.
  unfold flag_pend_wait_active, flag_pend_waiting_receipt; entailer!; tauto.
Qed.

(** Both actual wake results are retained: Post/PendOK and Del/PendAbort.
    In particular, a false scheduler request does not lose the receipt. *)
Lemma flag_task_rdy_fields_post_waiting_receipt :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg state original call node waiter old bits result returned local (frame : Assertion),
  UCOS2_state_inv sg state ->
  flag_task_rdy_domain sg state node waiter old bits ->
  flag_active_waiting_registration original node call state ->
  waiter.(flagNodeAddr) = node ->
  (result = PendOK \/ result = PendAbort) ->
  (flag_task_rdy_fields_post sg state node waiter bits result returned **
   UCOS2_raw_rep_missing_task_storage_sched_flag sg state **
   store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
     state.(TskState).(parkedTaskStacks)) ** frame |--
  EX post schedule,
    coq_prop (flag_task_rdy sg state node bits result = Some (schedule, post) /\
      returned = (if schedule then 1 else 0) /\ post.(FlagState).(flagWaitNodes) node = None) &&
    (UCOS2_fields_inv sg post ** flag_pend_waiting_receipt sg original node call post **
     store_parked_continuations (kernel_saved_continuation_entry abi post.(TskState) local)
       post.(TskState).(parkedTaskStacks) ** frame).
Proof.
  intros external platform port abi sg state original call node waiter old bits result returned local frame
    Hvalid Hdomain Hregistration Hnode Hresult.
  sep_apply_l_atomic (flag_active_task_rdy_fields_resources external platform port abi sg state original call
    node waiter old bits result returned local Hvalid Hdomain Hregistration Hnode).
  Intros post schedule.
  assert (Hstep : flag_task_rdy sg state node bits result = Some (schedule, post)) by tauto.
  pose proof (flag_pend_task_rdy_wait_outcome sg state original call node bits result schedule post
    Hregistration Hresult Hstep) as Houtcome.
  Exists post schedule; unfold flag_pend_waiting_receipt; entailer!; tauto.
Qed.

Lemma flag_pend_waiting_receipt_parked_map :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg original node call state local,
  flag_pend_wait_outcome original node state ->
  store_parked_continuations
    (kernel_saved_continuation_entry abi state.(TskState)
      (flag_continuation_local_node original.(os_sched_call_stack)
        (flag_active_waiting sg original node call state) local)) state.(TskState).(parkedTaskStacks) |--
  store_parked_continuations
    (kernel_saved_continuation_entry abi state.(TskState)
      (flag_continuation_local_node original.(os_sched_call_stack)
        (flag_pend_waiting_receipt sg original node call state) local)) state.(TskState).(parkedTaskStacks).
Proof.
  intros external platform port abi sg original node call state local Houtcome.
  unfold store_parked_continuations; apply TaskFieldStorage.store_map_mono.
  intros key payload Hlookup; unfold kernel_saved_continuation_entry; Intros descriptor.
  Exists descriptor; unfold flag_continuation_local_node.
  destruct task_stack_key_eq_dec; unfold flag_pend_waiting_receipt; entailer!.
Qed.

(** This is the actual Post/Del loop hand-off: OS_FlagTaskRdy's call edge,
    then the original Next load/assignment, and the resulting parked node
    loan.  Neither edge nor its intermediate heap is reconstructed from
    endpoint equality. *)
Lemma flag_task_rdy_next_publish_waiting_receipt : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state original call node waiter old bits result returned
  local fragments pnode (frame : Assertion) before middle after observed,
  UCOS2_state_inv sg state -> flag_task_rdy_domain sg state node waiter old bits ->
  flag_active_waiting_registration original node call state -> waiter.(flagNodeAddr) = node ->
  (result = PendOK \/ result = PendAbort) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  flag_pend_sched_fields_task_rdy_call sg node bits result returned before middle ->
  flag_source_next_assignment pnode node observed middle after ->
  (flag_task_rdy_fields_pre sg state node waiter old bits **
    (UCOS2_raw_rep_missing_task_storage_sched_flag sg state **
     store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
       state.(TskState).(parkedTaskStacks) ** (pnode # Ptr |-> node ** frame))) before ->
  exists post schedule,
    flag_task_rdy sg state node bits result = Some (schedule, post) /\
    returned = (if schedule then 1 else 0) /\
    observed = waiter.(flagWaitImage).(flagNodeNext) /\
    post.(FlagState).(flagWaitNodes) node = None /\
    (pnode # Ptr |-> observed ** UCOS2_fields_inv sg post **
     store_parked_continuations
       (kernel_saved_continuation_entry abi post.(TskState)
         (flag_continuation_local_node original.(os_sched_call_stack)
           (flag_pend_waiting_receipt sg original node call post) local))
       post.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi sg state original call node waiter old bits result returned local fragments
    pnode frame before middle after observed Hvalid Hdomain Hregistration Hnode Hresult Hentry Hcall Hnext Hpre.
  destruct (flag_active_task_rdy_next_publish external platform port abi sg state original call node waiter old
    bits result returned local fragments pnode frame before middle after observed Hvalid Hdomain Hregistration
    Hnode Hentry Hcall Hnext Hpre) as [post [schedule [Hstep [Hreturned [Hobserved [Hnone Hresources]]]]]].
  pose proof (flag_pend_task_rdy_wait_outcome sg state original call node bits result schedule post
    Hregistration Hresult Hstep) as Houtcome.
  exists post, schedule; split; [exact Hstep|]; split; [exact Hreturned|];
    split; [exact Hobserved|]; split; [exact Hnone|].
  match type of Hresources with ?P after =>
    match goal with |- ?Q after => assert (Htransport : P |-- Q) by
      (sep_apply_l_atomic (flag_pend_waiting_receipt_parked_map external platform port abi sg original node call
        post local Houtcome); entailer!) end end.
  exact (Htransport after Hresources).
Qed.

(** Tick only changes the timeout/status fields of this registered waiter.
    Its flag node remains linked, including the one-tick timeout branch. *)
Lemma flag_active_waiting_registration_tick : forall sg original node call state old,
  state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some old ->
  flag_active_waiting_registration original node call state ->
  flag_active_waiting_registration original node call
    (tick_task_step sg original.(os_sched_call_stack).(stackLeaseSlot) old state).
Proof.
  intros sg original node call state old Hold [observed [Htask Hnode]].
  assert (observed = old) by (destruct Htask as [_ [_ [Hlookup _]]]; congruence); subst observed.
  assert (Hgeneration : (tick_task_update old).(taskGeneration) = old.(taskGeneration))
    by (unfold tick_task_update; destruct (Z.eqb old.(dly) 0); reflexivity).
  assert (Hclear : flag_active_event_clear (tick_task_update old)).
  { destruct Htask as [_ [_ [_ [_ [_ Hclear]]]]].
    unfold flag_active_event_clear in *; unfold tick_task_update;
      destruct (Z.eqb old.(dly) 0); exact Hclear. }
  assert (Hflags : (tick_task_step sg original.(os_sched_call_stack).(stackLeaseSlot) old state).(FlagState) =
    state.(FlagState)).
  { unfold tick_task_step; destruct (Z.eqb old.(dly) 0); [reflexivity|].
    destruct (Z.eqb (tick_task_update old).(dly) 0); reflexivity. }
  exists (tick_task_update old); split.
  - pose proof (flag_active_task_fields_update original call state old (tick_task_update old)
      Htask Hgeneration Hclear) as Hupdated.
    unfold flag_active_task_fields in *; rewrite tick_task_step_task_state_eq by exact Hold.
    exact Hupdated.
  - rewrite Hflags; unfold tick_task_update; destruct (Z.eqb old.(dly) 0); exact Hnode.
Qed.

Lemma flag_pend_waiting_receipt_tick : forall sg original node call state old,
  state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some old ->
  flag_pend_waiting_receipt sg original node call state |--
  flag_pend_waiting_receipt sg original node call
    (tick_task_step sg original.(os_sched_call_stack).(stackLeaseSlot) old state).
Proof.
  intros sg original node call state old Hold heap [Houtcome [Hregistration Hnode]].
  split.
  - eapply flag_pend_tick_wait_outcome; eassumption.
  - split; [eapply flag_active_waiting_registration_tick; eassumption|].
    unfold flag_pend_sched_node_fields_rep in *; unfold tick_task_step;
      destruct (Z.eqb old.(dly) 0); [exact Hnode|].
    destruct (Z.eqb (tick_task_update old).(dly) 0); exact Hnode.
Qed.

(** Unlike a future receipt assumption, this consumes the exact Tick body
    cells and residual produced by the already proved C stores.  Only the
    private node-field owner (emp while linked) is part of the fixed frame. *)
Lemma time_tick_body_waiting_receipt : forall sg original node call state old
  (frame : Assertion) before after,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  time_tick_lookup state original.(os_sched_call_stack).(stackLeaseSlot) old ->
  flag_active_waiting_registration original node call state ->
  flag_pend_wait_outcome original node state ->
  (UCOS2_inv sg state ** (flag_pend_sched_node_fields_rep sg node state ** frame)) before ->
  ((time_tick_body_cells sg original.(os_sched_call_stack).(stackLeaseSlot) (tick_task_update old)
      (time_tick_ready_group (tick_task_step sg original.(os_sched_call_stack).(stackLeaseSlot) old state))
      (time_tick_ready_rows (tick_task_step sg original.(os_sched_call_stack).(stackLeaseSlot) old state)) **
    time_tick_body_residual sg state original.(os_sched_call_stack).(stackLeaseSlot) old) **
      (flag_pend_sched_node_fields_rep sg node state ** frame)) after ->
  (UCOS2_inv sg (tick_task_step sg original.(os_sched_call_stack).(stackLeaseSlot) old state) **
    (flag_pend_waiting_receipt sg original node call
      (tick_task_step sg original.(os_sched_call_stack).(stackLeaseSlot) old state) ** frame)) after.
Proof.
  intros sg original node call state old frame before after Hmulti Hlookup Hregistration Houtcome Hpre Hpost.
  pose proof (WakeComponent.time_tick_body_c_post_segment sg state original.(os_sched_call_stack).(stackLeaseSlot)
    old (flag_pend_sched_node_fields_rep sg node state ** frame) before after Hmulti Hlookup Hpre Hpost) as Hsegment.
  pose proof (proj2 (WakeComponent.kernel_wake_c_segment_resources _ _ _ _ _ _ _ Hsegment)) as Hresources.
  assert (Hnew : flag_active_waiting_registration original node call
    (tick_task_step sg original.(os_sched_call_stack).(stackLeaseSlot) old state))
    by (apply flag_active_waiting_registration_tick; assumption).
  assert (Hout : flag_pend_wait_outcome original node
    (tick_task_step sg original.(os_sched_call_stack).(stackLeaseSlot) old state))
    by (eapply flag_pend_tick_wait_outcome; eassumption).
  assert (Hfields : flag_pend_sched_node_fields_rep sg node
    (tick_task_step sg original.(os_sched_call_stack).(stackLeaseSlot) old state) =
    flag_pend_sched_node_fields_rep sg node state).
  { unfold flag_pend_sched_node_fields_rep, tick_task_step;
      destruct (Z.eqb old.(dly) 0); [reflexivity|].
    destruct (Z.eqb (tick_task_update old).(dly) 0); reflexivity. }
  match type of Hresources with ?P after =>
    match goal with |- ?Q after => assert (Htransport : P |-- Q) by
      (unfold flag_pend_waiting_receipt, flag_active_waiting; rewrite Hfields; entailer!) end end.
  exact (Htransport after Hresources).
Qed.

(** Scheduler installation changes the parked-stack map and current fields,
    not the waiter's registration or node fields.  This is only transport of
    a receipt already produced by a real Flag/Tick source, not its creation. *)
Lemma flag_pend_waiting_receipt_install :
  forall sg original node call context outgoing incoming state,
  flag_pend_waiting_receipt sg original node call state |--
  flag_pend_waiting_receipt sg original node call
    (os_sched_install_context context outgoing incoming state).
Proof.
  intros; unfold flag_pend_waiting_receipt, flag_pend_wait_outcome,
    flag_active_waiting, flag_active_waiting_registration, flag_active_task_fields,
    flag_pend_sched_node_fields_rep, os_sched_install_context,
    task_invocation_active, task_invocation_origin_live;
    cbn [replace_TskS replace_SchedS glob_task_set_parked_stacks]; entailer!.
Qed.

End FlagWaitingRecovery.
