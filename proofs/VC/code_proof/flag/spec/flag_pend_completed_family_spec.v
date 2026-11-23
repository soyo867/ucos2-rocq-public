(* Report candidate: actual module completions; staged only by the parent. *)
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
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_waiting_recovery_spec.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task_retirement.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_api_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_call_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_acquired_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_masked_c_step_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_returned_c_segment_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_wrapper_completion_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_retirement_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
Require Import Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_idle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_program_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_envelope_spec.
Require Import Coq.ZArith.ZArith Coq.Logic.FunctionalExtensionality Coq.Logic.PropExtensionality.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_fresh_recovery_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_fresh_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_returned_c_fresh_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_control_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_completion_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_completion_composition_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_outer_completion_spec.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_irq_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_caller_control_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_phase_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_call_spec.

Import UCOS2_C_Rules TaskStateDef ListNotations FlagPendSchedulerResources.
Import PrimitiveComponent PendPhaseCandidate.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import FlagWaitingRecovery FlagPendSchedulerResources PrimitiveComponent PendPhaseCandidate.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagWaitingSuccessor.

(** Only the private node fields are carried as a fixed Assertion.  These
    pure observations are re-established at every actual C successor cut.
    A retired or differently generated slot does not assert a live observer. *)
Definition flag_pend_detached_task_fields (task : TaskAbstractState) : Prop :=
  flag_active_event_clear task /\ task.(tcbFlagNode) = 0 /\
  (task.(statPend) = PendOK \/ task.(statPend) = PendAbort) /\ task.(dly) = 0.

Definition flag_pend_detached_fields_at_origin origin state : Prop :=
  match origin with
  | BootInvocation => True
  | RunningInvocation slot generation =>
      forall task, state.(TskState).(inUsedTaskStates) slot = Some task ->
      task.(taskGeneration) = generation -> flag_pend_detached_task_fields task
  end.

Lemma flag_pend_detached_fields_used_eq : forall origin before after,
  after.(TskState).(inUsedTaskStates) = before.(TskState).(inUsedTaskStates) ->
  flag_pend_detached_fields_at_origin origin before ->
  flag_pend_detached_fields_at_origin origin after.
Proof.
  intros [|slot generation] before after Hused Hfields; [exact I|].
  unfold flag_pend_detached_fields_at_origin in *; rewrite Hused; exact Hfields.
Qed.

Lemma flag_pend_detached_fields_task_update : forall origin before after slot old replacement,
  before.(TskState).(inUsedTaskStates) slot = Some old ->
  replacement.(taskGeneration) = old.(taskGeneration) ->
  (flag_pend_detached_task_fields old -> flag_pend_detached_task_fields replacement) ->
  after.(TskState).(inUsedTaskStates) =
    (glob_task_set_usedtask before.(TskState) slot replacement).(inUsedTaskStates) ->
  flag_pend_detached_fields_at_origin origin before ->
  flag_pend_detached_fields_at_origin origin after.
Proof.
  intros [|observed generation] before after slot old replacement Hold Hgen Hfields Hused Hbefore;
    [exact I|].
  unfold flag_pend_detached_fields_at_origin in *.
  intros task Htask Hg; rewrite Hused in Htask.
  cbn [glob_task_set_usedtask inUsedTaskStates] in Htask.
  destruct (Z.eqb observed slot) eqn:Heq.
  - apply Z.eqb_eq in Heq; subst observed; injection Htask as Htask; subst task.
    apply Hfields; apply (Hbefore old Hold); congruence.
  - exact (Hbefore task Htask Hg).
Qed.

Lemma flag_pend_waiting_detached_fields : forall sg original node call state heap,
  state.(FlagState).(flagWaitNodes) node = None ->
  flag_pend_waiting_receipt sg original node call state heap ->
  flag_pend_detached_fields_at_origin original.(os_sched_call_origin) state.
Proof.
  intros sg original node call state heap Hnone
    [[observed [Hobserved Houtcome]] [[task [Htask Hnode]] Hfields]].
  destruct Htask as [Hsame [Horigin [Hlookup [Hgen [Hactive Hclear]]]]].
  assert (observed = task) by congruence; subst observed.
  rewrite Hnone in Houtcome, Hnode; rewrite Horigin.
  intros next Hnext Hnextgen; assert (next = task) by congruence; subst next.
  unfold flag_pend_detached_task_fields; tauto.
Qed.

Lemma flag_task_rdy_domain_non_detached : forall sg state pointer waiter old bits,
  flag_task_rdy_domain sg state pointer waiter old bits ->
  ~ flag_pend_detached_task_fields old.
Proof.
  intros sg state pointer waiter old bits [_ [Hdomain Hrest]] [Hclear [Hnull Hstatus]].
  destruct Hdomain as [Hconfiguration [Hvalid [Hnode [Haddr [Hid [Hgen [Htcb Hpointer]]]]]]].
  pose proof (valid_flag_state_node_nonzero sg state.(FlagState) pointer waiter Hvalid Hnode).
  congruence.
Qed.

Lemma event_task_rdy_entry_non_detached : forall sg tasks eid event slot old,
  event_task_rdy_entry sg tasks eid event slot old ->
  ~ flag_pend_detached_task_fields old.
Proof.
  intros sg tasks eid event slot old [_ [_ [_ [_ [[Horder Hphase] [Hhead Hold]]]]]]
    [[Hnull Hrest] Hdetached].
  destruct (event_type_to_pend_type event.(eventType)) as [kind|] eqn:Hkind.
  - assert (Hin : In slot event.(waitList)).
    { destruct event.(waitList) as [|head tail]; [discriminate|].
      cbn in Hhead; injection Hhead as ->; simpl; auto. }
    destruct (Hphase slot Hin) as [task [Htask [Hptr Hremaining]]].
    assert (task = old) by congruence; subst task; congruence.
  - rewrite Hphase in Hhead; discriminate.
Qed.

(** The real C preconditions rule out a SECOND wake of the detached waiter.
    The old unguarded source relation alone cannot justify this argument. *)
Lemma kernel_wake_c_segment_detached_fields : forall sg entry before input returned after output origin,
  WakeComponent.kernel_wake_c_segment sg entry before input returned after output ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros sg entry before input returned after output origin Hsegment Hfields.
  destruct Hsegment as
    [entry pointer waiter old bits result c_result schedule checkpoint frame before after Hpre Hstep Hpost
    |entry eid event slot old kind message result c_result frame before after Hevent Hentry Hpre Hpost
    |entry slot old frame before after Hold Hpre Hpost].
  - destruct Hpre as [owned [rest [Hjoin [[Hdomain Hbody] Hframe]]]].
    pose proof Hdomain as [_ [Hunlinkdomain [Hold Hrest]]].
    destruct Hunlinkdomain as [Hconfiguration [Hvalid [Hnode Hrest']]].
    destruct (flag_task_rdy_result _ _ _ _ _ _ _ Hstep)
      as [actual [flags [found [Hunlink [Hfound [Hcheckpoint Hschedule]]]]]].
    pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hunlink)) as Hactual.
    assert (actual = waiter) by congruence; subst actual.
    assert (found = old) by congruence; subst found; subst checkpoint.
    eapply flag_pend_detached_fields_task_update with (replacement := task_flag_wake old bits result);
      [exact Hold|reflexivity| |reflexivity|exact Hfields].
    intro Hdetached; exfalso; eapply flag_task_rdy_domain_non_detached; eassumption.
  - pose proof Hentry as [_ [_ [_ [_ [_ [_ Hold]]]]]].
    eapply flag_pend_detached_fields_task_update with
      (replacement := task_event_wake_single old kind message result);
      [exact Hold|reflexivity| |reflexivity|exact Hfields].
    intro Hdetached; exfalso; eapply event_task_rdy_entry_non_detached; eassumption.
  - eapply flag_pend_detached_fields_task_update with (slot := slot) (old := old)
      (replacement := tick_task_update old).
    + exact Hold.
    + unfold tick_task_update; destruct (Z.eqb old.(dly) 0); reflexivity.
    + intros Hdetached; destruct Hdetached as [Hclear [Hnode [Hresult Hdelay]]].
      rewrite tick_task_zero_delay_eq by exact Hdelay.
      exact (conj Hclear (conj Hnode (conj Hresult Hdelay))).
    + rewrite (tick_task_step_task_state_eq sg slot old entry Hold); reflexivity.
    + exact Hfields.
Qed.

Lemma event_task_rdy_detached_fields : forall sg entry eid kind message result priority returned origin,
  (result = PendOK \/ result = PendAbort) ->
  event_task_rdy sg entry eid kind message result = Some (priority, returned) ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros sg entry eid kind message result priority returned origin Hresult Hstep Hfields.
  unfold event_task_rdy in Hstep.
  destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
  destruct (entry.(TskState).(prioTbl) (event_wait_priority entry.(TskState) event))
    as [| |slot]; try discriminate.
  destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
  injection Hstep as Hpriority Hreturned; subst returned.
  eapply flag_pend_detached_fields_task_update with
    (replacement := task_event_wake_single old kind message result);
    [exact Hold|reflexivity| |reflexivity|exact Hfields].
  intros [[Hptr [Hmulti Harray]] [Hnode [Hstatus Hdelay]]].
  unfold flag_pend_detached_task_fields, flag_active_event_clear.
  exact (conj (conj eq_refl (conj Hmulti Harray)) (conj Hnode (conj Hresult eq_refl))).
Qed.

Definition flag_wait_nodes_included before after : Prop :=
  forall pointer waiter, after.(FlagState).(flagWaitNodes) pointer = Some waiter ->
  exists previous, before.(FlagState).(flagWaitNodes) pointer = Some previous /\
    flag_waiter_link_identity waiter = flag_waiter_link_identity previous.

Lemma flag_wait_nodes_included_refl : forall state,
  flag_wait_nodes_included state state.
Proof. intros state pointer waiter Hnode; exists waiter; auto. Qed.

Lemma flag_wait_nodes_included_trans : forall before middle after,
  flag_wait_nodes_included before middle -> flag_wait_nodes_included middle after ->
  flag_wait_nodes_included before after.
Proof.
  intros before middle after Hfirst Hlast pointer waiter Hnode.
  destruct (Hlast pointer waiter Hnode) as [intermediate [Hmiddle Hidentity]].
  destruct (Hfirst pointer intermediate Hmiddle) as [previous [Hbefore Hidentity']].
  exists previous; split; [exact Hbefore|congruence].
Qed.

Lemma flag_wait_nodes_included_absent : forall before after pointer,
  flag_wait_nodes_included before after ->
  before.(FlagState).(flagWaitNodes) pointer = None ->
  after.(FlagState).(flagWaitNodes) pointer = None.
Proof.
  intros before after pointer Hsource Hnone.
  destruct (after.(FlagState).(flagWaitNodes) pointer) as [waiter|] eqn:Hnode; [|reflexivity].
  destruct (Hsource pointer waiter Hnode) as [previous [Hbefore Hidentity]]; congruence.
Qed.

Lemma kernel_wake_c_source_nodes_included : forall sg before after,
  WakeComponent.kernel_wake_c_source sg before after -> flag_wait_nodes_included before after.
Proof.
  intros sg before after Hsource; destruct Hsource.
  - destruct (flag_task_rdy_result _ _ _ _ _ _ _ H)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    intros other_pointer next Hnext.
    destruct (flag_unlink_surviving_node_origin _ _ _ _ _ _ Hunlink Hnext)
      as [Hdifferent [previous [Hprevious Hidentity]]].
    exists previous; exact (conj Hprevious Hidentity).
  - unfold event_task_rdy in H.
    destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
    destruct (entry.(TskState).(prioTbl) (event_wait_priority entry.(TskState) event))
      as [| |slot]; try discriminate.
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|]; [|discriminate].
    injection H as Hpriority Hreturned; subst returned.
    intros pointer waiter Hnode; exists waiter; split; [exact Hnode|reflexivity].
  - unfold tick_task_step; destruct (Z.eqb old.(dly) 0); [apply flag_wait_nodes_included_refl|].
    destruct (Z.eqb (tick_task_update old).(dly) 0);
      (intros pointer waiter Hnode; exists waiter; split; [exact Hnode|reflexivity]).
Qed.

Lemma flag_pend_waiting_receipt_take_node : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state original node call local fragments (frame : Assertion),
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  store_parked_continuations
    (kernel_saved_continuation_entry abi state.(TskState)
      (flag_continuation_local_node original.(os_sched_call_stack)
        (flag_pend_waiting_receipt sg original node call state) local))
    state.(TskState).(parkedTaskStacks) ** frame |--
  store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
    state.(TskState).(parkedTaskStacks) **
  flag_pend_waiting_receipt sg original node call state ** frame.
Proof.
  intros; sep_apply_l_atomic (flag_continuation_map_take_node external platform port abi
    state.(TskState) original.(os_sched_call_stack)
    (flag_pend_waiting_receipt sg original node call state) local state.(TskState).(parkedTaskStacks) fragments H);
    entailer!.
Qed.

End FlagWaitingSuccessor.

Import UCOS2_C_Rules TaskStateDef SchedStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


Module FlagWaitingDetachedSequence.
Import FlagWaitingSuccessor NamedSourceFrames.

Lemma task_suspend_state_preserves_detached_fields : forall entry slot node origin,
  entry.(TskState).(inUsedTaskStates) slot = Some node ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin (task_suspend_state entry slot node).
Proof.
  intros entry slot node origin Hnode Hfields.
  eapply flag_pend_detached_fields_task_update with (replacement := task_suspend node);
    [exact Hnode|reflexivity|intros H; exact H|reflexivity|exact Hfields].
Qed.

Lemma task_suspend_step_preserves_detached_fields : forall sg request priority entry result self returned origin,
  task_suspend_step sg request priority entry result self returned ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros sg request priority entry result self returned origin Hstep Hfields.
  destruct (TaskSuspendActualC.task_suspend_step_state_cases _ _ _ _ _ _ _ Hstep)
    as [->|[slot [node [Hnode ->]]]]; [exact Hfields|].
  eapply task_suspend_state_preserves_detached_fields; eassumption.
Qed.

Lemma kernel_status_c_source_preserves_detached_fields : forall sg entry returned origin,
  StatusComponent.kernel_status_c_source sg entry returned ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros sg entry returned origin Hsource Hfields; destruct Hsource.
  - destruct H as [cid [current [_ [_ [_ Hstep]]]]].
    destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg priority current))).
    + destruct Hstep as [_ ->]; exact Hfields.
    + destruct Hstep as [_ ->]; exact Hfields.
    + destruct Hstep as [old [Hold [_ ->]]].
      eapply task_suspend_state_preserves_detached_fields; eassumption.
  - destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority).
    + destruct Hstep as [_ ->]; exact Hfields.
    + destruct Hstep as [_ ->]; exact Hfields.
    + destruct Hstep as [old [Hold Hstep]]; destruct (task_is_suspended old.(stat)).
      * destruct Hstep as [_ ->].
        eapply flag_pend_detached_fields_task_update with (replacement := task_resume old);
          [exact Hold|reflexivity|intros H; exact H|reflexivity|exact Hfields].
      * destruct Hstep as [_ ->]; exact Hfields.
  - destruct H as [event [fields [_ [_ [_ ->]]]]]; destruct (Z.ltb 0 fields.(semCount)); exact Hfields.
Qed.

Lemma kernel_task_creation_c_source_preserves_detached_fields : forall sg entry returned origin,
  CreationComponent.kernel_task_creation_c_source sg entry returned ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros sg entry returned origin Hsource Hfields.
  apply (flag_pend_detached_fields_used_eq origin entry returned); [|exact Hfields].
  destruct Hsource; try reflexivity.
  - unfold task_create_critical in H; destruct (Z.ltb 0 entry.(IntrState).(intNesting)).
    + destruct H as [_ ->]; reflexivity.
    + destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority);
        destruct Hstep as [_ ->]; reflexivity.
  - destruct H2 as [_ ->]; reflexivity.
Qed.

Lemma kernel_event_creation_c_source_preserves_detached_fields : forall entry returned origin,
  EventCreationComponent.kernel_event_creation_c_source entry returned ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros entry returned origin Hsource Hfields.
  pose proof (kernel_event_creation_c_source_other_fields entry returned Hsource) as [Htasks _].
  eapply flag_pend_detached_fields_used_eq; [rewrite Htasks; reflexivity|exact Hfields].
Qed.

Lemma kernel_queue_creation_c_source_preserves_detached_fields : forall sg entry returned origin,
  QueueCreationComponent.kernel_queue_creation_c_source sg entry returned ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros sg entry returned origin Hsource Hfields.
  pose proof (kernel_queue_creation_c_source_other_fields sg entry returned Hsource) as [Htasks _].
  eapply flag_pend_detached_fields_used_eq; [rewrite Htasks; reflexivity|exact Hfields].
Qed.

Lemma task_delete_primitive_c_segment_preserves_detached_fields :
  forall environment critical sg entry before input stopped returned after output origin,
  DeleteComponent.task_delete_primitive_c_segment environment critical sg
    entry before input stopped returned after output ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros environment critical sg entry before input stopped returned after output origin Hstep Hfields.
  destruct Hstep; exact Hfields.
Qed.

Lemma flag_pend_task_primitive_c_step_preserves_detached_fields :
  forall environment critical sg entry before input stopped returned after output origin,
  PrimitiveComponent.flag_pend_task_primitive_c_step environment critical sg
    entry before input stopped returned after output ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros environment critical sg entry before input stopped returned after output origin Hstep Hfields.
  destruct Hstep; try exact Hfields.
  destruct H; exact Hfields.
Qed.

Lemma mutex_priority_task_preserves_detached_fields : forall task priority,
  flag_pend_detached_task_fields task ->
  flag_pend_detached_task_fields (mutex_priority_task task priority).
Proof. intros task priority Hfields; exact Hfields. Qed.

Lemma task_change_prio_critical_preserves_detached_fields :
  forall sg requested priority entry result returned origin,
  task_change_prio_critical sg requested priority entry result returned ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros sg requested priority entry result returned origin Hcode Hfields.
  unfold task_change_prio_critical in Hcode.
  destruct (entry.(TskState).(prioTbl) priority).
  - destruct Hcode as [selected [Hselection Hstep]].
    unfold task_change_prio_selected_effect in Hstep.
    destruct (Z.eqb selected sg.(osLowestPrio)).
    + destruct Hstep as [_ ->]; exact Hfields.
    + destruct (entry.(TskState).(prioTbl) selected).
      * destruct Hstep as [_ ->]; exact Hfields.
      * destruct Hstep as [_ ->]; exact Hfields.
      * destruct Hstep as [old [Hold [_ ->]]].
        eapply flag_pend_detached_fields_task_update with (replacement := mutex_priority_task old priority);
          [exact Hold|reflexivity|apply mutex_priority_task_preserves_detached_fields|reflexivity|exact Hfields].
  - destruct Hcode as [_ ->]; exact Hfields.
  - destruct Hcode as [_ ->]; exact Hfields.
Qed.

Lemma mutex_del_prepare_preserves_detached_fields : forall sg mutex entry returned origin,
  mutex_del_prepare sg mutex entry returned ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros sg mutex entry returned origin Hprepare Hfields.
  unfold mutex_del_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [subst returned; exact Hfields|].
  destruct mutex.(mfOwner) as [owner|].
  - destruct Hprepare as [node [priority [Hnode [Hpriority ->]]]].
    unfold mutex_del_owner_priority_state; destruct (Z.eq_dec node.(curPrio) priority).
    + exact Hfields.
    + eapply flag_pend_detached_fields_task_update with (replacement := mutex_priority_task node priority);
        [exact Hnode|reflexivity|apply mutex_priority_task_preserves_detached_fields|reflexivity|exact Hfields].
  - subst returned; exact Hfields.
Qed.

Lemma event_broadcast_preserves_detached_fields : forall sg eid kind message result entry priorities returned origin,
  (result = PendOK \/ result = PendAbort) ->
  event_broadcast sg eid kind message result entry priorities returned ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros sg eid kind message result entry priorities returned origin Hresult Hbroadcast.
  induction Hbroadcast; intro Hfields; [exact Hfields|].
  apply IHHbroadcast.
  eapply event_task_rdy_detached_fields; eassumption.
Qed.

Lemma mutex_del_critical_preserves_detached_fields : forall sg eid option entry result returned origin,
  mutex_del_critical sg eid option entry result returned ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros sg eid option entry result returned origin
    [event [mutex [Hevent [Htype [Hmutex Hstep]]]]] Hfields.
  destruct (Z.eq_dec option 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) entry.(TskState)) 0).
    + destruct Hstep as [prepared [Hprepare [-> Hresult]]].
      change (flag_pend_detached_fields_at_origin origin prepared).
      eapply mutex_del_prepare_preserves_detached_fields; eassumption.
    + destruct Hstep as [-> Hresult]; exact Hfields.
  - destruct (Z.eq_dec option 1).
    + destruct Hstep as [prepared [priorities [drained [Hprepare [Hbroadcast [-> Hresult]]]]]].
      change (flag_pend_detached_fields_at_origin origin drained).
      eapply event_broadcast_preserves_detached_fields; [right; reflexivity|exact Hbroadcast|].
      eapply mutex_del_prepare_preserves_detached_fields; eassumption.
    + destruct Hstep as [-> Hresult]; exact Hfields.
Qed.

Lemma kernel_critical_c_source_preserves_detached_fields : forall sg call origin,
  CriticalComponent.kernel_critical_c_source sg call ->
  flag_pend_detached_fields_at_origin origin (CriticalComponent.kernel_critical_c_entry call) ->
  flag_pend_detached_fields_at_origin origin (CriticalComponent.kernel_critical_c_returned call).
Proof.
  intros sg [actual|actual] origin Hsource Hfields; cbn in *.
  - destruct Hsource as [error [Hcritical Hresult]].
    eapply task_change_prio_critical_preserves_detached_fields; eassumption.
  - destruct Hsource.
    + destruct H0 as [error [scheduled [Hcritical Hencoding]]].
      eapply mutex_del_critical_preserves_detached_fields; eassumption.
    + exact Hfields.
Qed.

Lemma mutex_pend_inherit_step_preserves_detached_fields :
  forall sg entry owner node base waiter ceiling returned origin,
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_pend_inherit_step sg entry owner node base waiter ceiling returned ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros sg entry owner node base waiter ceiling returned origin Hnode Hstep Hfields.
  unfold mutex_pend_inherit_step in Hstep.
  destruct (mutex_pend_inherit_action sg.(osPrioMutexCeilDis) base node.(curPrio) waiter ceiling).
  - subst returned; exact Hfields.
  - subst returned; exact Hfields.
  - destruct Hstep as [events [Hevents ->]].
    eapply flag_pend_detached_fields_task_update with (replacement := mutex_priority_task node ceiling);
      [exact Hnode|reflexivity|apply mutex_priority_task_preserves_detached_fields|reflexivity|exact Hfields].
Qed.

Lemma mutex_post_prepare_preserves_detached_fields : forall sg mutex owner entry returned origin,
  mutex_post_prepare sg mutex owner entry returned ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros sg mutex owner entry returned origin Hprepare Hfields.
  unfold mutex_post_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [subst returned; exact Hfields|].
  destruct Hprepare as [node [priority [Hnode [Hpriority ->]]]].
  unfold mutex_post_owner_priority_state; destruct (Z.eq_dec node.(curPrio) priority).
  - exact Hfields.
  - eapply flag_pend_detached_fields_task_update with (replacement := mutex_priority_task node priority);
      [exact Hnode|reflexivity|apply mutex_priority_task_preserves_detached_fields|reflexivity|exact Hfields].
Qed.

Lemma mutex_post_critical_preserves_detached_fields : forall sg eid caller entry result schedule returned origin,
  mutex_post_critical sg eid caller entry result schedule returned ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros sg eid caller entry result schedule returned origin Hcritical Hfields; destruct Hcritical.
  - exact Hfields.
  - change (flag_pend_detached_fields_at_origin origin prepared).
    eapply mutex_post_prepare_preserves_detached_fields; eassumption.
  - change (flag_pend_detached_fields_at_origin origin woken).
    eapply event_task_rdy_detached_fields; [left; reflexivity|eassumption|].
    eapply mutex_post_prepare_preserves_detached_fields; eassumption.
Qed.

Lemma flag_pend_detached_fields_task_commit : forall origin before after priority invocation node,
  flag_pend_detached_task_fields node ->
  after.(TskState).(inUsedTaskStates) =
    (task_commit before.(TskState) priority invocation node).(inUsedTaskStates) ->
  flag_pend_detached_fields_at_origin origin before ->
  flag_pend_detached_fields_at_origin origin after.
Proof.
  intros [|slot generation] before after priority invocation node Hclear Hused Hfields; [exact I|].
  unfold flag_pend_detached_fields_at_origin in *.
  intros task Htask Hg; rewrite Hused in Htask.
  cbn [task_commit inUsedTaskStates] in Htask.
  destruct (Z.eq_dec slot node.(taskID)).
  - injection Htask as Htask; subst task; exact Hclear.
  - destruct before.(TskState).(tcbListHead) as [head|].
    + destruct (before.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
      destruct (Z.eq_dec slot head); injection Htask as Htask; subst task;
        exact (Hfields old eq_refl Hg).
    + exact (Hfields task Htask Hg).
Qed.

Lemma task_create_stack_publication_preserves_detached_fields : forall sg publication entry origin,
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin (task_create_stack_publication_state sg publication entry).
Proof.
  intros sg publication entry origin Hfields.
  eapply flag_pend_detached_fields_task_commit with
    (priority := (task_create_stack_publication_args publication).(initPrio))
    (invocation := publication.(stack_publication_invocation))
    (node := task_tcb_init_commit_node (task_create_stack_publication_args publication)
      publication.(stack_publication_acquired) publication.(stack_publication_slot)
      publication.(stack_publication_image));
    [unfold flag_pend_detached_task_fields, flag_active_event_clear; repeat split; try reflexivity; left; reflexivity
    |reflexivity|exact Hfields].
Qed.

Lemma flag_pend_detached_fields_task_recycle : forall sg origin before after tid priority node name,
  after.(TskState).(inUsedTaskStates) =
    (task_recycle sg before.(TskState) tid priority node name).(inUsedTaskStates) ->
  flag_pend_detached_fields_at_origin origin before ->
  flag_pend_detached_fields_at_origin origin after.
Proof.
  intros sg [|slot generation] before after tid priority node name Hused Hfields; [exact I|].
  unfold flag_pend_detached_fields_at_origin in *.
  intros task Htask Hg; rewrite Hused in Htask.
  cbn [task_recycle inUsedTaskStates] in Htask; unfold task_unlink_used_map in Htask.
  destruct (Z.eq_dec slot tid); [discriminate|].
  destruct (before.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
  injection Htask as Htask; subst task; exact (Hfields old eq_refl Hg).
Qed.

Lemma task_delete_prepare_after_unlink_preserves_detached_fields :
  forall entry after tid old updated origin,
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  after.(TskState).(inUsedTaskStates) = entry.(TskState).(inUsedTaskStates) ->
  updated.(taskGeneration) = old.(taskGeneration) ->
  (flag_pend_detached_task_fields old -> flag_pend_detached_task_fields updated) ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin (task_delete_prepare_after_unlink after tid updated).
Proof.
  intros entry after tid old updated origin Hold Hused Hgen Hclear Hfields.
  eapply flag_pend_detached_fields_task_update with (before := entry)
    (replacement := task_prepare_delete updated).
  - exact Hold.
  - exact Hgen.
  - intro H; destruct (Hclear H) as [Hclear_fields [Hnode Hrest]].
    exact (conj Hclear_fields (conj Hnode (conj (or_introl eq_refl) eq_refl))).
  - cbn [task_delete_prepare_after_unlink replace_SchedS replace_TskS TskState glob_task_set_usedtask
      inUsedTaskStates]; rewrite Hused; reflexivity.
  - exact Hfields.
Qed.

Lemma task_delete_prepare_single_wait_preserves_detached_fields :
  forall entry tid old prepared loan origin,
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  task_delete_prepare_single_wait entry tid old = Some (prepared, loan) ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin prepared.
Proof.
  intros entry tid old prepared loan origin Hold Hstep Hfields.
  unfold task_delete_prepare_single_wait in Hstep.
  destruct old.(eventPtr) as [eid|].
  - destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
    cbn [task_set_event_ptr tcbFlagNode] in Hstep.
    destruct (Z.eqb old.(tcbFlagNode) 0).
    + injection Hstep as Hprepared Hloan; subst prepared.
      eapply task_delete_prepare_after_unlink_preserves_detached_fields;
        [exact Hold|reflexivity|reflexivity| |exact Hfields].
      intros [[Hptr [Hmulti Harray]] [Hnode [Hresult Hdelay]]]; unfold flag_pend_detached_task_fields, flag_active_event_clear;
        repeat split; try assumption; reflexivity.
    + destruct (flag_unlink_node entry.(FlagState) old.(tcbFlagNode)) as [[waiter flags]|]; [|discriminate].
      injection Hstep as Hprepared Hloan; subst prepared.
      eapply task_delete_prepare_after_unlink_preserves_detached_fields;
        [exact Hold|reflexivity|reflexivity| |exact Hfields].
      intros [[Hptr [Hmulti Harray]] [Hnode [Hresult Hdelay]]]; unfold flag_pend_detached_task_fields, flag_active_event_clear;
        repeat split; try assumption; reflexivity.
  - destruct (Z.eqb old.(tcbFlagNode) 0).
    + injection Hstep as Hprepared Hloan; subst prepared.
      eapply task_delete_prepare_after_unlink_preserves_detached_fields;
        [exact Hold|reflexivity|reflexivity|intros H; exact H|exact Hfields].
    + destruct (flag_unlink_node entry.(FlagState) old.(tcbFlagNode)) as [[waiter flags]|]; [|discriminate].
      injection Hstep as Hprepared Hloan; subst prepared.
      eapply task_delete_prepare_after_unlink_preserves_detached_fields;
        [exact Hold|reflexivity|reflexivity| |exact Hfields].
      intros [Hclear [Hnode [Hresult Hdelay]]].
      exact (conj Hclear (conj eq_refl (conj Hresult Hdelay))).
Qed.

Lemma task_delete_own_c_segment_preserves_detached_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  DeleteComponent.task_delete_own_c_segment environment critical sg observer observer_origin
    entry before input stopped returned after output ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin
    Hstep Hfields; destruct Hstep.
  - destruct H0 as [Hprep Hinput Houtput].
    destruct Hprep as [[Hlookup [Hselected [Hlive Hpointer]]] [Hprepare Hrunning]].
    change (flag_pend_detached_fields_at_origin origin inputs.(DeleteComponent.delete_capture_prepared)).
    eapply task_delete_prepare_single_wait_preserves_detached_fields;
      [exact (proj2 (task_delete_table_lookup_live _ _ _ _ Hlive))|exact Hprepare|exact Hfields].
  - pose (inputs := capture.(DeleteComponent.delete_save_restore).(DeleteComponent.delete_restore_inputs)).
    exact (flag_pend_detached_fields_task_recycle inputs.(DeleteComponent.delete_capture_globals) origin
      capture.(DeleteComponent.delete_save_resumed) (DeleteComponent.task_delete_capture_cut capture)
      inputs.(DeleteComponent.delete_capture_tid) inputs.(DeleteComponent.delete_capture_priority)
      (task_delete_prepared_node inputs.(DeleteComponent.delete_capture_node))
      inputs.(DeleteComponent.delete_capture_name) eq_refl Hfields).
Qed.

Lemma kernel_builtin_c_segment_preserves_detached_fields :
  forall environment critical local sg entry before returned after input output origin,
  BuiltinComponent.kernel_builtin_c_segment environment critical local sg
    entry before returned after input output ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros environment critical local sg entry before returned after input output origin Hstep Hfields.
  destruct Hstep.
  - destruct operation; exact Hfields.
  - apply task_create_stack_publication_preserves_detached_fields; exact Hfields.
  - pose proof (BuiltinComponent.kernel_irq_transfer_c_completion_source environment critical sg
      handler saved entry transfer frame before after H) as Hsource.
    eapply flag_pend_detached_fields_used_eq; [|exact Hfields].
    exact (proj1 (BuiltinComponent.os_int_exit_configured_transfer_state_frame
      environment sg handler entry transfer Hsource)).
Qed.

Lemma task_install_c_step_preserves_detached_fields :
  forall environment local sg entry before input stopped returned after output origin,
  InstallComponent.task_install_c_step environment local sg
    entry before input stopped returned after output ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros environment local sg entry before input stopped returned after output origin Hstep Hfields.
  destruct Hstep; eapply flag_pend_detached_fields_used_eq; [reflexivity|exact Hfields].
Qed.

Lemma task_suspend_masked_c_step_preserves_detached_fields :
  forall environment critical sg entry before input stopped returned after output origin,
  TaskSuspendMaskedC.task_suspend_masked_c_step environment critical sg
    entry before input stopped returned after output ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros environment critical sg entry before input stopped returned after output origin Hstep Hfields.
  destruct Hstep as [saved_local caller saved call frame before after [[Hread Hcode] Hinput Houtput]].
  eapply task_suspend_step_preserves_detached_fields; eassumption.
Qed.

(** All thirteen original constructors retain their actual C source and
    resource completion.  No stop, current-task or target-inequality guard
    is needed for these fields once the concrete wake result is retained. *)
Lemma kernel_program_c_step_preserves_detached_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  kernel_program_c_step environment critical sg observer observer_origin
    entry before input stopped returned after output ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin
    Hstep Hfields; destruct Hstep.
  - destruct H as [Hcompletion [Hphysical [Hsource Hpacket]]].
    eapply kernel_critical_c_source_preserves_detached_fields; eassumption.
  - eapply kernel_builtin_c_segment_preserves_detached_fields; eassumption.
  - eapply task_install_c_step_preserves_detached_fields; eassumption.
  - eapply kernel_wake_c_segment_detached_fields; eassumption.
  - destruct H as [Hsource Hinput Houtput].
    eapply kernel_status_c_source_preserves_detached_fields; eassumption.
  - eapply kernel_task_creation_c_source_preserves_detached_fields;
      [eapply CreationComponent.kernel_task_creation_c_segment_source; exact H|exact Hfields].
  - eapply kernel_event_creation_c_source_preserves_detached_fields;
      [eapply EventCreationComponent.kernel_event_creation_c_segment_source; exact H|exact Hfields].
  - eapply kernel_queue_creation_c_source_preserves_detached_fields;
      [eapply QueueCreationComponent.kernel_queue_creation_c_segment_source; exact H|exact Hfields].
  - destruct H as [[Hnode [Hforeign Hsource]] Hinput Houtput].
    eapply mutex_pend_inherit_step_preserves_detached_fields; eassumption.
  - destruct H as [[Hcaller Hsource] Hinput Houtput].
    eapply mutex_post_critical_preserves_detached_fields; eassumption.
  - eapply task_delete_primitive_c_segment_preserves_detached_fields; eassumption.
  - eapply flag_pend_task_primitive_c_step_preserves_detached_fields; eassumption.
  - eapply task_delete_own_c_segment_preserves_detached_fields; eassumption.
Qed.

Lemma kernel_program_return_c_step_preserves_detached_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  SelectedReturnPrimitive.kernel_program_return_c_step environment critical sg observer observer_origin
    entry before input stopped returned after output ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin
    Hstep Hfields; destruct Hstep.
  - eapply kernel_program_c_step_preserves_detached_fields; eassumption.
  - destruct (SelectedReturnPrimitive.kernel_selected_return_c_step_state_stop _ _ _ _ _ _ _ _ H)
      as [-> Hstop]; exact Hfields.
  - eapply flag_pend_detached_fields_used_eq; [reflexivity|exact Hfields].
  - eapply flag_pend_detached_fields_used_eq; [reflexivity|exact Hfields].
Qed.

Lemma kernel_program_selected_c_step_preserves_detached_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  SelectedCProgram.kernel_program_selected_c_step environment critical sg observer observer_origin
    entry before input stopped returned after output ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin
    Hstep Hfields; destruct Hstep.
  - eapply kernel_program_return_c_step_preserves_detached_fields; eassumption.
  - destruct H.
    eapply flag_pend_detached_fields_used_eq; [|exact Hfields].
    exact (proj1 (BuiltinComponent.os_int_exit_configured_transfer_state_frame
      environment sg handler entry transfer source)).
  - eapply task_suspend_masked_c_step_preserves_detached_fields; eassumption.
Qed.

(** Induction consumes the given sequence, including its actual middle
    heaps and post-to-pre entailments.  The observer origin is fixed across
    every atom even when the execution's selected caller changes. *)
Lemma kernel_program_selected_c_sequence_preserves_detached_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  kernel_c_sequence
    (SelectedCProgram.kernel_program_selected_c_step environment critical sg observer observer_origin)
    entry before input stopped returned after output ->
  flag_pend_detached_fields_at_origin origin entry ->
  flag_pend_detached_fields_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin Hrun.
  induction Hrun; intro Hfields.
  - exact Hfields.
  - eapply kernel_program_selected_c_step_preserves_detached_fields; eassumption.
  - apply IHHrun2, IHHrun1, Hfields.
  - apply IHHrun, Hfields.
Qed.


End FlagWaitingDetachedSequence.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import FlagWaitingRecovery FlagWaitingSuccessor FlagWaitingDetachedSequence.
Import FlagPendSchedulerResources PrimitiveComponent PendPhaseCandidate.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagWaitingReceiptReindex.

(** A still-owned private node cannot simultaneously be a public Flag node
    on this exact heap. This obtains absence from actual ownership, rather
    than assuming that a later source state has retained the old map. *)
Lemma flag_private_node_fields_absent : forall sg state pointer image (frame : Assertion),
  UCOS2_fields_inv sg state ** flag_node_fields_rep sg.(osKernelConfig) pointer image ** frame |--
  coq_prop (state.(FlagState).(flagWaitNodes) pointer = None) &&
  (UCOS2_fields_inv sg state ** flag_node_fields_rep sg.(osKernelConfig) pointer image ** frame).
Proof.
  intros sg state pointer image frame.
  destruct (state.(FlagState).(flagWaitNodes) pointer) as [waiter|] eqn:Hnode; [|entailer!].
  assert (Hfalse :
    UCOS2_fields_inv sg state ** flag_node_fields_rep sg.(osKernelConfig) pointer image ** frame |--
    coq_prop False).
  { unfold UCOS2_fields_inv; Intros.
    destruct sg.(osKernelConfig).(cfgFlagEnabled) eqn:Henabled.
    - unfold UCOS2_fields_raw_rep, flag_fields_configured_rep; rewrite Henabled.
      unfold flag_fields_raw_rep.
      sep_apply_l_atomic (flag_wait_nodes_fields_rep_split_node sg state.(FlagState).(flagWaitNodes)
        pointer waiter Hnode).
      unfold flag_node_fields_rep.
      sepcon_right_assoc.
      sep_apply_l_atomic (dup_store_ptr pointer waiter.(flagWaitImage).(flagNodeNext) image.(flagNodeNext)); entailer!.
    - assert (Hconfiguration : valid_flag_configuration sg state.(FlagState))
        by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in *; tauto).
      unfold valid_flag_configuration in Hconfiguration; rewrite Henabled in Hconfiguration.
      rewrite Hconfiguration in Hnode; discriminate. }
  intros heap Howned; exfalso; exact (Hfalse heap Howned).
Qed.

Lemma flag_pend_detached_receipt_current : forall sg original node call previous returned current,
  previous.(FlagState).(flagWaitNodes) node = None ->
  current.(FlagState).(flagWaitNodes) node = None ->
  flag_pend_detached_fields_at_origin original.(os_sched_call_origin) current ->
  task_tcb_init_stack_same_call returned original ->
  kernel_call_task_source returned current ->
  flag_pend_waiting_receipt sg original node call previous |--
  flag_pend_waiting_receipt sg original node returned current.
Proof.
  intros sg original node call previous returned current Hprevious Hnone Hfields
    [Hinv [Horigin Hstack]] Hsource.
  pose proof (kernel_call_task_source_current_at returned current Hsource) as Hcurrent.
  destruct Hcurrent as [Hcur [task [Hlookup Hgen]]].
  rewrite Hstack in Hlookup, Hgen.
  destruct Hsource as [Hrunning [Hactive Hcurrent]].
  rewrite Horigin, Hstack in Hrunning; rewrite Hinv, Horigin in Hactive.
  rewrite Hrunning in Hfields.
  destruct (Hfields task Hlookup Hgen) as [Hclear [Hpointer [Hresult Hdelay]]].
  assert (Hregistration : flag_active_waiting_registration original node returned current).
  { exists task; split; [|rewrite Hnone; exact Hpointer].
    unfold flag_active_task_fields.
    exact (conj (conj Hinv (conj Horigin Hstack))
      (conj Hrunning (conj Hlookup (conj Hgen (conj Hactive Hclear))))). }
  assert (Houtcome : flag_pend_wait_outcome original node current).
  { exists task; split; [exact Hlookup|rewrite Hnone; exact (conj Hresult Hdelay)]. }
  unfold flag_pend_waiting_receipt, flag_active_waiting, flag_pend_sched_node_fields_rep.
  rewrite Hprevious, Hnone; Intros image; Exists image; entailer!.
Qed.

(** The source transition, not a future endpoint law, establishes the initial
    detached observation. The exact selected Hrun then transports it. *)
Lemma flag_task_rdy_selected_sequence_detached_fields :
  forall environment critical sg observer origin state original call node bits result schedule post
    before input stopped current after output,
  flag_active_waiting_registration original node call state ->
  (result = PendOK \/ result = PendAbort) ->
  flag_task_rdy sg state node bits result = Some (schedule, post) ->
  kernel_c_sequence
    (SelectedCProgram.kernel_program_selected_c_step environment critical sg observer origin)
    post before input stopped current after output ->
  flag_pend_detached_fields_at_origin original.(os_sched_call_origin) current.
Proof.
  intros environment critical sg observer origin state original call node bits result schedule post
    before input stopped current after output Hregistration Hresult Hstep Hrun.
  apply (kernel_program_selected_c_sequence_preserves_detached_fields environment critical sg observer origin
    post before input stopped current after output original.(os_sched_call_origin) Hrun).
  destruct (flag_active_task_rdy_waiting_registration sg state original call node bits result schedule post
    Hregistration Hstep) as [Hpost Hnone].
  pose proof (flag_pend_task_rdy_wait_outcome sg state original call node bits result schedule post
    Hregistration Hresult Hstep) as Houtcome.
  destruct Hpost as [task [[Hsame [Horigin [Hlookup [Hgen [Hactive Hclear]]]]] Hpointer]].
  destruct Houtcome as [observed [Hobserved Houtcome]].
  assert (observed = task) by congruence; subst observed.
  rewrite Hnone in Hpointer, Houtcome; rewrite Horigin.
  intros next Hnext Hg; assert (next = task) by congruence; subst next.
  unfold flag_pend_detached_task_fields; tauto.
Qed.

Lemma flag_pend_detached_receipt_absence : forall sg original node call previous current
  (frame : Assertion) heap,
  previous.(FlagState).(flagWaitNodes) node = None ->
  (UCOS2_fields_inv sg current ** flag_pend_waiting_receipt sg original node call previous ** frame) heap ->
  current.(FlagState).(flagWaitNodes) node = None.
Proof.
  intros sg original node call previous current frame heap Hnone Howned.
  assert (Hprojection :
    UCOS2_fields_inv sg current ** flag_pend_waiting_receipt sg original node call previous ** frame |--
    coq_prop (current.(FlagState).(flagWaitNodes) node = None)).
  { unfold flag_pend_waiting_receipt, flag_active_waiting, flag_pend_sched_node_fields_rep.
    rewrite Hnone; Intros image.
    sep_apply_l_atomic (flag_private_node_fields_absent sg current node image frame); entailer!. }
  exact (Hprojection heap Howned).
Qed.

(** The sequence output below is the OLD saved receipt and its actual owner,
    exactly what the selected take/restore contract transports.  The theorem
    derives the new waiting observation; it does not assume it in that output. *)
Lemma flag_task_rdy_selected_sequence_current_receipt :
  forall environment critical sg observer origin state original call node bits result schedule post
    before input stopped current after returned (frame : Assertion),
  flag_active_waiting_registration original node call state ->
  (result = PendOK \/ result = PendAbort) ->
  flag_task_rdy sg state node bits result = Some (schedule, post) ->
  kernel_c_sequence
    (SelectedCProgram.kernel_program_selected_c_step environment critical sg observer origin)
    post before input stopped current after
    (UCOS2_fields_inv sg current ** flag_pend_waiting_receipt sg original node call post ** frame) ->
  task_tcb_init_stack_same_call returned original ->
  kernel_call_task_source returned current ->
  (UCOS2_fields_inv sg current ** flag_pend_waiting_receipt sg original node returned current ** frame) after.
Proof.
  intros environment critical sg observer origin state original call node bits result schedule post
    before input stopped current after returned frame Hregistration Hresult Hstep Hrun Hsame Hsource.
  pose proof (proj2 (SelectedCProgram.kernel_program_selected_c_sequence_resources
    environment critical sg observer origin post before input stopped current after _ Hrun)) as Howned.
  destruct (flag_active_task_rdy_waiting_registration sg state original call node bits result schedule post
    Hregistration Hstep) as [Hpost Hnone].
  pose proof (flag_pend_detached_receipt_absence sg original node call post current frame after Hnone Howned)
    as Hcurrent_none.
  pose proof (flag_task_rdy_selected_sequence_detached_fields environment critical sg observer origin
    state original call node bits result schedule post before input stopped current after _
    Hregistration Hresult Hstep Hrun) as Hfields.
  match type of Howned with ?P after =>
    match goal with |- ?Q after => assert (Hrecover : P |-- Q) by
      (sep_apply_l_atomic (flag_pend_detached_receipt_current sg original node call post returned current
        Hnone Hcurrent_none Hfields Hsame Hsource); entailer!) end end.
  exact (Hrecover after Howned).
Qed.

End FlagWaitingReceiptReindex.

Import UCOS2_C_Rules TaskStateDef SchedStateDef EventStateDef ListNotations.
Import FlagWaitingSuccessor NamedSourceFrames.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagWaitingNodeInclusion.

Lemma flag_wait_nodes_included_flags_eq : forall before after,
  after.(FlagState) = before.(FlagState) -> flag_wait_nodes_included before after.
Proof.
  intros before after Hflags pointer waiter Hnode.
  rewrite Hflags in Hnode; exists waiter; auto.
Qed.

Lemma kernel_status_c_source_flag_state : forall sg entry returned,
  StatusComponent.kernel_status_c_source sg entry returned -> returned.(FlagState) = entry.(FlagState).
Proof.
  intros sg entry returned Hsource; destruct Hsource.
  - destruct H as [cid [current [_ [_ [_ Hstep]]]]].
    destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg priority current))).
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [old [Hold [_ ->]]]; reflexivity.
  - destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority).
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [old [Hold Hstep]]; destruct (task_is_suspended old.(stat));
        destruct Hstep as [_ ->]; reflexivity.
  - destruct H as [event [fields [_ [_ [_ ->]]]]]; destruct (Z.ltb 0 fields.(semCount)); reflexivity.
Qed.

Lemma kernel_task_creation_c_source_flag_state : forall sg entry returned,
  CreationComponent.kernel_task_creation_c_source sg entry returned -> returned.(FlagState) = entry.(FlagState).
Proof.
  intros sg entry returned Hsource; destruct Hsource; try reflexivity.
  - unfold task_create_critical in H; destruct (Z.ltb 0 entry.(IntrState).(intNesting)).
    + destruct H as [_ ->]; reflexivity.
    + destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority);
        destruct Hstep as [_ ->]; reflexivity.
  - destruct H2 as [_ ->]; reflexivity.
Qed.

Lemma kernel_event_creation_c_source_flag_state : forall entry returned,
  EventCreationComponent.kernel_event_creation_c_source entry returned -> returned.(FlagState) = entry.(FlagState).
Proof.
  intros entry returned Hsource; destruct Hsource; try reflexivity.
  unfold event_create_allocate_critical in H; destruct (entry.(EventState).(unUsedEventStates)).
  - destruct H as [_ ->]; reflexivity.
  - destruct H as [image [_ [_ ->]]]; reflexivity.
Qed.

Lemma kernel_queue_creation_c_source_flag_state : forall sg entry returned,
  QueueCreationComponent.kernel_queue_creation_c_source sg entry returned -> returned.(FlagState) = entry.(FlagState).
Proof.
  intros sg entry returned Hsource; destruct Hsource; [|reflexivity].
  destruct H0 as [allocation [Hget Hcode]]; destruct free; destruct Hcode as [_ ->]; reflexivity.
Qed.

Lemma task_change_prio_critical_flag_state : forall sg requested priority entry result returned,
  task_change_prio_critical sg requested priority entry result returned -> returned.(FlagState) = entry.(FlagState).
Proof.
  intros sg requested priority entry result returned Hcode.
  unfold task_change_prio_critical in Hcode; destruct (entry.(TskState).(prioTbl) priority).
  - destruct Hcode as [selected [Hselection Hstep]]; unfold task_change_prio_selected_effect in Hstep.
    destruct (Z.eqb selected sg.(osLowestPrio)).
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct (entry.(TskState).(prioTbl) selected).
      * destruct Hstep as [_ ->]; reflexivity.
      * destruct Hstep as [_ ->]; reflexivity.
      * destruct Hstep as [old [Hold [_ ->]]]; reflexivity.
  - destruct Hcode as [_ ->]; reflexivity.
  - destruct Hcode as [_ ->]; reflexivity.
Qed.

Lemma mutex_del_prepare_flag_state : forall sg mutex entry returned,
  mutex_del_prepare sg mutex entry returned -> returned.(FlagState) = entry.(FlagState).
Proof.
  intros sg mutex entry returned Hprepare; unfold mutex_del_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [subst returned; reflexivity|].
  destruct mutex.(mfOwner) as [owner|].
  - destruct Hprepare as [node [priority [Hnode [Hpriority ->]]]].
    unfold mutex_del_owner_priority_state; destruct (Z.eq_dec node.(curPrio) priority); reflexivity.
  - subst returned; reflexivity.
Qed.

Lemma event_task_rdy_flag_state : forall sg entry eid kind message result priority returned,
  event_task_rdy sg entry eid kind message result = Some (priority, returned) ->
  returned.(FlagState) = entry.(FlagState).
Proof.
  intros sg entry eid kind message result priority returned Hstep; unfold event_task_rdy in Hstep.
  destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
  destruct (entry.(TskState).(prioTbl) (event_wait_priority entry.(TskState) event)) as [| |slot]; try discriminate.
  destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|]; [|discriminate].
  injection Hstep as Hpriority Hreturned; subst returned; reflexivity.
Qed.

Lemma event_broadcast_flag_state : forall sg eid kind message result entry priorities returned,
  event_broadcast sg eid kind message result entry priorities returned -> returned.(FlagState) = entry.(FlagState).
Proof.
  intros sg eid kind message result entry priorities returned Hbroadcast; induction Hbroadcast; [reflexivity|].
  rewrite IHHbroadcast; eapply event_task_rdy_flag_state; eassumption.
Qed.

Lemma mutex_del_critical_flag_state : forall sg eid option entry result returned,
  mutex_del_critical sg eid option entry result returned -> returned.(FlagState) = entry.(FlagState).
Proof.
  intros sg eid option entry result returned [event [mutex [Hevent [Htype [Hmutex Hstep]]]]].
  destruct (Z.eq_dec option 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) entry.(TskState)) 0).
    + destruct Hstep as [prepared [Hprepare [-> Hresult]]]; cbn.
      eapply mutex_del_prepare_flag_state; eassumption.
    + destruct Hstep as [-> Hresult]; reflexivity.
  - destruct (Z.eq_dec option 1).
    + destruct Hstep as [prepared [priorities [drained [Hprepare [Hbroadcast [-> Hresult]]]]]]; cbn.
      rewrite (event_broadcast_flag_state _ _ _ _ _ _ _ _ Hbroadcast).
      eapply mutex_del_prepare_flag_state; eassumption.
    + destruct Hstep as [-> Hresult]; reflexivity.
Qed.

Lemma kernel_critical_c_source_flag_state : forall sg call,
  CriticalComponent.kernel_critical_c_source sg call ->
  (CriticalComponent.kernel_critical_c_returned call).(FlagState) =
  (CriticalComponent.kernel_critical_c_entry call).(FlagState).
Proof.
  intros sg [actual|actual] Hsource; cbn in *.
  - destruct Hsource as [error [Hcritical Hresult]]; eapply task_change_prio_critical_flag_state; eassumption.
  - destruct Hsource.
    + destruct H0 as [error [scheduled [Hcritical Hencoding]]]; eapply mutex_del_critical_flag_state; eassumption.
    + reflexivity.
Qed.

Lemma mutex_pend_inherit_step_flag_state : forall sg entry owner node base waiter ceiling returned,
  mutex_pend_inherit_step sg entry owner node base waiter ceiling returned -> returned.(FlagState) = entry.(FlagState).
Proof.
  intros sg entry owner node base waiter ceiling returned Hstep; unfold mutex_pend_inherit_step in Hstep.
  destruct (mutex_pend_inherit_action sg.(osPrioMutexCeilDis) base node.(curPrio) waiter ceiling).
  - subst returned; reflexivity.
  - subst returned; reflexivity.
  - destruct Hstep as [events [Hevents ->]]; reflexivity.
Qed.

Lemma mutex_post_prepare_flag_state : forall sg mutex owner entry returned,
  mutex_post_prepare sg mutex owner entry returned -> returned.(FlagState) = entry.(FlagState).
Proof.
  intros sg mutex owner entry returned Hprepare; unfold mutex_post_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [subst returned; reflexivity|].
  destruct Hprepare as [node [priority [Hnode [Hpriority ->]]]].
  unfold mutex_post_owner_priority_state; destruct (Z.eq_dec node.(curPrio) priority); reflexivity.
Qed.

Lemma mutex_post_critical_flag_state : forall sg eid caller entry result schedule returned,
  mutex_post_critical sg eid caller entry result schedule returned -> returned.(FlagState) = entry.(FlagState).
Proof.
  intros sg eid caller entry result schedule returned Hcritical; destruct Hcritical; [reflexivity| |].
  - change (prepared.(FlagState) = entry.(FlagState)); eapply mutex_post_prepare_flag_state; eassumption.
  - change (woken.(FlagState) = entry.(FlagState)).
    rewrite (event_task_rdy_flag_state _ _ _ _ _ _ _ _ H5).
    eapply mutex_post_prepare_flag_state; eassumption.
Qed.

Lemma task_delete_prepare_single_wait_nodes_included : forall entry tid old prepared loan,
  task_delete_prepare_single_wait entry tid old = Some (prepared, loan) -> flag_wait_nodes_included entry prepared.
Proof.
  intros entry tid old prepared loan Hstep; unfold task_delete_prepare_single_wait in Hstep.
  destruct old.(eventPtr) as [eid|].
  - destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
    cbn [task_set_event_ptr tcbFlagNode] in Hstep; destruct (Z.eqb old.(tcbFlagNode) 0).
    + injection Hstep as Hprepared Hloan; subst prepared; apply flag_wait_nodes_included_flags_eq; reflexivity.
    + destruct (flag_unlink_node entry.(FlagState) old.(tcbFlagNode)) as [[waiter flags]|] eqn:Hunlink; [|discriminate].
      injection Hstep as Hprepared Hloan; subst prepared; intros pointer next Hnext.
      destruct (flag_unlink_surviving_node_origin _ _ _ _ _ _ Hunlink Hnext) as [Hdifferent [previous [Hprevious Hidentity]]].
      exists previous; exact (conj Hprevious Hidentity).
  - destruct (Z.eqb old.(tcbFlagNode) 0).
    + injection Hstep as Hprepared Hloan; subst prepared; apply flag_wait_nodes_included_flags_eq; reflexivity.
    + destruct (flag_unlink_node entry.(FlagState) old.(tcbFlagNode)) as [[waiter flags]|] eqn:Hunlink; [|discriminate].
      injection Hstep as Hprepared Hloan; subst prepared; intros pointer next Hnext.
      destruct (flag_unlink_surviving_node_origin _ _ _ _ _ _ Hunlink Hnext) as [Hdifferent [previous [Hprevious Hidentity]]].
      exists previous; exact (conj Hprevious Hidentity).
Qed.

Lemma task_delete_own_c_segment_nodes_included :
  forall environment critical sg observer origin entry before input stopped returned after output,
  DeleteComponent.task_delete_own_c_segment environment critical sg observer origin
    entry before input stopped returned after output -> flag_wait_nodes_included entry returned.
Proof.
  intros environment critical sg observer origin entry before input stopped returned after output Hstep; destruct Hstep.
  - destruct H0 as [Hprep Hinput Houtput].
    destruct Hprep as [Hlookup [Hprepare Hrunning]].
    change (flag_wait_nodes_included inputs.(DeleteComponent.delete_capture_acquired)
      inputs.(DeleteComponent.delete_capture_prepared)).
    eapply task_delete_prepare_single_wait_nodes_included; exact Hprepare.
  - apply flag_wait_nodes_included_flags_eq; reflexivity.
Qed.

Lemma kernel_builtin_c_segment_flag_state :
  forall environment critical local sg entry before returned after input output,
  BuiltinComponent.kernel_builtin_c_segment environment critical local sg entry before returned after input output ->
  returned.(FlagState) = entry.(FlagState).
Proof.
  intros environment critical local sg entry before returned after input output Hstep; destruct Hstep.
  - destruct operation; reflexivity.
  - reflexivity.
  - pose proof (BuiltinComponent.kernel_irq_transfer_c_completion_source environment critical sg
      handler saved entry transfer frame before after H) as Hsource.
    unfold os_int_exit_installed_state.
    rewrite (BuiltinComponent.os_int_exit_configured_transfer_hooked_eq environment sg handler entry transfer Hsource).
    reflexivity.
Qed.

Lemma kernel_program_c_step_nodes_included :
  forall environment critical sg observer origin entry before input stopped returned after output,
  kernel_program_c_step environment critical sg observer origin entry before input stopped returned after output ->
  flag_wait_nodes_included entry returned.
Proof.
  intros environment critical sg observer origin entry before input stopped returned after output Hstep; destruct Hstep.
  - apply flag_wait_nodes_included_flags_eq; destruct H as [Hcompletion [Hphysical [Hsource Hpacket]]].
    eapply kernel_critical_c_source_flag_state; eassumption.
  - apply flag_wait_nodes_included_flags_eq; eapply kernel_builtin_c_segment_flag_state; eassumption.
  - apply flag_wait_nodes_included_flags_eq; destruct H; reflexivity.
  - eapply kernel_wake_c_source_nodes_included; eapply WakeComponent.kernel_wake_c_segment_source; exact H.
  - apply flag_wait_nodes_included_flags_eq; destruct H as [Hsource Hinput Houtput].
    eapply kernel_status_c_source_flag_state; eassumption.
  - apply flag_wait_nodes_included_flags_eq; eapply kernel_task_creation_c_source_flag_state;
      eapply CreationComponent.kernel_task_creation_c_segment_source; exact H.
  - apply flag_wait_nodes_included_flags_eq; eapply kernel_event_creation_c_source_flag_state;
      eapply EventCreationComponent.kernel_event_creation_c_segment_source; exact H.
  - apply flag_wait_nodes_included_flags_eq; eapply kernel_queue_creation_c_source_flag_state;
      eapply QueueCreationComponent.kernel_queue_creation_c_segment_source; exact H.
  - apply flag_wait_nodes_included_flags_eq; destruct H as [[Hnode [Hforeign Hsource]] Hinput Houtput].
    eapply mutex_pend_inherit_step_flag_state; eassumption.
  - apply flag_wait_nodes_included_flags_eq; destruct H as [[Hcaller Hsource] Hinput Houtput].
    eapply mutex_post_critical_flag_state; eassumption.
  - apply flag_wait_nodes_included_flags_eq; destruct H; reflexivity.
  - apply flag_wait_nodes_included_flags_eq; destruct H; try reflexivity; destruct H; reflexivity.
  - eapply task_delete_own_c_segment_nodes_included; eassumption.
Qed.

Lemma kernel_program_return_c_step_nodes_included :
  forall environment critical sg observer origin entry before input stopped returned after output,
  SelectedReturnPrimitive.kernel_program_return_c_step environment critical sg observer origin
    entry before input stopped returned after output -> flag_wait_nodes_included entry returned.
Proof.
  intros environment critical sg observer origin entry before input stopped returned after output Hstep; destruct Hstep.
  - eapply kernel_program_c_step_nodes_included; eassumption.
  - destruct (SelectedReturnPrimitive.kernel_selected_return_c_step_state_stop _ _ _ _ _ _ _ _ H) as [-> Hstop].
    apply flag_wait_nodes_included_refl.
  - apply flag_wait_nodes_included_flags_eq; reflexivity.
  - apply flag_wait_nodes_included_flags_eq; reflexivity.
Qed.

Lemma kernel_program_selected_c_step_nodes_included :
  forall environment critical sg observer origin entry before input stopped returned after output,
  SelectedCProgram.kernel_program_selected_c_step environment critical sg observer origin
    entry before input stopped returned after output -> flag_wait_nodes_included entry returned.
Proof.
  intros environment critical sg observer origin entry before input stopped returned after output Hstep; destruct Hstep.
  - eapply kernel_program_return_c_step_nodes_included; eassumption.
  - destruct H; apply flag_wait_nodes_included_flags_eq; unfold os_int_exit_installed_state.
    rewrite (BuiltinComponent.os_int_exit_configured_transfer_hooked_eq environment sg handler entry transfer source).
    reflexivity.
  - apply flag_wait_nodes_included_flags_eq.
    destruct H as [saved_local caller saved call frame before after [[Hread Hcode] Hinput Houtput]].
    destruct (TaskSuspendActualC.task_suspend_step_state_cases _ _ _ _ _ _ _ Hcode) as [->|[slot [node [Hnode ->]]]];
      reflexivity.
Qed.

(** The relation follows this exact execution and its actual middle heaps.
    This union contains removal and update, but no FlagBlock insertion. *)
Lemma kernel_program_selected_c_sequence_nodes_included :
  forall environment critical sg observer origin entry before input stopped returned after output,
  kernel_c_sequence (SelectedCProgram.kernel_program_selected_c_step environment critical sg observer origin)
    entry before input stopped returned after output -> flag_wait_nodes_included entry returned.
Proof.
  intros environment critical sg observer origin entry before input stopped returned after output Hrun; induction Hrun.
  - apply flag_wait_nodes_included_refl.
  - eapply kernel_program_selected_c_step_nodes_included; eassumption.
  - eapply flag_wait_nodes_included_trans; eassumption.
  - exact IHHrun.
Qed.

End FlagWaitingNodeInclusion.

Import UCOS2_C_Rules TaskStateDef SchedStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


Module FlagWaitingMultiPointer.
Import NamedSourceFrames.

Definition flag_pend_zero_multi_task (task : TaskAbstractState) : Prop :=
  task.(tcbEventMultiPtr) = 0.

Definition flag_pend_zero_multi_at_origin origin state : Prop :=
  match origin with
  | BootInvocation => True
  | RunningInvocation slot generation =>
      forall task, state.(TskState).(inUsedTaskStates) slot = Some task ->
      task.(taskGeneration) = generation -> flag_pend_zero_multi_task task
  end.

Lemma flag_pend_zero_multi_fields_used_eq : forall origin before after,
  after.(TskState).(inUsedTaskStates) = before.(TskState).(inUsedTaskStates) ->
  flag_pend_zero_multi_at_origin origin before ->
  flag_pend_zero_multi_at_origin origin after.
Proof.
  intros [|slot generation] before after Hused Hfields; [exact I|].
  unfold flag_pend_zero_multi_at_origin in *; rewrite Hused; exact Hfields.
Qed.

Lemma flag_pend_zero_multi_fields_task_update : forall origin before after slot old replacement,
  before.(TskState).(inUsedTaskStates) slot = Some old ->
  replacement.(taskGeneration) = old.(taskGeneration) ->
  (flag_pend_zero_multi_task old -> flag_pend_zero_multi_task replacement) ->
  after.(TskState).(inUsedTaskStates) =
    (glob_task_set_usedtask before.(TskState) slot replacement).(inUsedTaskStates) ->
  flag_pend_zero_multi_at_origin origin before ->
  flag_pend_zero_multi_at_origin origin after.
Proof.
  intros [|observed generation] before after slot old replacement Hold Hgen Hfields Hused Hbefore;
    [exact I|].
  unfold flag_pend_zero_multi_at_origin in *.
  intros task Htask Hg; rewrite Hused in Htask.
  cbn [glob_task_set_usedtask inUsedTaskStates] in Htask.
  destruct (Z.eqb observed slot) eqn:Heq.
  - apply Z.eqb_eq in Heq; subst observed; injection Htask as Htask; subst task.
    apply Hfields; apply (Hbefore old Hold); congruence.
  - exact (Hbefore task Htask Hg).
Qed.

Lemma kernel_wake_c_source_zero_multi_fields : forall sg entry returned origin,
  WakeComponent.kernel_wake_c_source sg entry returned ->
  flag_pend_zero_multi_at_origin origin entry -> flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros sg entry returned origin Hsource Hfields; destruct Hsource.
  - destruct (flag_task_rdy_result _ _ _ _ _ _ _ H)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    eapply flag_pend_zero_multi_fields_task_update with (replacement := task_flag_wake old bits result);
      [exact Hold|reflexivity|intros Hzero; exact Hzero|reflexivity|exact Hfields].
  - unfold event_task_rdy in H.
    destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
    destruct (entry.(TskState).(prioTbl) (event_wait_priority entry.(TskState) event)) as [| |slot]; try discriminate.
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
    injection H as Hpriority Hreturned; subst returned.
    eapply flag_pend_zero_multi_fields_task_update with (replacement := task_event_wake_single old kind message result);
      [exact Hold|reflexivity|intros Hzero; exact Hzero|reflexivity|exact Hfields].
  - eapply flag_pend_zero_multi_fields_task_update with (slot := slot) (old := old)
      (replacement := tick_task_update old).
    + exact H.
    + unfold tick_task_update; destruct (Z.eqb old.(dly) 0); reflexivity.
    + intro Hzero; unfold flag_pend_zero_multi_task, tick_task_update in *;
        destruct (Z.eqb old.(dly) 0); exact Hzero.
    + rewrite (tick_task_step_task_state_eq sg slot old entry H); reflexivity.
    + exact Hfields.
Qed.

Lemma event_task_rdy_zero_multi_fields : forall sg entry eid kind message result priority returned origin,
  event_task_rdy sg entry eid kind message result = Some (priority, returned) ->
  flag_pend_zero_multi_at_origin origin entry -> flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros sg entry eid kind message result priority returned origin Hstep Hfields.
  eapply kernel_wake_c_source_zero_multi_fields; [econstructor 2; exact Hstep|exact Hfields].
Qed.

Lemma task_suspend_state_preserves_zero_multi_fields : forall entry slot node origin,
  entry.(TskState).(inUsedTaskStates) slot = Some node ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin (task_suspend_state entry slot node).
Proof.
  intros entry slot node origin Hnode Hfields.
  eapply flag_pend_zero_multi_fields_task_update with (replacement := task_suspend node);
    [exact Hnode|reflexivity|intros H; exact H|reflexivity|exact Hfields].
Qed.

Lemma task_suspend_step_preserves_zero_multi_fields : forall sg request priority entry result self returned origin,
  task_suspend_step sg request priority entry result self returned ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros sg request priority entry result self returned origin Hstep Hfields.
  destruct (TaskSuspendActualC.task_suspend_step_state_cases _ _ _ _ _ _ _ Hstep)
    as [->|[slot [node [Hnode ->]]]]; [exact Hfields|].
  eapply task_suspend_state_preserves_zero_multi_fields; eassumption.
Qed.

Lemma kernel_status_c_source_preserves_zero_multi_fields : forall sg entry returned origin,
  StatusComponent.kernel_status_c_source sg entry returned ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros sg entry returned origin Hsource Hfields; destruct Hsource.
  - destruct H as [cid [current [_ [_ [_ Hstep]]]]].
    destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg priority current))).
    + destruct Hstep as [_ ->]; exact Hfields.
    + destruct Hstep as [_ ->]; exact Hfields.
    + destruct Hstep as [old [Hold [_ ->]]].
      eapply task_suspend_state_preserves_zero_multi_fields; eassumption.
  - destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority).
    + destruct Hstep as [_ ->]; exact Hfields.
    + destruct Hstep as [_ ->]; exact Hfields.
    + destruct Hstep as [old [Hold Hstep]]; destruct (task_is_suspended old.(stat)).
      * destruct Hstep as [_ ->].
        eapply flag_pend_zero_multi_fields_task_update with (replacement := task_resume old);
          [exact Hold|reflexivity|intros H; exact H|reflexivity|exact Hfields].
      * destruct Hstep as [_ ->]; exact Hfields.
  - destruct H as [event [fields [_ [_ [_ ->]]]]]; destruct (Z.ltb 0 fields.(semCount)); exact Hfields.
Qed.

Lemma kernel_task_creation_c_source_preserves_zero_multi_fields : forall sg entry returned origin,
  CreationComponent.kernel_task_creation_c_source sg entry returned ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros sg entry returned origin Hsource Hfields.
  apply (flag_pend_zero_multi_fields_used_eq origin entry returned); [|exact Hfields].
  destruct Hsource; try reflexivity.
  - unfold task_create_critical in H; destruct (Z.ltb 0 entry.(IntrState).(intNesting)).
    + destruct H as [_ ->]; reflexivity.
    + destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority);
        destruct Hstep as [_ ->]; reflexivity.
  - destruct H2 as [_ ->]; reflexivity.
Qed.

Lemma kernel_event_creation_c_source_preserves_zero_multi_fields : forall entry returned origin,
  EventCreationComponent.kernel_event_creation_c_source entry returned ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros entry returned origin Hsource Hfields.
  pose proof (kernel_event_creation_c_source_other_fields entry returned Hsource) as [Htasks _].
  eapply flag_pend_zero_multi_fields_used_eq; [rewrite Htasks; reflexivity|exact Hfields].
Qed.

Lemma kernel_queue_creation_c_source_preserves_zero_multi_fields : forall sg entry returned origin,
  QueueCreationComponent.kernel_queue_creation_c_source sg entry returned ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros sg entry returned origin Hsource Hfields.
  pose proof (kernel_queue_creation_c_source_other_fields sg entry returned Hsource) as [Htasks _].
  eapply flag_pend_zero_multi_fields_used_eq; [rewrite Htasks; reflexivity|exact Hfields].
Qed.

Lemma task_delete_primitive_c_segment_preserves_zero_multi_fields :
  forall environment critical sg entry before input stopped returned after output origin,
  DeleteComponent.task_delete_primitive_c_segment environment critical sg
    entry before input stopped returned after output ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros environment critical sg entry before input stopped returned after output origin Hstep Hfields.
  destruct Hstep; exact Hfields.
Qed.

Lemma flag_pend_task_primitive_c_step_preserves_zero_multi_fields :
  forall environment critical sg entry before input stopped returned after output origin,
  PrimitiveComponent.flag_pend_task_primitive_c_step environment critical sg
    entry before input stopped returned after output ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros environment critical sg entry before input stopped returned after output origin Hstep Hfields.
  destruct Hstep; try exact Hfields.
  destruct H; exact Hfields.
Qed.

Lemma mutex_priority_task_preserves_zero_multi_fields : forall task priority,
  flag_pend_zero_multi_task task ->
  flag_pend_zero_multi_task (mutex_priority_task task priority).
Proof. intros task priority Hfields; exact Hfields. Qed.

Lemma task_change_prio_critical_preserves_zero_multi_fields :
  forall sg requested priority entry result returned origin,
  task_change_prio_critical sg requested priority entry result returned ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros sg requested priority entry result returned origin Hcode Hfields.
  unfold task_change_prio_critical in Hcode.
  destruct (entry.(TskState).(prioTbl) priority).
  - destruct Hcode as [selected [Hselection Hstep]].
    unfold task_change_prio_selected_effect in Hstep.
    destruct (Z.eqb selected sg.(osLowestPrio)).
    + destruct Hstep as [_ ->]; exact Hfields.
    + destruct (entry.(TskState).(prioTbl) selected).
      * destruct Hstep as [_ ->]; exact Hfields.
      * destruct Hstep as [_ ->]; exact Hfields.
      * destruct Hstep as [old [Hold [_ ->]]].
        eapply flag_pend_zero_multi_fields_task_update with (replacement := mutex_priority_task old priority);
          [exact Hold|reflexivity|apply mutex_priority_task_preserves_zero_multi_fields|reflexivity|exact Hfields].
  - destruct Hcode as [_ ->]; exact Hfields.
  - destruct Hcode as [_ ->]; exact Hfields.
Qed.

Lemma mutex_del_prepare_preserves_zero_multi_fields : forall sg mutex entry returned origin,
  mutex_del_prepare sg mutex entry returned ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros sg mutex entry returned origin Hprepare Hfields.
  unfold mutex_del_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [subst returned; exact Hfields|].
  destruct mutex.(mfOwner) as [owner|].
  - destruct Hprepare as [node [priority [Hnode [Hpriority ->]]]].
    unfold mutex_del_owner_priority_state; destruct (Z.eq_dec node.(curPrio) priority).
    + exact Hfields.
    + eapply flag_pend_zero_multi_fields_task_update with (replacement := mutex_priority_task node priority);
        [exact Hnode|reflexivity|apply mutex_priority_task_preserves_zero_multi_fields|reflexivity|exact Hfields].
  - subst returned; exact Hfields.
Qed.

Lemma event_broadcast_preserves_zero_multi_fields : forall sg eid kind message result entry priorities returned origin,
  event_broadcast sg eid kind message result entry priorities returned ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros sg eid kind message result entry priorities returned origin Hbroadcast.
  induction Hbroadcast; intro Hfields; [exact Hfields|].
  apply IHHbroadcast.
  eapply event_task_rdy_zero_multi_fields; eassumption.
Qed.

Lemma mutex_del_critical_preserves_zero_multi_fields : forall sg eid option entry result returned origin,
  mutex_del_critical sg eid option entry result returned ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros sg eid option entry result returned origin
    [event [mutex [Hevent [Htype [Hmutex Hstep]]]]] Hfields.
  destruct (Z.eq_dec option 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) entry.(TskState)) 0).
    + destruct Hstep as [prepared [Hprepare [-> Hresult]]].
      change (flag_pend_zero_multi_at_origin origin prepared).
      eapply mutex_del_prepare_preserves_zero_multi_fields; eassumption.
    + destruct Hstep as [-> Hresult]; exact Hfields.
  - destruct (Z.eq_dec option 1).
    + destruct Hstep as [prepared [priorities [drained [Hprepare [Hbroadcast [-> Hresult]]]]]].
      change (flag_pend_zero_multi_at_origin origin drained).
      eapply event_broadcast_preserves_zero_multi_fields; [exact Hbroadcast|].
      eapply mutex_del_prepare_preserves_zero_multi_fields; eassumption.
    + destruct Hstep as [-> Hresult]; exact Hfields.
Qed.

Lemma kernel_critical_c_source_preserves_zero_multi_fields : forall sg call origin,
  CriticalComponent.kernel_critical_c_source sg call ->
  flag_pend_zero_multi_at_origin origin (CriticalComponent.kernel_critical_c_entry call) ->
  flag_pend_zero_multi_at_origin origin (CriticalComponent.kernel_critical_c_returned call).
Proof.
  intros sg [actual|actual] origin Hsource Hfields; cbn in *.
  - destruct Hsource as [error [Hcritical Hresult]].
    eapply task_change_prio_critical_preserves_zero_multi_fields; eassumption.
  - destruct Hsource.
    + destruct H0 as [error [scheduled [Hcritical Hencoding]]].
      eapply mutex_del_critical_preserves_zero_multi_fields; eassumption.
    + exact Hfields.
Qed.

Lemma mutex_pend_inherit_step_preserves_zero_multi_fields :
  forall sg entry owner node base waiter ceiling returned origin,
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_pend_inherit_step sg entry owner node base waiter ceiling returned ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros sg entry owner node base waiter ceiling returned origin Hnode Hstep Hfields.
  unfold mutex_pend_inherit_step in Hstep.
  destruct (mutex_pend_inherit_action sg.(osPrioMutexCeilDis) base node.(curPrio) waiter ceiling).
  - subst returned; exact Hfields.
  - subst returned; exact Hfields.
  - destruct Hstep as [events [Hevents ->]].
    eapply flag_pend_zero_multi_fields_task_update with (replacement := mutex_priority_task node ceiling);
      [exact Hnode|reflexivity|apply mutex_priority_task_preserves_zero_multi_fields|reflexivity|exact Hfields].
Qed.

Lemma mutex_post_prepare_preserves_zero_multi_fields : forall sg mutex owner entry returned origin,
  mutex_post_prepare sg mutex owner entry returned ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros sg mutex owner entry returned origin Hprepare Hfields.
  unfold mutex_post_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [subst returned; exact Hfields|].
  destruct Hprepare as [node [priority [Hnode [Hpriority ->]]]].
  unfold mutex_post_owner_priority_state; destruct (Z.eq_dec node.(curPrio) priority).
  - exact Hfields.
  - eapply flag_pend_zero_multi_fields_task_update with (replacement := mutex_priority_task node priority);
      [exact Hnode|reflexivity|apply mutex_priority_task_preserves_zero_multi_fields|reflexivity|exact Hfields].
Qed.

Lemma mutex_post_critical_preserves_zero_multi_fields : forall sg eid caller entry result schedule returned origin,
  mutex_post_critical sg eid caller entry result schedule returned ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros sg eid caller entry result schedule returned origin Hcritical Hfields; destruct Hcritical.
  - exact Hfields.
  - change (flag_pend_zero_multi_at_origin origin prepared).
    eapply mutex_post_prepare_preserves_zero_multi_fields; eassumption.
  - change (flag_pend_zero_multi_at_origin origin woken).
    eapply event_task_rdy_zero_multi_fields; [eassumption|].
    eapply mutex_post_prepare_preserves_zero_multi_fields; eassumption.
Qed.

Lemma flag_pend_zero_multi_fields_task_commit : forall origin before after priority invocation node,
  flag_pend_zero_multi_task node ->
  after.(TskState).(inUsedTaskStates) =
    (task_commit before.(TskState) priority invocation node).(inUsedTaskStates) ->
  flag_pend_zero_multi_at_origin origin before ->
  flag_pend_zero_multi_at_origin origin after.
Proof.
  intros [|slot generation] before after priority invocation node Hclear Hused Hfields; [exact I|].
  unfold flag_pend_zero_multi_at_origin in *.
  intros task Htask Hg; rewrite Hused in Htask.
  cbn [task_commit inUsedTaskStates] in Htask.
  destruct (Z.eq_dec slot node.(taskID)).
  - injection Htask as Htask; subst task; exact Hclear.
  - destruct before.(TskState).(tcbListHead) as [head|].
    + destruct (before.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
      destruct (Z.eq_dec slot head); injection Htask as Htask; subst task;
        exact (Hfields old eq_refl Hg).
    + exact (Hfields task Htask Hg).
Qed.

Lemma task_create_stack_publication_preserves_zero_multi_fields : forall sg publication entry origin,
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin (task_create_stack_publication_state sg publication entry).
Proof.
  intros sg publication entry origin Hfields.
  eapply flag_pend_zero_multi_fields_task_commit with
    (priority := (task_create_stack_publication_args publication).(initPrio))
    (invocation := publication.(stack_publication_invocation))
    (node := task_tcb_init_commit_node (task_create_stack_publication_args publication)
      publication.(stack_publication_acquired) publication.(stack_publication_slot)
      publication.(stack_publication_image));
    [reflexivity
    |reflexivity|exact Hfields].
Qed.

Lemma flag_pend_zero_multi_fields_task_recycle : forall sg origin before after tid priority node name,
  after.(TskState).(inUsedTaskStates) =
    (task_recycle sg before.(TskState) tid priority node name).(inUsedTaskStates) ->
  flag_pend_zero_multi_at_origin origin before ->
  flag_pend_zero_multi_at_origin origin after.
Proof.
  intros sg [|slot generation] before after tid priority node name Hused Hfields; [exact I|].
  unfold flag_pend_zero_multi_at_origin in *.
  intros task Htask Hg; rewrite Hused in Htask.
  cbn [task_recycle inUsedTaskStates] in Htask; unfold task_unlink_used_map in Htask.
  destruct (Z.eq_dec slot tid); [discriminate|].
  destruct (before.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
  injection Htask as Htask; subst task; exact (Hfields old eq_refl Hg).
Qed.

Lemma task_delete_prepare_after_unlink_preserves_zero_multi_fields :
  forall entry after tid old updated origin,
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  after.(TskState).(inUsedTaskStates) = entry.(TskState).(inUsedTaskStates) ->
  updated.(taskGeneration) = old.(taskGeneration) ->
  (flag_pend_zero_multi_task old -> flag_pend_zero_multi_task updated) ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin (task_delete_prepare_after_unlink after tid updated).
Proof.
  intros entry after tid old updated origin Hold Hused Hgen Hclear Hfields.
  eapply flag_pend_zero_multi_fields_task_update with (before := entry)
    (replacement := task_prepare_delete updated).
  - exact Hold.
  - exact Hgen.
  - intro Hzero; exact (Hclear Hzero).
  - cbn [task_delete_prepare_after_unlink replace_SchedS replace_TskS TskState glob_task_set_usedtask
      inUsedTaskStates]; rewrite Hused; reflexivity.
  - exact Hfields.
Qed.

Lemma task_delete_prepare_single_wait_preserves_zero_multi_fields :
  forall entry tid old prepared loan origin,
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  task_delete_prepare_single_wait entry tid old = Some (prepared, loan) ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin prepared.
Proof.
  intros entry tid old prepared loan origin Hold Hstep Hfields.
  unfold task_delete_prepare_single_wait in Hstep.
  destruct old.(eventPtr) as [eid|].
  - destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
    cbn [task_set_event_ptr tcbFlagNode] in Hstep.
    destruct (Z.eqb old.(tcbFlagNode) 0).
    + injection Hstep as Hprepared Hloan; subst prepared.
      eapply task_delete_prepare_after_unlink_preserves_zero_multi_fields;
        [exact Hold|reflexivity|reflexivity| |exact Hfields].
      intro Hzero; exact Hzero.
    + destruct (flag_unlink_node entry.(FlagState) old.(tcbFlagNode)) as [[waiter flags]|]; [|discriminate].
      injection Hstep as Hprepared Hloan; subst prepared.
      eapply task_delete_prepare_after_unlink_preserves_zero_multi_fields;
        [exact Hold|reflexivity|reflexivity| |exact Hfields].
      intro Hzero; exact Hzero.
  - destruct (Z.eqb old.(tcbFlagNode) 0).
    + injection Hstep as Hprepared Hloan; subst prepared.
      eapply task_delete_prepare_after_unlink_preserves_zero_multi_fields;
        [exact Hold|reflexivity|reflexivity|intros H; exact H|exact Hfields].
    + destruct (flag_unlink_node entry.(FlagState) old.(tcbFlagNode)) as [[waiter flags]|]; [|discriminate].
      injection Hstep as Hprepared Hloan; subst prepared.
      eapply task_delete_prepare_after_unlink_preserves_zero_multi_fields;
        [exact Hold|reflexivity|reflexivity| |exact Hfields].
      intro Hzero; exact Hzero.
Qed.

Lemma task_delete_own_c_segment_preserves_zero_multi_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  DeleteComponent.task_delete_own_c_segment environment critical sg observer observer_origin
    entry before input stopped returned after output ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin
    Hstep Hfields; destruct Hstep.
  - destruct H0 as [Hprep Hinput Houtput].
    destruct Hprep as [[Hlookup [Hselected [Hlive Hpointer]]] [Hprepare Hrunning]].
    change (flag_pend_zero_multi_at_origin origin inputs.(DeleteComponent.delete_capture_prepared)).
    eapply task_delete_prepare_single_wait_preserves_zero_multi_fields;
      [exact (proj2 (task_delete_table_lookup_live _ _ _ _ Hlive))|exact Hprepare|exact Hfields].
  - pose (inputs := capture.(DeleteComponent.delete_save_restore).(DeleteComponent.delete_restore_inputs)).
    exact (flag_pend_zero_multi_fields_task_recycle inputs.(DeleteComponent.delete_capture_globals) origin
      capture.(DeleteComponent.delete_save_resumed) (DeleteComponent.task_delete_capture_cut capture)
      inputs.(DeleteComponent.delete_capture_tid) inputs.(DeleteComponent.delete_capture_priority)
      (task_delete_prepared_node inputs.(DeleteComponent.delete_capture_node))
      inputs.(DeleteComponent.delete_capture_name) eq_refl Hfields).
Qed.

Lemma kernel_builtin_c_segment_preserves_zero_multi_fields :
  forall environment critical local sg entry before returned after input output origin,
  BuiltinComponent.kernel_builtin_c_segment environment critical local sg
    entry before returned after input output ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros environment critical local sg entry before returned after input output origin Hstep Hfields.
  destruct Hstep.
  - destruct operation; exact Hfields.
  - apply task_create_stack_publication_preserves_zero_multi_fields; exact Hfields.
  - pose proof (BuiltinComponent.kernel_irq_transfer_c_completion_source environment critical sg
      handler saved entry transfer frame before after H) as Hsource.
    eapply flag_pend_zero_multi_fields_used_eq; [|exact Hfields].
    exact (proj1 (BuiltinComponent.os_int_exit_configured_transfer_state_frame
      environment sg handler entry transfer Hsource)).
Qed.

Lemma task_install_c_step_preserves_zero_multi_fields :
  forall environment local sg entry before input stopped returned after output origin,
  InstallComponent.task_install_c_step environment local sg
    entry before input stopped returned after output ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros environment local sg entry before input stopped returned after output origin Hstep Hfields.
  destruct Hstep; eapply flag_pend_zero_multi_fields_used_eq; [reflexivity|exact Hfields].
Qed.

Lemma task_suspend_masked_c_step_preserves_zero_multi_fields :
  forall environment critical sg entry before input stopped returned after output origin,
  TaskSuspendMaskedC.task_suspend_masked_c_step environment critical sg
    entry before input stopped returned after output ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros environment critical sg entry before input stopped returned after output origin Hstep Hfields.
  destruct Hstep as [saved_local caller saved call frame before after [[Hread Hcode] Hinput Houtput]].
  eapply task_suspend_step_preserves_zero_multi_fields; eassumption.
Qed.

Lemma kernel_program_c_step_preserves_zero_multi_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  kernel_program_c_step environment critical sg observer observer_origin
    entry before input stopped returned after output ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin
    Hstep Hfields; destruct Hstep.
  - destruct H as [Hcompletion [Hphysical [Hsource Hpacket]]].
    eapply kernel_critical_c_source_preserves_zero_multi_fields; eassumption.
  - eapply kernel_builtin_c_segment_preserves_zero_multi_fields; eassumption.
  - eapply task_install_c_step_preserves_zero_multi_fields; eassumption.
  - eapply kernel_wake_c_source_zero_multi_fields;
      [eapply WakeComponent.kernel_wake_c_segment_source; exact H|exact Hfields].
  - destruct H as [Hsource Hinput Houtput].
    eapply kernel_status_c_source_preserves_zero_multi_fields; eassumption.
  - eapply kernel_task_creation_c_source_preserves_zero_multi_fields;
      [eapply CreationComponent.kernel_task_creation_c_segment_source; exact H|exact Hfields].
  - eapply kernel_event_creation_c_source_preserves_zero_multi_fields;
      [eapply EventCreationComponent.kernel_event_creation_c_segment_source; exact H|exact Hfields].
  - eapply kernel_queue_creation_c_source_preserves_zero_multi_fields;
      [eapply QueueCreationComponent.kernel_queue_creation_c_segment_source; exact H|exact Hfields].
  - destruct H as [[Hnode [Hforeign Hsource]] Hinput Houtput].
    eapply mutex_pend_inherit_step_preserves_zero_multi_fields; eassumption.
  - destruct H as [[Hcaller Hsource] Hinput Houtput].
    eapply mutex_post_critical_preserves_zero_multi_fields; eassumption.
  - eapply task_delete_primitive_c_segment_preserves_zero_multi_fields; eassumption.
  - eapply flag_pend_task_primitive_c_step_preserves_zero_multi_fields; eassumption.
  - eapply task_delete_own_c_segment_preserves_zero_multi_fields; eassumption.
Qed.

Lemma kernel_program_return_c_step_preserves_zero_multi_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  SelectedReturnPrimitive.kernel_program_return_c_step environment critical sg observer observer_origin
    entry before input stopped returned after output ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin
    Hstep Hfields; destruct Hstep.
  - eapply kernel_program_c_step_preserves_zero_multi_fields; eassumption.
  - destruct (SelectedReturnPrimitive.kernel_selected_return_c_step_state_stop _ _ _ _ _ _ _ _ H)
      as [-> Hstop]; exact Hfields.
  - eapply flag_pend_zero_multi_fields_used_eq; [reflexivity|exact Hfields].
  - eapply flag_pend_zero_multi_fields_used_eq; [reflexivity|exact Hfields].
Qed.

Lemma kernel_program_selected_c_step_preserves_zero_multi_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  SelectedCProgram.kernel_program_selected_c_step environment critical sg observer observer_origin
    entry before input stopped returned after output ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin
    Hstep Hfields; destruct Hstep.
  - eapply kernel_program_return_c_step_preserves_zero_multi_fields; eassumption.
  - destruct H.
    eapply flag_pend_zero_multi_fields_used_eq; [|exact Hfields].
    exact (proj1 (BuiltinComponent.os_int_exit_configured_transfer_state_frame
      environment sg handler entry transfer source)).
  - eapply task_suspend_masked_c_step_preserves_zero_multi_fields; eassumption.
Qed.

Lemma kernel_program_selected_c_sequence_preserves_zero_multi_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  kernel_c_sequence
    (SelectedCProgram.kernel_program_selected_c_step environment critical sg observer observer_origin)
    entry before input stopped returned after output ->
  flag_pend_zero_multi_at_origin origin entry ->
  flag_pend_zero_multi_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin Hrun.
  induction Hrun; intro Hfields.
  - exact Hfields.
  - eapply kernel_program_selected_c_step_preserves_zero_multi_fields; eassumption.
  - apply IHHrun2, IHHrun1, Hfields.
  - apply IHHrun, Hfields.
Qed.

End FlagWaitingMultiPointer.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import FlagWaitingRecovery FlagWaitingSuccessor FlagWaitingNodeInclusion FlagWaitingMultiPointer.
Import FlagPendSchedulerResources PrimitiveComponent PendPhaseCandidate.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagWaitingLinkedReturn.

Lemma flag_waiting_registration_zero_multi_fields : forall original node call state,
  flag_active_waiting_registration original node call state ->
  flag_pend_zero_multi_at_origin original.(os_sched_call_origin) state.
Proof.
  intros original node call state [task [[Hsame [Horigin [Hlookup [Hgen [Hactive [Hptr [Hlist Hmulti]]]]]]] Hnode]].
  rewrite Horigin; intros other Hother Hg; assert (other = task) by congruence; subst other; exact Hmulti.
Qed.

Lemma flag_wait_nodes_included_identity : forall entry current node original next,
  flag_wait_nodes_included entry current ->
  entry.(FlagState).(flagWaitNodes) node = Some original ->
  current.(FlagState).(flagWaitNodes) node = Some next ->
  next.(flagNodeAddr) = original.(flagNodeAddr) /\
  next.(flagTask) = original.(flagTask) /\ next.(flagTaskGeneration) = original.(flagTaskGeneration).
Proof.
  intros entry current node original next Hsource Horiginal Hnext.
  destruct (Hsource node next Hnext) as [previous [Hprevious Hidentity]].
  assert (previous = original) by congruence; subst previous.
  unfold flag_waiter_link_identity in Hidentity; inversion Hidentity; auto.
Qed.

(** A real ready selector with a surviving Flag link can only return the
    timeout phase. Its link identity comes from this execution, and the
    remaining Multi pointer comes from actual writer-field transport. *)
Lemma flag_waiting_linked_ready_observations :
  forall sg entry current original call returned node old_waiter waiter,
  flag_active_waiting_registration original node call entry ->
  entry.(FlagState).(flagWaitNodes) node = Some old_waiter ->
  flag_wait_nodes_included entry current ->
  current.(FlagState).(flagWaitNodes) node = Some waiter ->
  UCOS2_state_inv sg current ->
  flag_pend_zero_multi_at_origin original.(os_sched_call_origin) current ->
  task_tcb_init_stack_same_call returned original -> kernel_call_task_source returned current ->
  flag_pend_current_ready returned current ->
  flag_active_waiting_registration original node returned current /\
  flag_pend_wait_outcome original node current.
Proof.
  intros sg entry current original call returned node old_waiter waiter
    [old [Hold Hlink]] Hentry Hnodes Hcurrent Hvalid Hmulti Hsame Hsource
    [task [[Hlookup [Hcur [Hprio [Hin Hready]]]] Hgen]].
  destruct Hsame as [Hinv [Horigin Hstack]].
  rewrite Hstack in Hlookup, Hgen.
  rewrite Hentry in Hlink; destruct Hlink as [Haddr [Hkey Hpointer]].
  destruct (flag_wait_nodes_included_identity entry current node old_waiter waiter Hnodes Hentry Hcurrent)
    as [Haddr' [Hslot Hgeneration]].
  assert (Hkey' : task_stack_key original.(os_sched_call_stack) =
      (waiter.(flagTask), waiter.(flagTaskGeneration))) by (rewrite Hslot, Hgeneration; exact Hkey).
  unfold task_stack_key in Hkey'; injection Hkey' as Hslot' Hgen'.
  assert (Hcross : task_flag_waiter_consistency sg current.(TskState) current.(FlagState))
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, cross_module_consistency in Hvalid; tauto).
  destruct (proj1 Hcross node waiter Hcurrent)
    as [Hnonzero [linked [Hlinked [Hlinked_gen [Hflag [Htcb [Hphase [Hevent Hlist]]]]]]]].
  rewrite <- Hslot' in Hlinked; assert (linked = task) by congruence; subst linked.
  destruct Hsource as [Hrunning [Hactive Hsource_current]].
  rewrite Horigin, Hstack in Hrunning; rewrite Hinv, Horigin in Hactive.
  rewrite Hrunning in Hmulti.
  pose proof (Hmulti task Hlookup Hgen) as Harray.
  pose proof (task_effectively_ready_has_no_pending task Hready) as Hpending.
  destruct Hphase as [Hflag_pending|Htimeout].
  { change (task_non_suspension_bits task.(stat) = 32) in Hflag_pending; lia. }
  split.
  - exists task; split.
    + unfold flag_active_task_fields, flag_active_event_clear.
      exact (conj (conj Hinv (conj Horigin Hstack))
        (conj Hrunning (conj Hlookup (conj Hgen (conj Hactive (conj Hevent (conj Hlist Harray))))))).
    + rewrite Hcurrent; split; [congruence|split; [unfold task_stack_key; congruence|exact Hflag]].
  - exists task; split; [exact Hlookup|rewrite Hcurrent; right; exact Htimeout].
Qed.

Lemma flag_pend_linked_selected_ready_receipt :
  forall environment critical sg observer origin original call returned node entry old_waiter
    before input stopped current waiter after (frame : Assertion),
  entry.(FlagState).(flagWaitNodes) node = Some old_waiter ->
  current.(FlagState).(flagWaitNodes) node = Some waiter ->
  kernel_c_sequence
    (SelectedCProgram.kernel_program_selected_c_step environment critical sg observer origin)
    entry before input stopped current after
    (UCOS2_fields_inv sg current ** flag_pend_waiting_receipt sg original node call entry ** frame) ->
  task_tcb_init_stack_same_call returned original -> kernel_call_task_source returned current ->
  flag_pend_current_ready returned current ->
  (UCOS2_fields_inv sg current ** flag_pend_waiting_receipt sg original node returned current ** frame) after.
Proof.
  intros environment critical sg observer origin original call returned node entry old_waiter
    before input stopped current waiter after frame Hentry Hcurrent Hrun Hsame Hsource Hready.
  pose proof (proj2 (SelectedCProgram.kernel_program_selected_c_sequence_resources
    environment critical sg observer origin entry before input stopped current after _ Hrun)) as Howned.
  assert (Hprojection :
    UCOS2_fields_inv sg current ** flag_pend_waiting_receipt sg original node call entry ** frame |--
    coq_prop (UCOS2_state_inv sg current /\ flag_active_waiting_registration original node call entry)).
  { unfold UCOS2_fields_inv, flag_pend_waiting_receipt, flag_active_waiting; entailer!. }
  destruct (Hprojection after Howned) as [Hvalid Hregistration].
  pose proof (kernel_program_selected_c_sequence_nodes_included _ _ _ _ _ _ _ _ _ _ _ _ Hrun) as Hnodes.
  pose proof (kernel_program_selected_c_sequence_preserves_zero_multi_fields environment critical sg observer origin
    entry before input stopped current after _ original.(os_sched_call_origin) Hrun
      (flag_waiting_registration_zero_multi_fields original node call entry Hregistration)) as Hmulti.
  destruct (flag_waiting_linked_ready_observations sg entry current original call returned node old_waiter waiter
    Hregistration Hentry Hnodes Hcurrent Hvalid Hmulti Hsame Hsource Hready) as [Hregistration' Houtcome].
  assert (Hrecover :
    UCOS2_fields_inv sg current ** flag_pend_waiting_receipt sg original node call entry ** frame |--
    UCOS2_fields_inv sg current ** flag_pend_waiting_receipt sg original node returned current ** frame).
  { unfold flag_pend_waiting_receipt, flag_active_waiting, flag_pend_sched_node_fields_rep.
    rewrite Hentry, Hcurrent; entailer!. }
  exact (Hrecover after Howned).
Qed.

End FlagWaitingLinkedReturn.

Import UCOS2_C_Rules TaskStateDef SchedStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.



Module FlagWaitingPendingResult.
Import NamedSourceFrames.

Definition flag_pend_pending_result_task (task : TaskAbstractState) : Prop :=
  task_non_suspension_bits task.(stat) = task_pend_mask PendFlag -> task.(statPend) = PendOK.

Definition flag_pend_pending_result_at_origin origin state : Prop :=
  match origin with
  | BootInvocation => True
  | RunningInvocation slot generation =>
      forall task, state.(TskState).(inUsedTaskStates) slot = Some task ->
      task.(taskGeneration) = generation -> flag_pend_pending_result_task task
  end.

Lemma flag_pend_pending_result_fields_used_eq : forall origin before after,
  after.(TskState).(inUsedTaskStates) = before.(TskState).(inUsedTaskStates) ->
  flag_pend_pending_result_at_origin origin before ->
  flag_pend_pending_result_at_origin origin after.
Proof.
  intros [|slot generation] before after Hused Hfields; [exact I|].
  unfold flag_pend_pending_result_at_origin in *; rewrite Hused; exact Hfields.
Qed.

Lemma flag_pend_pending_result_fields_task_update : forall origin before after slot old replacement,
  before.(TskState).(inUsedTaskStates) slot = Some old ->
  replacement.(taskGeneration) = old.(taskGeneration) ->
  (flag_pend_pending_result_task old -> flag_pend_pending_result_task replacement) ->
  after.(TskState).(inUsedTaskStates) =
    (glob_task_set_usedtask before.(TskState) slot replacement).(inUsedTaskStates) ->
  flag_pend_pending_result_at_origin origin before ->
  flag_pend_pending_result_at_origin origin after.
Proof.
  intros [|observed generation] before after slot old replacement Hold Hgen Hfields Hused Hbefore;
    [exact I|].
  unfold flag_pend_pending_result_at_origin in *.
  intros task Htask Hg; rewrite Hused in Htask.
  cbn [glob_task_set_usedtask inUsedTaskStates] in Htask.
  destruct (Z.eqb observed slot) eqn:Heq.
  - apply Z.eqb_eq in Heq; subst observed; injection Htask as Htask; subst task.
    apply Hfields; apply (Hbefore old Hold); congruence.
  - exact (Hbefore task Htask Hg).
Qed.


Lemma task_suspend_preserves_pending_result : forall task,
  flag_pend_pending_result_task task -> flag_pend_pending_result_task (task_suspend task).
Proof.
  intros task Hpending Hbits; apply Hpending.
  change (task_non_suspension_bits (task_status_suspend task.(stat)) = task_pend_mask PendFlag) in Hbits.
  rewrite (proj1 (task_status_suspend_observations task.(stat))) in Hbits; exact Hbits.
Qed.

Lemma task_resume_preserves_pending_result : forall task,
  flag_pend_pending_result_task task -> flag_pend_pending_result_task (task_resume task).
Proof.
  intros task Hpending Hbits; apply Hpending.
  change (task_non_suspension_bits (task_status_resume task.(stat)) = task_pend_mask PendFlag) in Hbits.
  rewrite (proj1 (task_status_resume_observations task.(stat))) in Hbits; exact Hbits.
Qed.

Lemma task_flag_wake_pending_result : forall task bits result,
  flag_pend_pending_result_task (task_flag_wake task bits result).
Proof.
  intros task bits result Hpending; exfalso.
  exact (proj2 (task_flag_wake_clears_registration task bits result) Hpending).
Qed.

Lemma task_event_wake_phase_pending_result : forall task phase kind message result,
  phase <> PendFlag -> task_linked_wait_phase task phase ->
  flag_pend_pending_result_task (task_event_wake_single task kind message result).
Proof.
  intros task phase kind message result Hdifferent Hphase Hpending; exfalso.
  change (task_non_suspension_bits (task_clear_pending_status task.(stat) kind) = task_pend_mask PendFlag)
    in Hpending.
  destruct Hphase as [Hbits|[Hbits Htimeout]].
  - rewrite (task_status_single_of_mask task.(stat) (Some phase) Hbits) in Hpending.
    destruct phase; try contradiction; destruct kind; destruct (task_is_suspended task.(stat)); discriminate.
  - rewrite (task_status_single_of_mask task.(stat) None Hbits) in Hpending.
    destruct kind; destruct (task_is_suspended task.(stat)); discriminate.
Qed.

Lemma event_wait_entry_task_phase : forall sg tasks eid event slot old kind,
  event_wait_entry_consistency sg tasks eid event ->
  event_type_to_pend_type event.(eventType) = Some kind -> In slot event.(waitList) ->
  tasks.(inUsedTaskStates) slot = Some old -> task_linked_wait_phase old kind.
Proof.
  intros sg tasks eid event slot old kind [Horder Hphase] Hkind Hin Hold.
  rewrite Hkind in Hphase.
  destruct (Hphase slot Hin) as [task [Htask [Hptr [Hmulti Htaskphase]]]].
  assert (task = old) by congruence; subst task; exact Htaskphase.
Qed.

Lemma tick_task_preserves_pending_result : forall task,
  flag_pend_pending_result_task task -> flag_pend_pending_result_task (tick_task_update task).
Proof.
  intros task Hpending; unfold tick_task_update.
  destruct (Z.eqb task.(dly) 0); [exact Hpending|].
  destruct (Z.eqb (task.(dly) - 1) 0); [|exact Hpending].
  intro Hbits; exfalso.
  exact (task_status_after_timeout_no_single_pending task.(stat) PendFlag ltac:(discriminate) Hbits).
Qed.

Lemma kernel_wake_c_segment_pending_result_fields : forall sg entry before input returned after output origin,
  WakeComponent.kernel_wake_c_segment sg entry before input returned after output ->
  flag_pend_pending_result_at_origin origin entry -> flag_pend_pending_result_at_origin origin returned.
Proof.
  intros sg entry before input returned after output origin Hsegment Hfields.
  destruct Hsegment as
    [entry pointer waiter old bits result c_result schedule checkpoint frame before after Hpre Hstep Hpost
    |entry eid event slot old kind message result c_result frame before after Hevent Hentry Hpre Hpost
    |entry slot old frame before after Hold Hpre Hpost].
  - destruct (flag_task_rdy_result _ _ _ _ _ _ _ Hstep)
      as [actual [flags [found [Hunlink [Hfound [-> Hschedule]]]]]].
    eapply flag_pend_pending_result_fields_task_update with (replacement := task_flag_wake found bits result);
      [exact Hfound|reflexivity|intros _; apply task_flag_wake_pending_result|reflexivity|exact Hfields].
  - destruct Hentry as [_ [_ [_ [_ [Hentry [Hhead Hold]]]]]].
    destruct (event_type_to_pend_type event.(eventType)) as [phase|] eqn:Hphase.
    + assert (Hin : In slot event.(waitList)).
      { destruct event.(waitList) as [|head tail]; [discriminate|].
        cbn in Hhead; injection Hhead as ->; simpl; auto. }
      assert (Hnotflag : phase <> PendFlag)
        by (destruct event.(eventType); cbn in Hphase; congruence).
      pose proof (event_wait_entry_task_phase sg entry.(TskState) eid event slot old phase
        Hentry Hphase Hin Hold) as Htaskphase.
      eapply flag_pend_pending_result_fields_task_update with (replacement := task_event_wake_single old kind message result);
        [exact Hold|reflexivity|intros _; eapply task_event_wake_phase_pending_result; eassumption
        |reflexivity|exact Hfields].
    + destruct Hentry as [Horder Hempty]; rewrite Hphase in Hempty; rewrite Hempty in Hhead; discriminate.
  - eapply flag_pend_pending_result_fields_task_update with (slot := slot) (old := old)
      (replacement := tick_task_update old).
    + exact Hold.
    + unfold tick_task_update; destruct (Z.eqb old.(dly) 0); reflexivity.
    + apply tick_task_preserves_pending_result.
    + rewrite (tick_task_step_task_state_eq sg slot old entry Hold); reflexivity.
    + exact Hfields.
Qed.

Lemma event_task_rdy_pending_result_fields : forall sg entry eid kind message priority returned origin,
  event_task_rdy sg entry eid kind message PendOK = Some (priority, returned) ->
  flag_pend_pending_result_at_origin origin entry -> flag_pend_pending_result_at_origin origin returned.
Proof.
  intros sg entry eid kind message priority returned origin Hstep Hfields; unfold event_task_rdy in Hstep.
  destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
  destruct (entry.(TskState).(prioTbl) (event_wait_priority entry.(TskState) event)) as [| |slot]; try discriminate.
  destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
  injection Hstep as Hp Hreturned; subst returned.
  eapply flag_pend_pending_result_fields_task_update with (replacement := task_event_wake_single old kind message PendOK);
    [exact Hold|reflexivity|intros _ _; reflexivity|reflexivity|exact Hfields].
Qed.

Lemma task_suspend_state_preserves_pending_result_fields : forall entry slot node origin,
  entry.(TskState).(inUsedTaskStates) slot = Some node ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin (task_suspend_state entry slot node).
Proof.
  intros entry slot node origin Hnode Hfields.
  eapply flag_pend_pending_result_fields_task_update with (replacement := task_suspend node);
    [exact Hnode|reflexivity|apply task_suspend_preserves_pending_result|reflexivity|exact Hfields].
Qed.

Lemma task_suspend_step_preserves_pending_result_fields : forall sg request priority entry result self returned origin,
  task_suspend_step sg request priority entry result self returned ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin returned.
Proof.
  intros sg request priority entry result self returned origin Hstep Hfields.
  destruct (TaskSuspendActualC.task_suspend_step_state_cases _ _ _ _ _ _ _ Hstep)
    as [->|[slot [node [Hnode ->]]]]; [exact Hfields|].
  eapply task_suspend_state_preserves_pending_result_fields; eassumption.
Qed.

Lemma kernel_status_c_source_preserves_pending_result_fields : forall sg entry returned origin,
  StatusComponent.kernel_status_c_source sg entry returned ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin returned.
Proof.
  intros sg entry returned origin Hsource Hfields; destruct Hsource.
  - destruct H as [cid [current [_ [_ [_ Hstep]]]]].
    destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg priority current))).
    + destruct Hstep as [_ ->]; exact Hfields.
    + destruct Hstep as [_ ->]; exact Hfields.
    + destruct Hstep as [old [Hold [_ ->]]].
      eapply task_suspend_state_preserves_pending_result_fields; eassumption.
  - destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority).
    + destruct Hstep as [_ ->]; exact Hfields.
    + destruct Hstep as [_ ->]; exact Hfields.
    + destruct Hstep as [old [Hold Hstep]]; destruct (task_is_suspended old.(stat)).
      * destruct Hstep as [_ ->].
        eapply flag_pend_pending_result_fields_task_update with (replacement := task_resume old);
          [exact Hold|reflexivity|apply task_resume_preserves_pending_result|reflexivity|exact Hfields].
      * destruct Hstep as [_ ->]; exact Hfields.
  - destruct H as [event [fields [_ [_ [_ ->]]]]]; destruct (Z.ltb 0 fields.(semCount)); exact Hfields.
Qed.

Lemma kernel_task_creation_c_source_preserves_pending_result_fields : forall sg entry returned origin,
  CreationComponent.kernel_task_creation_c_source sg entry returned ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin returned.
Proof.
  intros sg entry returned origin Hsource Hfields.
  apply (flag_pend_pending_result_fields_used_eq origin entry returned); [|exact Hfields].
  destruct Hsource; try reflexivity.
  - unfold task_create_critical in H; destruct (Z.ltb 0 entry.(IntrState).(intNesting)).
    + destruct H as [_ ->]; reflexivity.
    + destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority);
        destruct Hstep as [_ ->]; reflexivity.
  - destruct H2 as [_ ->]; reflexivity.
Qed.

Lemma kernel_event_creation_c_source_preserves_pending_result_fields : forall entry returned origin,
  EventCreationComponent.kernel_event_creation_c_source entry returned ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin returned.
Proof.
  intros entry returned origin Hsource Hfields.
  pose proof (kernel_event_creation_c_source_other_fields entry returned Hsource) as [Htasks _].
  eapply flag_pend_pending_result_fields_used_eq; [rewrite Htasks; reflexivity|exact Hfields].
Qed.

Lemma kernel_queue_creation_c_source_preserves_pending_result_fields : forall sg entry returned origin,
  QueueCreationComponent.kernel_queue_creation_c_source sg entry returned ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin returned.
Proof.
  intros sg entry returned origin Hsource Hfields.
  pose proof (kernel_queue_creation_c_source_other_fields sg entry returned Hsource) as [Htasks _].
  eapply flag_pend_pending_result_fields_used_eq; [rewrite Htasks; reflexivity|exact Hfields].
Qed.

Lemma task_delete_primitive_c_segment_preserves_pending_result_fields :
  forall environment critical sg entry before input stopped returned after output origin,
  DeleteComponent.task_delete_primitive_c_segment environment critical sg
    entry before input stopped returned after output ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin returned.
Proof.
  intros environment critical sg entry before input stopped returned after output origin Hstep Hfields.
  destruct Hstep; exact Hfields.
Qed.

Lemma flag_pend_task_primitive_c_step_preserves_pending_result_fields :
  forall environment critical sg entry before input stopped returned after output origin,
  PrimitiveComponent.flag_pend_task_primitive_c_step environment critical sg
    entry before input stopped returned after output ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin returned.
Proof.
  intros environment critical sg entry before input stopped returned after output origin Hstep Hfields.
  destruct Hstep; try exact Hfields.
  destruct H; exact Hfields.
Qed.

Lemma mutex_priority_task_preserves_pending_result_fields : forall task priority,
  flag_pend_pending_result_task task ->
  flag_pend_pending_result_task (mutex_priority_task task priority).
Proof. intros task priority Hfields; exact Hfields. Qed.

Lemma task_change_prio_critical_preserves_pending_result_fields :
  forall sg requested priority entry result returned origin,
  task_change_prio_critical sg requested priority entry result returned ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin returned.
Proof.
  intros sg requested priority entry result returned origin Hcode Hfields.
  unfold task_change_prio_critical in Hcode.
  destruct (entry.(TskState).(prioTbl) priority).
  - destruct Hcode as [selected [Hselection Hstep]].
    unfold task_change_prio_selected_effect in Hstep.
    destruct (Z.eqb selected sg.(osLowestPrio)).
    + destruct Hstep as [_ ->]; exact Hfields.
    + destruct (entry.(TskState).(prioTbl) selected).
      * destruct Hstep as [_ ->]; exact Hfields.
      * destruct Hstep as [_ ->]; exact Hfields.
      * destruct Hstep as [old [Hold [_ ->]]].
        eapply flag_pend_pending_result_fields_task_update with (replacement := mutex_priority_task old priority);
          [exact Hold|reflexivity|apply mutex_priority_task_preserves_pending_result_fields|reflexivity|exact Hfields].
  - destruct Hcode as [_ ->]; exact Hfields.
  - destruct Hcode as [_ ->]; exact Hfields.
Qed.

Lemma mutex_del_prepare_preserves_pending_result_fields : forall sg mutex entry returned origin,
  mutex_del_prepare sg mutex entry returned ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin returned.
Proof.
  intros sg mutex entry returned origin Hprepare Hfields.
  unfold mutex_del_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [subst returned; exact Hfields|].
  destruct mutex.(mfOwner) as [owner|].
  - destruct Hprepare as [node [priority [Hnode [Hpriority ->]]]].
    unfold mutex_del_owner_priority_state; destruct (Z.eq_dec node.(curPrio) priority).
    + exact Hfields.
    + eapply flag_pend_pending_result_fields_task_update with (replacement := mutex_priority_task node priority);
        [exact Hnode|reflexivity|apply mutex_priority_task_preserves_pending_result_fields|reflexivity|exact Hfields].
  - subst returned; exact Hfields.
Qed.

Lemma mutex_del_broadcast_preserves_pending_result_fields : forall sg eid mutex entry priorities returned origin,
  event_broadcast sg eid PendMutex 0 PendAbort entry priorities returned ->
  mutex_del_wake_state_inv sg eid mutex entry ->
  flag_pend_pending_result_at_origin origin entry -> flag_pend_pending_result_at_origin origin returned.
Proof.
  intros sg eid mutex entry priorities returned origin Hloop.
  induction Hloop as [entry event He Hzero|entry event priority middle priorities returned He Hnonzero Hstep Hloop IH];
    intros Hphase Hfields; [exact Hfields|].
  destruct (mutex_del_wake_decompose sg eid mutex entry event priority middle Hphase He Hnonzero Hstep)
    as [slot [old [Hin [Hold [Hpriority [Hmiddle HphaseMid]]]]]].
  apply IH; [exact HphaseMid|].
  pose proof (mutex_del_wake_state_ranges sg eid mutex entry Hphase) as [Hprofile [Htasks [Hsched Hevents]]].
  destruct Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  assert (Htype : event.(eventType) = OS_EVENT_TYPE_MUTEX).
  { destruct Hphase as [actual [Hactual [Htype Hrest]]]; assert (actual = event) by congruence; subst; exact Htype. }
  pose proof (event_wait_entry_task_phase sg entry.(TskState) eid event slot old PendMutex
    (Hentries eid event He) ltac:(rewrite Htype; reflexivity) Hin Hold) as Hwait.
  rewrite Hmiddle.
  eapply flag_pend_pending_result_fields_task_update with (replacement := task_event_wake_single old PendMutex 0 PendAbort);
    [exact Hold|reflexivity|intros _; eapply task_event_wake_phase_pending_result with (phase := PendMutex); [discriminate|exact Hwait]
    |reflexivity|exact Hfields].
Qed.

Lemma mutex_del_critical_preserves_pending_result_fields : forall sg eid option entry result returned origin,
  CriticalComponent.mutex_del_no_pend_critical_call_guard sg eid entry ->
  mutex_del_critical sg eid option entry result returned ->
  flag_pend_pending_result_at_origin origin entry -> flag_pend_pending_result_at_origin origin returned.
Proof.
  intros sg eid option entry result returned origin
    [known [known_mutex [[Hvalid [Hknown [Hknown_type [Hknown_mutex Huse]]]] Hpointer]]]
    [event [mutex [Hevent [Htype [Hmutex Hstep]]]]] Hfields.
  assert (known = event) by (unfold mutex_query_lookup in Hknown; congruence); subst known.
  assert (known_mutex = mutex) by congruence; subst known_mutex.
  destruct (Z.eq_dec option 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) entry.(TskState)) 0).
    + destruct Hstep as [prepared [Hprepare [-> Hresult]]].
      change (flag_pend_pending_result_at_origin origin prepared).
      eapply mutex_del_prepare_preserves_pending_result_fields; eassumption.
    + destruct Hstep as [-> Hresult]; exact Hfields.
  - destruct (Z.eq_dec option 1).
    + destruct Hstep as [prepared [priorities [drained [Hprepare [Hbroadcast [-> Hresult]]]]]].
      change (flag_pend_pending_result_at_origin origin drained).
      eapply mutex_del_broadcast_preserves_pending_result_fields; [exact Hbroadcast| |].
      * eapply mutex_del_prepare_under_owner_use; eassumption.
      * eapply mutex_del_prepare_preserves_pending_result_fields; eassumption.
    + destruct Hstep as [-> Hresult]; exact Hfields.
Qed.

Lemma kernel_critical_c_source_preserves_pending_result_fields : forall sg call origin,
  CriticalComponent.kernel_critical_c_source sg call ->
  flag_pend_pending_result_at_origin origin (CriticalComponent.kernel_critical_c_entry call) ->
  flag_pend_pending_result_at_origin origin (CriticalComponent.kernel_critical_c_returned call).
Proof.
  intros sg [actual|actual] origin Hsource Hfields; cbn in *.
  - destruct Hsource as [error [Hcritical Hresult]].
    eapply task_change_prio_critical_preserves_pending_result_fields; eassumption.
  - destruct Hsource.
    + destruct H0 as [error [scheduled [Hcritical Hencoding]]].
      eapply mutex_del_critical_preserves_pending_result_fields; eassumption.
    + exact Hfields.
Qed.

Lemma mutex_pend_inherit_step_preserves_pending_result_fields :
  forall sg entry owner node base waiter ceiling returned origin,
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_pend_inherit_step sg entry owner node base waiter ceiling returned ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin returned.
Proof.
  intros sg entry owner node base waiter ceiling returned origin Hnode Hstep Hfields.
  unfold mutex_pend_inherit_step in Hstep.
  destruct (mutex_pend_inherit_action sg.(osPrioMutexCeilDis) base node.(curPrio) waiter ceiling).
  - subst returned; exact Hfields.
  - subst returned; exact Hfields.
  - destruct Hstep as [events [Hevents ->]].
    eapply flag_pend_pending_result_fields_task_update with (replacement := mutex_priority_task node ceiling);
      [exact Hnode|reflexivity|apply mutex_priority_task_preserves_pending_result_fields|reflexivity|exact Hfields].
Qed.

Lemma mutex_post_prepare_preserves_pending_result_fields : forall sg mutex owner entry returned origin,
  mutex_post_prepare sg mutex owner entry returned ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin returned.
Proof.
  intros sg mutex owner entry returned origin Hprepare Hfields.
  unfold mutex_post_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [subst returned; exact Hfields|].
  destruct Hprepare as [node [priority [Hnode [Hpriority ->]]]].
  unfold mutex_post_owner_priority_state; destruct (Z.eq_dec node.(curPrio) priority).
  - exact Hfields.
  - eapply flag_pend_pending_result_fields_task_update with (replacement := mutex_priority_task node priority);
      [exact Hnode|reflexivity|apply mutex_priority_task_preserves_pending_result_fields|reflexivity|exact Hfields].
Qed.

Lemma mutex_post_critical_preserves_pending_result_fields : forall sg eid caller entry result schedule returned origin,
  mutex_post_critical sg eid caller entry result schedule returned ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin returned.
Proof.
  intros sg eid caller entry result schedule returned origin Hcritical Hfields; destruct Hcritical.
  - exact Hfields.
  - change (flag_pend_pending_result_at_origin origin prepared).
    eapply mutex_post_prepare_preserves_pending_result_fields; eassumption.
  - change (flag_pend_pending_result_at_origin origin woken).
    eapply event_task_rdy_pending_result_fields; [eassumption|].
    eapply mutex_post_prepare_preserves_pending_result_fields; eassumption.
Qed.

Lemma flag_pend_pending_result_fields_task_commit : forall origin before after priority invocation node,
  flag_pend_pending_result_task node ->
  after.(TskState).(inUsedTaskStates) =
    (task_commit before.(TskState) priority invocation node).(inUsedTaskStates) ->
  flag_pend_pending_result_at_origin origin before ->
  flag_pend_pending_result_at_origin origin after.
Proof.
  intros [|slot generation] before after priority invocation node Hclear Hused Hfields; [exact I|].
  unfold flag_pend_pending_result_at_origin in *.
  intros task Htask Hg; rewrite Hused in Htask.
  cbn [task_commit inUsedTaskStates] in Htask.
  destruct (Z.eq_dec slot node.(taskID)).
  - injection Htask as Htask; subst task; exact Hclear.
  - destruct before.(TskState).(tcbListHead) as [head|].
    + destruct (before.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
      destruct (Z.eq_dec slot head); injection Htask as Htask; subst task;
        exact (Hfields old eq_refl Hg).
    + exact (Hfields task Htask Hg).
Qed.

Lemma task_create_stack_publication_preserves_pending_result_fields : forall sg publication entry origin,
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin (task_create_stack_publication_state sg publication entry).
Proof.
  intros sg publication entry origin Hfields.
  eapply flag_pend_pending_result_fields_task_commit with
    (priority := (task_create_stack_publication_args publication).(initPrio))
    (invocation := publication.(stack_publication_invocation))
    (node := task_tcb_init_commit_node (task_create_stack_publication_args publication)
      publication.(stack_publication_acquired) publication.(stack_publication_slot)
      publication.(stack_publication_image));
    [intros _; reflexivity
    |reflexivity|exact Hfields].
Qed.

Lemma flag_pend_pending_result_fields_task_recycle : forall sg origin before after tid priority node name,
  after.(TskState).(inUsedTaskStates) =
    (task_recycle sg before.(TskState) tid priority node name).(inUsedTaskStates) ->
  flag_pend_pending_result_at_origin origin before ->
  flag_pend_pending_result_at_origin origin after.
Proof.
  intros sg [|slot generation] before after tid priority node name Hused Hfields; [exact I|].
  unfold flag_pend_pending_result_at_origin in *.
  intros task Htask Hg; rewrite Hused in Htask.
  cbn [task_recycle inUsedTaskStates] in Htask; unfold task_unlink_used_map in Htask.
  destruct (Z.eq_dec slot tid); [discriminate|].
  destruct (before.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
  injection Htask as Htask; subst task; exact (Hfields old eq_refl Hg).
Qed.

Lemma task_delete_prepare_after_unlink_preserves_pending_result_fields :
  forall entry after tid old updated origin,
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  after.(TskState).(inUsedTaskStates) = entry.(TskState).(inUsedTaskStates) ->
  updated.(taskGeneration) = old.(taskGeneration) ->
  (flag_pend_pending_result_task old -> flag_pend_pending_result_task updated) ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin (task_delete_prepare_after_unlink after tid updated).
Proof.
  intros entry after tid old updated origin Hold Hused Hgen Hclear Hfields.
  eapply flag_pend_pending_result_fields_task_update with (before := entry)
    (replacement := task_prepare_delete updated).
  - exact Hold.
  - exact Hgen.
  - intros _ _; reflexivity.
  - cbn [task_delete_prepare_after_unlink replace_SchedS replace_TskS TskState glob_task_set_usedtask
      inUsedTaskStates]; rewrite Hused; reflexivity.
  - exact Hfields.
Qed.

Lemma task_delete_prepare_single_wait_preserves_pending_result_fields :
  forall entry tid old prepared loan origin,
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  task_delete_prepare_single_wait entry tid old = Some (prepared, loan) ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin prepared.
Proof.
  intros entry tid old prepared loan origin Hold Hstep Hfields.
  unfold task_delete_prepare_single_wait in Hstep.
  destruct old.(eventPtr) as [eid|].
  - destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
    cbn [task_set_event_ptr tcbFlagNode] in Hstep.
    destruct (Z.eqb old.(tcbFlagNode) 0).
    + injection Hstep as Hprepared Hloan; subst prepared.
      eapply task_delete_prepare_after_unlink_preserves_pending_result_fields;
        [exact Hold|reflexivity|reflexivity| |exact Hfields].
      intro Hzero; exact Hzero.
    + destruct (flag_unlink_node entry.(FlagState) old.(tcbFlagNode)) as [[waiter flags]|]; [|discriminate].
      injection Hstep as Hprepared Hloan; subst prepared.
      eapply task_delete_prepare_after_unlink_preserves_pending_result_fields;
        [exact Hold|reflexivity|reflexivity| |exact Hfields].
      intro Hzero; exact Hzero.
  - destruct (Z.eqb old.(tcbFlagNode) 0).
    + injection Hstep as Hprepared Hloan; subst prepared.
      eapply task_delete_prepare_after_unlink_preserves_pending_result_fields;
        [exact Hold|reflexivity|reflexivity|intros H; exact H|exact Hfields].
    + destruct (flag_unlink_node entry.(FlagState) old.(tcbFlagNode)) as [[waiter flags]|]; [|discriminate].
      injection Hstep as Hprepared Hloan; subst prepared.
      eapply task_delete_prepare_after_unlink_preserves_pending_result_fields;
        [exact Hold|reflexivity|reflexivity| |exact Hfields].
      intro Hzero; exact Hzero.
Qed.

Lemma task_delete_own_c_segment_preserves_pending_result_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  DeleteComponent.task_delete_own_c_segment environment critical sg observer observer_origin
    entry before input stopped returned after output ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin
    Hstep Hfields; destruct Hstep.
  - destruct H0 as [Hprep Hinput Houtput].
    destruct Hprep as [[Hlookup [Hselected [Hlive Hpointer]]] [Hprepare Hrunning]].
    change (flag_pend_pending_result_at_origin origin inputs.(DeleteComponent.delete_capture_prepared)).
    eapply task_delete_prepare_single_wait_preserves_pending_result_fields;
      [exact (proj2 (task_delete_table_lookup_live _ _ _ _ Hlive))|exact Hprepare|exact Hfields].
  - pose (inputs := capture.(DeleteComponent.delete_save_restore).(DeleteComponent.delete_restore_inputs)).
    exact (flag_pend_pending_result_fields_task_recycle inputs.(DeleteComponent.delete_capture_globals) origin
      capture.(DeleteComponent.delete_save_resumed) (DeleteComponent.task_delete_capture_cut capture)
      inputs.(DeleteComponent.delete_capture_tid) inputs.(DeleteComponent.delete_capture_priority)
      (task_delete_prepared_node inputs.(DeleteComponent.delete_capture_node))
      inputs.(DeleteComponent.delete_capture_name) eq_refl Hfields).
Qed.

Lemma kernel_builtin_c_segment_preserves_pending_result_fields :
  forall environment critical local sg entry before returned after input output origin,
  BuiltinComponent.kernel_builtin_c_segment environment critical local sg
    entry before returned after input output ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin returned.
Proof.
  intros environment critical local sg entry before returned after input output origin Hstep Hfields.
  destruct Hstep.
  - destruct operation; exact Hfields.
  - apply task_create_stack_publication_preserves_pending_result_fields; exact Hfields.
  - pose proof (BuiltinComponent.kernel_irq_transfer_c_completion_source environment critical sg
      handler saved entry transfer frame before after H) as Hsource.
    eapply flag_pend_pending_result_fields_used_eq; [|exact Hfields].
    exact (proj1 (BuiltinComponent.os_int_exit_configured_transfer_state_frame
      environment sg handler entry transfer Hsource)).
Qed.

Lemma task_install_c_step_preserves_pending_result_fields :
  forall environment local sg entry before input stopped returned after output origin,
  InstallComponent.task_install_c_step environment local sg
    entry before input stopped returned after output ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin returned.
Proof.
  intros environment local sg entry before input stopped returned after output origin Hstep Hfields.
  destruct Hstep; eapply flag_pend_pending_result_fields_used_eq; [reflexivity|exact Hfields].
Qed.

Lemma task_suspend_masked_c_step_preserves_pending_result_fields :
  forall environment critical sg entry before input stopped returned after output origin,
  TaskSuspendMaskedC.task_suspend_masked_c_step environment critical sg
    entry before input stopped returned after output ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin returned.
Proof.
  intros environment critical sg entry before input stopped returned after output origin Hstep Hfields.
  destruct Hstep as [saved_local caller saved call frame before after [[Hread Hcode] Hinput Houtput]].
  eapply task_suspend_step_preserves_pending_result_fields; eassumption.
Qed.

Lemma kernel_program_c_step_preserves_pending_result_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  kernel_program_c_step environment critical sg observer observer_origin
    entry before input stopped returned after output ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin
    Hstep Hfields; destruct Hstep.
  - destruct H as [Hcompletion [Hphysical [Hsource Hpacket]]].
    eapply kernel_critical_c_source_preserves_pending_result_fields; eassumption.
  - eapply kernel_builtin_c_segment_preserves_pending_result_fields; eassumption.
  - eapply task_install_c_step_preserves_pending_result_fields; eassumption.
  - eapply kernel_wake_c_segment_pending_result_fields; [exact H|exact Hfields].
  - destruct H as [Hsource Hinput Houtput].
    eapply kernel_status_c_source_preserves_pending_result_fields; eassumption.
  - eapply kernel_task_creation_c_source_preserves_pending_result_fields;
      [eapply CreationComponent.kernel_task_creation_c_segment_source; exact H|exact Hfields].
  - eapply kernel_event_creation_c_source_preserves_pending_result_fields;
      [eapply EventCreationComponent.kernel_event_creation_c_segment_source; exact H|exact Hfields].
  - eapply kernel_queue_creation_c_source_preserves_pending_result_fields;
      [eapply QueueCreationComponent.kernel_queue_creation_c_segment_source; exact H|exact Hfields].
  - destruct H as [[Hnode [Hforeign Hsource]] Hinput Houtput].
    eapply mutex_pend_inherit_step_preserves_pending_result_fields; eassumption.
  - destruct H as [[Hcaller Hsource] Hinput Houtput].
    eapply mutex_post_critical_preserves_pending_result_fields; eassumption.
  - eapply task_delete_primitive_c_segment_preserves_pending_result_fields; eassumption.
  - eapply flag_pend_task_primitive_c_step_preserves_pending_result_fields; eassumption.
  - eapply task_delete_own_c_segment_preserves_pending_result_fields; eassumption.
Qed.

Lemma kernel_program_return_c_step_preserves_pending_result_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  SelectedReturnPrimitive.kernel_program_return_c_step environment critical sg observer observer_origin
    entry before input stopped returned after output ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin
    Hstep Hfields; destruct Hstep.
  - eapply kernel_program_c_step_preserves_pending_result_fields; eassumption.
  - destruct (SelectedReturnPrimitive.kernel_selected_return_c_step_state_stop _ _ _ _ _ _ _ _ H)
      as [-> Hstop]; exact Hfields.
  - eapply flag_pend_pending_result_fields_used_eq; [reflexivity|exact Hfields].
  - eapply flag_pend_pending_result_fields_used_eq; [reflexivity|exact Hfields].
Qed.

Lemma kernel_program_selected_c_step_preserves_pending_result_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  SelectedCProgram.kernel_program_selected_c_step environment critical sg observer observer_origin
    entry before input stopped returned after output ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin
    Hstep Hfields; destruct Hstep.
  - eapply kernel_program_return_c_step_preserves_pending_result_fields; eassumption.
  - destruct H.
    eapply flag_pend_pending_result_fields_used_eq; [|exact Hfields].
    exact (proj1 (BuiltinComponent.os_int_exit_configured_transfer_state_frame
      environment sg handler entry transfer source)).
  - eapply task_suspend_masked_c_step_preserves_pending_result_fields; eassumption.
Qed.

Lemma kernel_program_selected_c_sequence_preserves_pending_result_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  kernel_c_sequence
    (SelectedCProgram.kernel_program_selected_c_step environment critical sg observer observer_origin)
    entry before input stopped returned after output ->
  flag_pend_pending_result_at_origin origin entry ->
  flag_pend_pending_result_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin Hrun.
  induction Hrun; intro Hfields.
  - exact Hfields.
  - eapply kernel_program_selected_c_step_preserves_pending_result_fields; eassumption.
  - apply IHHrun2, IHHrun1, Hfields.
  - apply IHHrun, Hfields.
Qed.

End FlagWaitingPendingResult.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import FlagWaitingRecovery FlagWaitingSuccessor FlagWaitingNodeInclusion FlagWaitingMultiPointer.
Import FlagWaitingLinkedReturn FlagWaitingPendingResult.
Import FlagPendSchedulerResources PrimitiveComponent PendPhaseCandidate.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagWaitingPendingReturn.

Lemma flag_waiting_linked_initial_pending_result : forall original node call state waiter,
  state.(FlagState).(flagWaitNodes) node = Some waiter ->
  flag_active_waiting_registration original node call state -> flag_pend_wait_outcome original node state ->
  flag_pend_pending_result_at_origin original.(os_sched_call_origin) state.
Proof.
  intros original node call state waiter Hnode
    [task [[Hsame [Horigin [Hlookup [Hgen [Hactive Hclear]]]]] Hpointer]]
    [observed [Hobserved Houtcome]].
  assert (observed = task) by congruence; subst observed; rewrite Hnode in Houtcome.
  rewrite Horigin; intros next Hnext Hg; assert (next = task) by congruence; subst next.
  intro Hpending; destruct Houtcome as [[Hbits Hok]|[Hclearbits Htimeout]]; [exact Hok|].
  change (task_non_suspension_bits task.(stat) = 32) in Hpending; lia.
Qed.

(** Unlike the ready-only corollary, this also retains a still-pending
    caller after the real no-selection IRQ return. Both possible linked
    outcomes are produced from the same writer history. *)
Lemma flag_waiting_linked_current_observations :
  forall sg entry current original call returned node old_waiter waiter,
  flag_active_waiting_registration original node call entry ->
  entry.(FlagState).(flagWaitNodes) node = Some old_waiter ->
  flag_wait_nodes_included entry current ->
  current.(FlagState).(flagWaitNodes) node = Some waiter ->
  UCOS2_state_inv sg current ->
  flag_pend_zero_multi_at_origin original.(os_sched_call_origin) current ->
  flag_pend_pending_result_at_origin original.(os_sched_call_origin) current ->
  task_tcb_init_stack_same_call returned original -> kernel_call_task_source returned current ->
  flag_active_waiting_registration original node returned current /\
  flag_pend_wait_outcome original node current.
Proof.
  intros sg entry current original call returned node old_waiter waiter
    [old [Hold Hlink]] Hentry Hnodes Hcurrent Hvalid Hmulti Hpending Hsame Hsource.
  pose proof (kernel_call_task_source_current_at returned current Hsource) as [Hcur [task [Hlookup Hgen]]].
  destruct Hsame as [Hinv [Horigin Hstack]]; rewrite Hstack in Hlookup, Hgen.
  rewrite Hentry in Hlink; destruct Hlink as [Haddr [Hkey Hpointer]].
  destruct (flag_wait_nodes_included_identity entry current node old_waiter waiter Hnodes Hentry Hcurrent)
    as [Haddr' [Hslot Hgeneration]].
  assert (Hkey' : task_stack_key original.(os_sched_call_stack) =
      (waiter.(flagTask), waiter.(flagTaskGeneration))) by (rewrite Hslot, Hgeneration; exact Hkey).
  unfold task_stack_key in Hkey'; injection Hkey' as Hslot' Hgen'.
  assert (Hcross : task_flag_waiter_consistency sg current.(TskState) current.(FlagState))
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, cross_module_consistency in Hvalid; tauto).
  destruct (proj1 Hcross node waiter Hcurrent)
    as [Hnonzero [linked [Hlinked [Hlinked_gen [Hflag [Htcb [Hphase [Hevent Hlist]]]]]]]].
  rewrite <- Hslot' in Hlinked; assert (linked = task) by congruence; subst linked.
  destruct Hsource as [Hrunning [Hactive Hsource_current]].
  rewrite Horigin, Hstack in Hrunning; rewrite Hinv, Horigin in Hactive.
  rewrite Hrunning in Hmulti, Hpending.
  pose proof (Hmulti task Hlookup Hgen) as Harray.
  pose proof (Hpending task Hlookup Hgen) as Hresult.
  split.
  - exists task; split.
    + unfold flag_active_task_fields, flag_active_event_clear.
      exact (conj (conj Hinv (conj Horigin Hstack))
        (conj Hrunning (conj Hlookup (conj Hgen (conj Hactive (conj Hevent (conj Hlist Harray))))))).
    + rewrite Hcurrent; split; [congruence|split; [unfold task_stack_key; congruence|exact Hflag]].
  - exists task; split; [exact Hlookup|rewrite Hcurrent].
    destruct Hphase as [Hbits|Htimeout].
    + left; split; [exact Hbits|apply Hresult; exact Hbits].
    + right; exact Htimeout.
Qed.

Lemma flag_pend_linked_selected_sequence_current_receipt :
  forall environment critical sg observer origin original call returned node entry old_waiter
    before input stopped current waiter after (frame : Assertion),
  entry.(FlagState).(flagWaitNodes) node = Some old_waiter ->
  current.(FlagState).(flagWaitNodes) node = Some waiter ->
  kernel_c_sequence
    (SelectedCProgram.kernel_program_selected_c_step environment critical sg observer origin)
    entry before input stopped current after
    (UCOS2_fields_inv sg current ** flag_pend_waiting_receipt sg original node call entry ** frame) ->
  task_tcb_init_stack_same_call returned original -> kernel_call_task_source returned current ->
  (UCOS2_fields_inv sg current ** flag_pend_waiting_receipt sg original node returned current ** frame) after.
Proof.
  intros environment critical sg observer origin original call returned node entry old_waiter
    before input stopped current waiter after frame Hentry Hcurrent Hrun Hsame Hsource.
  pose proof (proj2 (SelectedCProgram.kernel_program_selected_c_sequence_resources
    environment critical sg observer origin entry before input stopped current after _ Hrun)) as Howned.
  assert (Hprojection :
    UCOS2_fields_inv sg current ** flag_pend_waiting_receipt sg original node call entry ** frame |--
    coq_prop (UCOS2_state_inv sg current /\ flag_active_waiting_registration original node call entry /\
      flag_pend_wait_outcome original node entry)).
  { unfold UCOS2_fields_inv, flag_pend_waiting_receipt, flag_active_waiting; entailer!. }
  destruct (Hprojection after Howned) as [Hvalid [Hregistration Houtcome]].
  pose proof (kernel_program_selected_c_sequence_nodes_included _ _ _ _ _ _ _ _ _ _ _ _ Hrun) as Hnodes.
  pose proof (kernel_program_selected_c_sequence_preserves_zero_multi_fields environment critical sg observer origin
    entry before input stopped current after _ original.(os_sched_call_origin) Hrun
      (flag_waiting_registration_zero_multi_fields original node call entry Hregistration)) as Hmulti.
  pose proof (kernel_program_selected_c_sequence_preserves_pending_result_fields environment critical sg observer origin
    entry before input stopped current after _ original.(os_sched_call_origin) Hrun
      (flag_waiting_linked_initial_pending_result original node call entry old_waiter Hentry Hregistration Houtcome))
    as Hpending.
  destruct (flag_waiting_linked_current_observations sg entry current original call returned node old_waiter waiter
    Hregistration Hentry Hnodes Hcurrent Hvalid Hmulti Hpending Hsame Hsource) as [Hregistration' Houtcome'].
  assert (Hrecover :
    UCOS2_fields_inv sg current ** flag_pend_waiting_receipt sg original node call entry ** frame |--
    UCOS2_fields_inv sg current ** flag_pend_waiting_receipt sg original node returned current ** frame).
  { unfold flag_pend_waiting_receipt, flag_active_waiting, flag_pend_sched_node_fields_rep.
    rewrite Hentry, Hcurrent; entailer!. }
  exact (Hrecover after Howned).
Qed.

End FlagWaitingPendingReturn.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import CriticalComponent PrimitiveComponent PendPhaseCandidate.
Import SelectedIRQWrapperCompletion SelectedIRQWrapperSegment OSIntExitReturnedC.
Import FlagWaitingRecovery FlagWaitingSuccessor FlagWaitingNodeInclusion.
Import FlagWaitingMultiPointer FlagWaitingPendingResult.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagWaitingReturnedFields.

(** These leaves retain the original C completion and physical restore.
    Their field projections cover the complete Returned prefix, including
    the counter and the non-switching selector stores. *)
Lemma irq_wrapper_c_step_waiting_fields :
  forall environment sg entry before input stopped current after output,
  irq_wrapper_c_step environment sg entry before input stopped current after output ->
  flag_wait_nodes_included entry current /\
  (forall origin,
    (flag_pend_zero_multi_at_origin origin entry -> flag_pend_zero_multi_at_origin origin current) /\
    (flag_pend_pending_result_at_origin origin entry -> flag_pend_pending_result_at_origin origin current) /\
    (flag_pend_detached_fields_at_origin origin entry -> flag_pend_detached_fields_at_origin origin current)).
Proof.
  intros until output; intro Hstep; destruct Hstep; split.
  - apply flag_wait_nodes_included_flags_eq; reflexivity.
  - intros origin; repeat split; intro Hfields; exact Hfields.
Qed.

Lemma os_int_exit_returned_c_step_waiting_fields :
  forall environment critical sg entry before input stopped current after output,
  os_int_exit_returned_c_step environment critical sg entry before input stopped current after output ->
  flag_wait_nodes_included entry current /\
  (forall origin,
    (flag_pend_zero_multi_at_origin origin entry -> flag_pend_zero_multi_at_origin origin current) /\
    (flag_pend_pending_result_at_origin origin entry -> flag_pend_pending_result_at_origin origin current) /\
    (flag_pend_detached_fields_at_origin origin entry -> flag_pend_detached_fields_at_origin origin current)).
Proof.
  intros until output; intro Hstep.
  pose proof (proj1 (os_int_exit_returned_c_step_task_fields _ _ _ _ _ _ _ _ _ _ Hstep)) as Hused.
  split.
  - apply flag_wait_nodes_included_flags_eq; destruct Hstep;
      destruct observed.(SchedState).(isRunning); reflexivity.
  - intros origin; repeat split; intro Hfields.
    + eapply flag_pend_zero_multi_fields_used_eq; [exact Hused|exact Hfields].
    + eapply flag_pend_pending_result_fields_used_eq; [exact Hused|exact Hfields].
    + eapply flag_pend_detached_fields_used_eq; [exact Hused|exact Hfields].
Qed.

Lemma irq_wrapper_c_step_waiting_receipt_equiv :
  forall environment sg entry before input stopped current after output,
  irq_wrapper_c_step environment sg entry before input stopped current after output ->
  forall original node call,
  flag_pend_waiting_receipt sg original node call entry --||--
  flag_pend_waiting_receipt sg original node call current.
Proof.
  intros until output; intro Hstep; destruct Hstep; intros reference pointer call;
    split; intros heap Hreceipt; exact Hreceipt.
Qed.

Lemma os_int_exit_returned_c_step_waiting_receipt_equiv :
  forall environment critical sg entry before input stopped current after output,
  os_int_exit_returned_c_step environment critical sg entry before input stopped current after output ->
  forall reference node call,
  flag_pend_waiting_receipt sg reference node call entry --||--
  flag_pend_waiting_receipt sg reference node call current.
Proof.
  intros until output; intro Hstep; destruct Hstep; intros reference pointer call;
    destruct observed.(SchedState).(isRunning);
    split; intros heap Hreceipt; exact Hreceipt.
Qed.

End FlagWaitingReturnedFields.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import CriticalComponent PrimitiveComponent SelectedCProgram SelectedRetirementTransport.
Import SelectedIRQWrapperCompletion SelectedIRQWrapperSegment OSIntExitReturnedC SelectedReturnedCProgram.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module ReturnedLocalSource.

Lemma kernel_program_returned_c_step_preserves_unretired :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_program_returned_c_step environment critical sg observer origin
    state before input stopped current after output ->
  task_unretired_transport state.(TskState) current.(TskState).
Proof.
  intros until output; intro Hstep; destruct Hstep.
  - destruct H.
    + eapply kernel_program_selected_c_step_preserves_unretired; exact H.
    + destruct H; intros invocation Hret; exact Hret.
  - pose proof (proj1 (proj2 (os_int_exit_returned_c_step_task_fields _ _ _ _ _ _ _ _ _ _ H))) as Hlife.
    intros invocation Hret; unfold task_unretired_transport in *; rewrite Hlife; exact Hret.
Qed.

Lemma kernel_program_returned_c_sequence_preserves_unretired :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
    state before input stopped current after output ->
  task_unretired_transport state.(TskState) current.(TskState).
Proof.
  intros until output; intro Hrun; induction Hrun.
  - intros invocation Hret; exact Hret.
  - eapply kernel_program_returned_c_step_preserves_unretired; exact H.
  - intros invocation Hret; apply IHHrun2, IHHrun1; exact Hret.
  - exact IHHrun.
Qed.

(** [current], [node], and the generation are the real terminal reads.
    The same prefix provides invocation registration and unretiredness;
    an arbitrary local observation need not identify the current task. *)
Lemma kernel_program_returned_c_sequence_live_source_from_active :
  forall environment critical sg original initial first_heap input stopped current last_heap output node,
  kernel_c_sequence (kernel_program_returned_c_step environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial first_heap input stopped current last_heap output ->
  task_in_range sg initial.(TskState) ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active initial.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  current.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  current.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) ->
  kernel_call_task_source original current.
Proof.
  intros until node; intros Hrun Hrange Horigin Hactive Hcurrent Hnode Hgen.
  pose proof (task_observer_lifetime_from_active sg initial.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) Hrange Hactive) as Hlife.
  destruct (kernel_program_returned_c_sequence_observer_lifetime _ _ _ _ _ _ _ _ _ _ _ _ Hrun)
    as [Htransport Hstop].
  destruct (Htransport Hlife) as [[Hregistered Hrest] Hback].
  pose proof (kernel_program_returned_c_sequence_preserves_unretired _ _ _ _ _ _ _ _ _ _ _ _ Hrun
    original.(os_sched_call_invocation) (proj1 (proj2 Hactive))) as Hretired.
  split; [exact Horigin|]; split.
  - split; [exact Hregistered|]; split; [exact Hretired|].
    rewrite Horigin; exists node; split; assumption.
  - unfold task_execution_current; rewrite Horigin; exact Hcurrent.
Qed.

Lemma kernel_program_returned_irq_wrapper_source_from_active :
  forall environment critical sg original initial first_heap input stopped state before
    local suspended receipt node handler frame after
    (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap input stopped state before
      (irq_wrapper_c_input environment sg state local suspended receipt handler frame)),
  task_in_range sg initial.(TskState) ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active initial.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  irq_wrapper_c_completion environment sg state local suspended receipt original node handler frame before after ->
  kernel_call_task_source (armv7a_continuation_resumed_call suspended original)
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)).
Proof.
  intros environment critical sg original initial first_heap input stopped state before
    local suspended receipt node handler frame after run Hrange Horigin Hactive Hcomplete.
  destruct Hcomplete as [Hbinding Hcall Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hinput Hrestore].
  assert (Hstack : original.(os_sched_call_stack) = suspended.(armv7a_continuation_stack)).
  { pose proof (proj2 Hbinding) as H; rewrite Hcall in H; exact H. }
  assert (Hsource : kernel_call_task_source original state).
  { eapply kernel_program_returned_c_sequence_live_source_from_active;
      [exact run|exact Hrange|exact Horigin|exact Hactive| | |]; rewrite Hstack; eassumption. }
  destruct Hsource as [_ [Hreturned Hcur]].
  unfold kernel_call_task_source, armv7a_continuation_resumed_call; simpl.
  split; [rewrite <- Hstack; exact Horigin|]; split; [exact Hreturned|].
  unfold task_execution_current; rewrite Horigin.
  change (state.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot)).
  rewrite Hstack; exact Hcurrent.
Qed.

Lemma kernel_program_returned_os_int_exit_source_from_active :
  forall environment critical sg original initial first_heap input stopped observed read_heap observation_frame
    state before local suspended receipt node handler frame middle after
    (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap input stopped state before
      (os_int_exit_returned_c_input environment sg state local suspended receipt handler frame)),
  task_in_range sg initial.(TskState) ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active initial.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
    state local suspended receipt original node handler frame before middle after ->
  kernel_call_task_source (armv7a_continuation_resumed_call suspended original)
    (os_int_exit_wrapper_restored_state
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state)
      suspended.(armv7a_continuation_stack)).
Proof.
  intros environment critical sg original initial first_heap input stopped observed read_heap observation_frame
    state before local suspended receipt node handler frame middle after run Hrange Horigin Hactive Hcomplete.
  pose proof (os_int_exit_returned_current _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete) as Hcurrent.
  pose proof (os_int_exit_returned_node _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete) as Hnode.
  pose proof (os_int_exit_returned_generation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete) as Hgen.
  assert (Hstack : original.(os_sched_call_stack) = suspended.(armv7a_continuation_stack)).
  { pose proof (proj2 (os_int_exit_returned_binding _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete)) as H.
    rewrite (os_int_exit_returned_saved_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete) in H; exact H. }
  assert (Hsource : kernel_call_task_source original state).
  { eapply kernel_program_returned_c_sequence_live_source_from_active;
      [exact run|exact Hrange|exact Horigin|exact Hactive| | |]; rewrite Hstack; eassumption. }
  destruct Hsource as [_ [Hreturned Hcur]].
  destruct (os_int_exit_checkpoint_current_frame observed.(SchedState).(isRunning) state)
    as [Hcur_eq [Hpriority Hrunning]].
  pose proof (proj1 (os_int_exit_checkpoint_frame observed.(SchedState).(isRunning) state)) as Htasks.
  unfold kernel_call_task_source, armv7a_continuation_resumed_call; simpl.
  split; [rewrite <- Hstack; exact Horigin|]; split.
  - change (task_invocation_active
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state).(TskState)
      original.(os_sched_call_invocation) original.(os_sched_call_origin)).
    rewrite Htasks; exact Hreturned.
  - unfold task_execution_current; rewrite Horigin.
    change ((os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state).(SchedState).(curTaskID) =
      Some original.(os_sched_call_stack).(stackLeaseSlot)).
    rewrite Hcur_eq, Hstack; exact Hcurrent.
Qed.

End ReturnedLocalSource.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import CriticalComponent PrimitiveComponent SelectedIRQWrapperSegment SelectedReturnedCProgram.
Import FlagWaitingSuccessor FlagWaitingDetachedSequence FlagWaitingNodeInclusion.
Import FlagWaitingMultiPointer FlagWaitingPendingResult FlagWaitingReturnedFields.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagWaitingReturnedSequence.

Lemma kernel_program_returned_c_step_nodes_included :
  forall environment critical sg observer origin entry before input stopped current after output,
  kernel_program_returned_c_step environment critical sg observer origin
    entry before input stopped current after output -> flag_wait_nodes_included entry current.
Proof.
  intros until output; intro Hstep; destruct Hstep.
  - destruct H.
    + eapply kernel_program_selected_c_step_nodes_included; exact H.
    + exact (proj1 (irq_wrapper_c_step_waiting_fields _ _ _ _ _ _ _ _ _ H)).
  - exact (proj1 (os_int_exit_returned_c_step_waiting_fields _ _ _ _ _ _ _ _ _ _ H)).
Qed.

Lemma kernel_program_returned_c_step_waiting_fields :
  forall environment critical sg observer origin entry before input stopped current after output,
  kernel_program_returned_c_step environment critical sg observer origin
    entry before input stopped current after output -> forall observed_origin,
  (flag_pend_zero_multi_at_origin observed_origin entry -> flag_pend_zero_multi_at_origin observed_origin current) /\
  (flag_pend_pending_result_at_origin observed_origin entry -> flag_pend_pending_result_at_origin observed_origin current) /\
  (flag_pend_detached_fields_at_origin observed_origin entry -> flag_pend_detached_fields_at_origin observed_origin current).
Proof.
  intros until output; intro Hstep; destruct Hstep; intro observed_origin.
  - destruct H.
    + repeat split; intro Hfields.
      * eapply kernel_program_selected_c_step_preserves_zero_multi_fields; eassumption.
      * eapply kernel_program_selected_c_step_preserves_pending_result_fields; eassumption.
      * eapply kernel_program_selected_c_step_preserves_detached_fields; eassumption.
    + exact (proj2 (irq_wrapper_c_step_waiting_fields _ _ _ _ _ _ _ _ _ H) observed_origin).
  - exact (proj2 (os_int_exit_returned_c_step_waiting_fields _ _ _ _ _ _ _ _ _ _ H) observed_origin).
Qed.

Lemma kernel_program_returned_c_sequence_waiting_fields :
  forall environment critical sg observer origin entry before input stopped current after output,
  kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
    entry before input stopped current after output ->
  flag_wait_nodes_included entry current /\
  (forall observed_origin,
    (flag_pend_zero_multi_at_origin observed_origin entry -> flag_pend_zero_multi_at_origin observed_origin current) /\
    (flag_pend_pending_result_at_origin observed_origin entry -> flag_pend_pending_result_at_origin observed_origin current) /\
    (flag_pend_detached_fields_at_origin observed_origin entry -> flag_pend_detached_fields_at_origin observed_origin current)).
Proof.
  intros until output; intro Hrun; induction Hrun.
  - split; [apply flag_wait_nodes_included_refl|intros observed_origin; repeat split; auto].
  - split.
    + eapply kernel_program_returned_c_step_nodes_included; exact H.
    + eapply kernel_program_returned_c_step_waiting_fields; exact H.
  - destruct IHHrun1 as [Hnodes1 Hfields1], IHHrun2 as [Hnodes2 Hfields2].
    split; [eapply flag_wait_nodes_included_trans; eassumption|].
    intros observed_origin; destruct (Hfields1 observed_origin) as [Hm1 [Hp1 Hd1]].
    destruct (Hfields2 observed_origin) as [Hm2 [Hp2 Hd2]]; repeat split; auto.
  - exact IHHrun.
Qed.

End FlagWaitingReturnedSequence.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import CriticalComponent PrimitiveComponent PendPhaseCandidate SelectedReturnedCProgram.
Import SelectedIRQWrapperCompletion OSIntExitReturnedC ReturnedLocalSource.
Import FlagWaitingRecovery FlagWaitingSuccessor FlagWaitingReceiptReindex.
Import FlagWaitingNodeInclusion FlagWaitingMultiPointer FlagWaitingPendingResult.
Import FlagWaitingLinkedReturn FlagWaitingPendingReturn FlagWaitingReturnedFields FlagWaitingReturnedSequence.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagWaitingReturnedOwner.

Lemma flag_waiting_registration_call_activity : forall original call node state,
  flag_active_waiting_registration original node call state ->
  call.(os_sched_call_origin) = RunningInvocation call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) /\
  task_invocation_active state.(TskState) call.(os_sched_call_invocation) call.(os_sched_call_origin).
Proof.
  intros original call node state [task [[Hsame [Horigin [Hnode [Hgeneration [Hactive Hclear]]]]] Hpointer]].
  destruct Hsame as [Hinv [Hcall_origin Hstack]].
  split; [rewrite Hcall_origin, Hstack; exact Horigin|rewrite Hinv, Hcall_origin; exact Hactive].
Qed.

Lemma flag_waiting_detached_registration_fields : forall original node call state,
  flag_active_waiting_registration original node call state ->
  flag_pend_wait_outcome original node state ->
  state.(FlagState).(flagWaitNodes) node = None ->
  flag_pend_detached_fields_at_origin original.(os_sched_call_origin) state.
Proof.
  intros original node call state
    [task [[Hsame [Horigin [Hlookup [Hgen [Hactive Hclear]]]]] Hpointer]]
    [observed [Hobserved Houtcome]] Hnone.
  assert (observed = task) by congruence; subst observed.
  rewrite Hnone in Hpointer, Houtcome; rewrite Horigin.
  intros next Hnext Hg; assert (next = task) by congruence; subst next.
  unfold flag_pend_detached_task_fields; tauto.
Qed.

(** A single-cut consequence, used only after the actual run has produced
    the three field transports and its terminal reads have produced source.
    The left case is an observed still-public node. The right case is the
    detached receipt published by the literal Post/Del call and Next store.
    An old linked emp receipt is never turned into a detached node owner. *)
Lemma flag_waiting_receipt_from_returned_observations :
  forall sg original node call initial returned current,
  flag_active_waiting_registration original node call initial ->
  flag_pend_wait_outcome original node initial ->
  UCOS2_state_inv sg current -> flag_wait_nodes_included initial current ->
  (flag_pend_zero_multi_at_origin original.(os_sched_call_origin) initial ->
    flag_pend_zero_multi_at_origin original.(os_sched_call_origin) current) ->
  (flag_pend_pending_result_at_origin original.(os_sched_call_origin) initial ->
    flag_pend_pending_result_at_origin original.(os_sched_call_origin) current) ->
  (flag_pend_detached_fields_at_origin original.(os_sched_call_origin) initial ->
    flag_pend_detached_fields_at_origin original.(os_sched_call_origin) current) ->
  ((exists waiter, current.(FlagState).(flagWaitNodes) node = Some waiter) \/
    initial.(FlagState).(flagWaitNodes) node = None) ->
  task_tcb_init_stack_same_call returned original -> kernel_call_task_source returned current ->
  flag_pend_waiting_receipt sg original node call initial |--
  flag_pend_waiting_receipt sg original node returned current.
Proof.
  intros sg original node call initial returned current Hregistration Houtcome Hvalid Hnodes
    Hmulti Hpending Hdetached Hcase Hsame Hsource.
  destruct Hcase as [[waiter Hnode]|Hnone].
  - destruct (Hnodes node waiter Hnode) as [previous [Hprevious Hidentity]].
    destruct (flag_waiting_linked_current_observations sg initial current original call returned node previous waiter
      Hregistration Hprevious Hnodes Hnode Hvalid
      (Hmulti (flag_waiting_registration_zero_multi_fields _ _ _ _ Hregistration))
      (Hpending (flag_waiting_linked_initial_pending_result _ _ _ _ _ Hprevious Hregistration Houtcome))
      Hsame Hsource) as [Hregistration' Houtcome'].
    unfold flag_pend_waiting_receipt, flag_active_waiting, flag_pend_sched_node_fields_rep.
    rewrite Hprevious, Hnode; entailer!.
  - eapply flag_pend_detached_receipt_current;
      [exact Hnone|eapply flag_wait_nodes_included_absent; eassumption
      |apply Hdetached; eapply flag_waiting_detached_registration_fields; eassumption
      |exact Hsame|exact Hsource].
Qed.

(** The old receipt is read from the very returned owner. Its registration
    is not an extra callee Require. The terminal descriptor generates the
    current TaskSource and same-call facts inside this proof. *)
Lemma kernel_program_returned_irq_wrapper_waiting_receipt :
  forall environment critical sg original pointer call initial first_heap input stopped state before
    local suspended node handler frame after
    (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin))
      initial first_heap input stopped state before
      (irq_wrapper_c_input environment sg state local suspended
        (flag_pend_waiting_receipt sg original pointer call initial) handler frame)),
  task_in_range sg initial.(TskState) ->
  ((exists waiter, state.(FlagState).(flagWaitNodes) pointer = Some waiter) \/
    initial.(FlagState).(flagWaitNodes) pointer = None) ->
  irq_wrapper_c_completion environment sg state local suspended
    (flag_pend_waiting_receipt sg original pointer call initial) call node handler frame before after ->
  (irq_wrapper_c_output environment sg state local suspended
    (flag_pend_waiting_receipt sg original pointer (armv7a_continuation_resumed_call suspended call)
      (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)))
    call handler frame) after.
Proof.
  intros environment critical sg original pointer call initial first_heap input stopped state before
    local suspended node handler frame after run Hrange Hcase Hcomplete.
  pose proof (proj2 (irq_wrapper_c_completion_resources _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete)) as Houtput.
  assert (Hextract : irq_wrapper_c_output environment sg state local suspended
      (flag_pend_waiting_receipt sg original pointer call initial) call handler frame |--
    coq_prop (UCOS2_state_inv sg (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) /\
      flag_active_waiting_registration original pointer call initial /\ flag_pend_wait_outcome original pointer initial)).
  { unfold irq_wrapper_c_output, flag_source_save_input, kernel_continuation_call_closed,
      kernel_continuation_inv, UCOS2_fields_inv,
      flag_pend_waiting_receipt, flag_active_waiting; entailer!. }
  destruct (Hextract after Houtput) as [Hvalid [Hregistration Houtcome]].
  destruct (flag_waiting_registration_call_activity _ _ _ _ Hregistration) as [Horigin Hactive].
  pose proof (kernel_program_returned_irq_wrapper_source_from_active environment critical sg call
    initial first_heap input stopped state before local suspended
    (flag_pend_waiting_receipt sg original pointer call initial) node handler frame after
    run Hrange Horigin Hactive Hcomplete) as Hreturned.
  pose proof (irq_wrapper_c_completion_normal_return _ _ _ _ _ _ _ _ _ _ _ _ initial Hcomplete Horigin) as Hnormal.
  assert (Hsame : task_tcb_init_stack_same_call (armv7a_continuation_resumed_call suspended call) original).
  { destruct Hregistration as [task [[Hsame0 Hrest] Hpointer]].
    destruct Hsame0 as [Hi [Ho Hs]]; destruct (proj1 Hnormal) as [Hi' [Ho' Hs']].
    unfold task_tcb_init_stack_same_call; repeat split; congruence. }
  destruct (kernel_program_returned_c_sequence_waiting_fields _ _ _ _ _ _ _ _ _ _ _ _ run)
    as [Hnodes Hfields].
  destruct (Hfields original.(os_sched_call_origin)) as [Hmulti [Hpending Hdetached]].
  assert (Hrecover : flag_pend_waiting_receipt sg original pointer call initial |--
    flag_pend_waiting_receipt sg original pointer (armv7a_continuation_resumed_call suspended call)
      (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack))).
  { eapply flag_waiting_receipt_from_returned_observations;
      [exact Hregistration|exact Houtcome|exact Hvalid|exact Hnodes
      |exact Hmulti|exact Hpending|exact Hdetached|exact Hcase|exact Hsame|exact Hreturned]. }
  match type of Houtput with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold irq_wrapper_c_output, flag_source_save_input.
    sep_apply_l_atomic Hrecover; entailer!. }
  exact (Hclose after Houtput).
Qed.

(** This branch additionally executes OSIntExit's real counter/selector
    prefix on [before -> middle] before the same wrapper restore. *)
Lemma kernel_program_returned_os_int_exit_waiting_receipt :
  forall environment critical sg original pointer call initial first_heap input stopped observed read_heap observation_frame
    state before local suspended node handler frame middle after
    (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin))
      initial first_heap input stopped state before
      (os_int_exit_returned_c_input environment sg state local suspended
        (flag_pend_waiting_receipt sg original pointer call initial) handler frame)),
  task_in_range sg initial.(TskState) ->
  ((exists waiter, state.(FlagState).(flagWaitNodes) pointer = Some waiter) \/
    initial.(FlagState).(flagWaitNodes) pointer = None) ->
  os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame state local suspended
    (flag_pend_waiting_receipt sg original pointer call initial) call node handler frame before middle after ->
  (irq_wrapper_c_output environment sg (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state)
    local suspended
    (flag_pend_waiting_receipt sg original pointer (armv7a_continuation_resumed_call suspended call)
      (os_int_exit_wrapper_restored_state (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state)
        suspended.(armv7a_continuation_stack))) call handler (unmap_table_rep sg ** frame)) after.
Proof.
  intros environment critical sg original pointer call initial first_heap input stopped observed read_heap observation_frame
    state before local suspended node handler frame middle after run Hrange Hcase Hcomplete.
  pose proof (proj2 (os_int_exit_returned_c_completion_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete)) as Houtput.
  pose proof (os_int_exit_returned_c_completion_wrapper _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete) as Hwrapper.
  assert (Hextract : irq_wrapper_c_output environment sg
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) local suspended
      (flag_pend_waiting_receipt sg original pointer call initial) call handler (unmap_table_rep sg ** frame) |--
    coq_prop (UCOS2_state_inv sg (os_int_exit_wrapper_restored_state
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) suspended.(armv7a_continuation_stack)) /\
      flag_active_waiting_registration original pointer call initial /\ flag_pend_wait_outcome original pointer initial)).
  { unfold irq_wrapper_c_output, flag_source_save_input, kernel_continuation_call_closed,
      kernel_continuation_inv, UCOS2_fields_inv,
      flag_pend_waiting_receipt, flag_active_waiting; entailer!. }
  destruct (Hextract after Houtput) as [Hvalid [Hregistration Houtcome]].
  destruct (flag_waiting_registration_call_activity _ _ _ _ Hregistration) as [Horigin Hactive].
  pose proof (kernel_program_returned_os_int_exit_source_from_active environment critical sg call
    initial first_heap input stopped observed read_heap observation_frame state before local suspended
    (flag_pend_waiting_receipt sg original pointer call initial) node handler frame middle after
    run Hrange Horigin Hactive Hcomplete) as Hreturned.
  pose proof (irq_wrapper_c_completion_normal_return _ _ _ _ _ _ _ _ _ _ _ _ initial Hwrapper Horigin) as Hnormal.
  assert (Hsame : task_tcb_init_stack_same_call (armv7a_continuation_resumed_call suspended call) original).
  { destruct Hregistration as [task [[Hsame0 Hrest] Hpointer]].
    destruct Hsame0 as [Hi [Ho Hs]]; destruct (proj1 Hnormal) as [Hi' [Ho' Hs']].
    unfold task_tcb_init_stack_same_call; repeat split; congruence. }
  destruct (kernel_program_returned_c_sequence_waiting_fields _ _ _ _ _ _ _ _ _ _ _ _ run)
    as [Hnodes Hfields].
  assert (Hstep : os_int_exit_returned_c_step environment critical sg state before
    (os_int_exit_returned_c_input environment sg state local suspended
      (flag_pend_waiting_receipt sg original pointer call initial) handler frame) false
    (os_int_exit_wrapper_restored_state (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state)
      suspended.(armv7a_continuation_stack)) after
    (irq_wrapper_c_output environment sg (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state)
      local suspended (flag_pend_waiting_receipt sg original pointer call initial) call handler
      (unmap_table_rep sg ** frame))).
  { econstructor; exact Hcomplete. }
  destruct (os_int_exit_returned_c_step_waiting_fields _ _ _ _ _ _ _ _ _ _ Hstep)
    as [Hnodes' Hfields'].
  destruct (Hfields original.(os_sched_call_origin)) as [Hmulti [Hpending Hdetached]].
  destruct (Hfields' original.(os_sched_call_origin)) as [Hmulti' [Hpending' Hdetached']].
  assert (Hcase' : (exists waiter, (os_int_exit_wrapper_restored_state
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state)
      suspended.(armv7a_continuation_stack)).(FlagState).(flagWaitNodes) pointer = Some waiter) \/
    initial.(FlagState).(flagWaitNodes) pointer = None).
  { destruct observed.(SchedState).(isRunning); exact Hcase. }
  assert (Hrecover : flag_pend_waiting_receipt sg original pointer call initial |--
    flag_pend_waiting_receipt sg original pointer (armv7a_continuation_resumed_call suspended call)
      (os_int_exit_wrapper_restored_state (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state)
        suspended.(armv7a_continuation_stack))).
  { eapply flag_waiting_receipt_from_returned_observations;
      [exact Hregistration|exact Houtcome|exact Hvalid
      |eapply flag_wait_nodes_included_trans; eassumption
      |auto|auto|auto|exact Hcase'|exact Hsame|exact Hreturned]. }
  match type of Houtput with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold irq_wrapper_c_output, flag_source_save_input.
    sep_apply_l_atomic Hrecover; entailer!. }
  exact (Hclose after Houtput).
Qed.

End FlagWaitingReturnedOwner.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module ReturnedIdleSource.
Import PrimitiveComponent SelectedCProgram SelectedIdleComposition.
Import SelectedIRQWrapperCompletion SelectedIRQWrapperSegment SelectedReturnedCProgram OSIntExitReturnedC.

(** Retain the actual named source on the original C branch.  In
    particular the raw Suspend relation is not silently strengthened. *)
Inductive kernel_program_returned_idle_source environment critical sg observer origin :
  forall state before input stopped current after output,
  kernel_program_returned_c_step environment critical sg observer origin
    state before input stopped current after output -> Prop :=
| KernelReturnedIdleSelected : forall state before input stopped current after output step,
  kernel_program_selected_idle_source environment critical sg observer origin
    state before input stopped current after output step ->
  kernel_program_returned_idle_source environment critical sg observer origin state before input stopped current after output
    (@KernelProgramReturnedWrapper environment critical sg observer origin state before input stopped current after output
      (@KernelProgramWrapperOriginal environment critical sg observer origin state before input stopped current after output step))
| KernelReturnedIdleWrapper : forall state before input stopped current after output step,
  kernel_program_returned_idle_source environment critical sg observer origin state before input stopped current after output
    (@KernelProgramReturnedWrapper environment critical sg observer origin state before input stopped current after output
      (@KernelProgramWrapperIRQ environment critical sg observer origin state before input stopped current after output step))
| KernelReturnedIdleExit : forall state before input stopped current after output step,
  kernel_program_returned_idle_source environment critical sg observer origin state before input stopped current after output
    (@KernelProgramReturnedExit environment critical sg observer origin state before input stopped current after output step).

Definition kernel_program_returned_sequence_idle_source environment critical sg observer origin
  state before input stopped current after output
  (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
    state before input stopped current after output) : Prop :=
  kernel_c_sequence_has_source (kernel_program_returned_c_step environment critical sg observer origin)
    (kernel_program_returned_idle_source environment critical sg observer origin)
    state before input stopped current after output run.

Lemma kernel_program_returned_idle_source_transport :
  forall environment critical sg observed state before input stopped current after output
    (step : kernel_program_returned_c_step environment critical sg observed.(os_sched_call_invocation)
      observed.(os_sched_call_origin) state before input stopped current after output),
  kernel_program_returned_idle_source environment critical sg observed.(os_sched_call_invocation)
    observed.(os_sched_call_origin) _ _ _ _ _ _ _ step ->
  observed.(os_sched_call_origin) = RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
    observed.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(SchedState).(isRunning) = true -> stopped = false ->
  (task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState)) /\
  (flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current).
Proof.
  intros until step; intros Hsource Horigin Hrunning Hstop; destruct Hsource.
  - eapply kernel_program_selected_idle_source_transport; eassumption.
  - destruct step; split; trivial.
  - eapply os_int_exit_returned_c_step_idle_non_idle; exact step.
Qed.

Lemma kernel_program_returned_sequence_idle_source_transport :
  forall environment critical sg observed state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observed.(os_sched_call_invocation)
      observed.(os_sched_call_origin)) state before input stopped current after output),
  kernel_program_returned_sequence_idle_source environment critical sg observed.(os_sched_call_invocation)
    observed.(os_sched_call_origin) _ _ _ _ _ _ _ run ->
  observed.(os_sched_call_origin) = RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
    observed.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(SchedState).(isRunning) = true -> stopped = false ->
  (task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState)) /\
  (flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current).
Proof.
  intros until run; intros Hsource Horigin.
  induction Hsource; intros Hrunning Hstop.
  - split; trivial.
  - eapply kernel_program_returned_idle_source_transport; eassumption.
  - apply Bool.orb_false_iff in Hstop; destruct Hstop as [Hfirst_stop Hlast_stop].
    destruct (IHHsource1 Hrunning Hfirst_stop) as [Hfirst_idle Hfirst_non_idle].
    assert (Hmiddle_running : middle.(SchedState).(isRunning) = true).
    { rewrite (kernel_program_returned_c_sequence_running environment critical sg
        observed.(os_sched_call_invocation) observed.(os_sched_call_origin) _ _ _ _ _ _ _ first).
      exact Hrunning. }
    destruct (IHHsource2 Hmiddle_running Hlast_stop) as [Hlast_idle Hlast_non_idle].
    split; auto.
  - apply IHHsource; assumption.
Qed.

(** Initial activity is supplied by the concrete saved receipt, and final
    activity is supplied by the actual terminal descriptor.  A temporary
    non-current/blocked cut is allowed. *)
Lemma kernel_program_returned_completed_idle_non_idle :
  forall environment critical sg original returned state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin)) state before input stopped current after output),
  kernel_program_returned_sequence_idle_source environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) _ _ _ _ _ _ _ run ->
  task_in_range sg state.(TskState) ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  state.(SchedState).(isRunning) = true ->
  kernel_call_normal_return original state returned current -> kernel_call_task_source returned current ->
  stopped = false /\
  (task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState)) /\
  (flag_pend_non_idle_at sg original state -> flag_pend_non_idle_at sg returned current).
Proof.
  intros until run; intros Hsource Hrange Horigin Hactive Hrunning Hnormal Hreturned.
  assert (Hstop : stopped = false).
  { destruct stopped; [|reflexivity].
    exfalso; eapply (proj2 (kernel_program_returned_c_sequence_observer_lifetime
      _ _ _ _ _ _ _ _ _ _ _ _ run)).
    - eapply task_observer_lifetime_from_active; eassumption.
    - reflexivity.
    - eapply kernel_call_same_return_observer_active; [exact (proj1 Hnormal)|exact Hreturned]. }
  destruct (kernel_program_returned_sequence_idle_source_transport environment critical sg original
    _ _ _ _ _ _ _ run Hsource Horigin Hrunning Hstop) as [Hidle Hnonidle].
  split; [exact Hstop|]; split; [exact Hidle|].
  intro Hinitial; specialize (Hnonidle Hinitial).
  unfold flag_pend_non_idle_at in *.
  rewrite (proj2 (proj2 (proj1 Hnormal))); exact Hnonidle.
Qed.

End ReturnedIdleSource.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module ReturnedIRQEntryReceipts.
Import PrimitiveComponent PendPhaseCandidate OSIntExitCCallEnvelope ReturnedIRQEntryResources FlagWaitingRecovery.

Section ActualEntry.
Context (environment : TaskStackCallEnvironment) (sg : StableGlobVars)
  (initial : UCOS2_Verify_State) (node : TaskAbstractState) (handler : OsIntExitCallContext)
  (suspended : Armv7aContinuation) (publication : nat) (local : Armv7aContinuation -> Assertion)
  (frame : Assertion) (before saved_heap body_heap : model).
Context (entry : os_int_exit_first_level_entry_c_completion environment sg initial node handler suspended
  publication local frame before saved_heap body_heap).
Let parked := armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
  suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments).

Lemma os_int_exit_entry_task_lookup : forall slot old,
  initial.(TskState).(inUsedTaskStates) slot = Some old ->
  exists current, parked.(TskState).(inUsedTaskStates) slot = Some current /\
    (current = old \/ current = task_set_saved_sp old suspended.(armv7a_continuation_sp)).
Proof.
  intros slot old Hlookup.
  pose proof (os_int_exit_first_level_entry_task_fields _ _ _ _ _ _ _ _ _ _ _ _ entry) as Htasks.
  unfold parked; rewrite Htasks.
  cbn [glob_task_set_parked_stacks glob_task_set_usedtask inUsedTaskStates].
  destruct (Z.eqb slot handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot)) eqn:Heq.
  - apply Z.eqb_eq in Heq; subst slot.
    pose proof (os_int_exit_entry_node _ _ _ _ _ _ _ _ _ _ _ _ entry) as Hnode.
    assert (old = node) by congruence; subst old.
    exists (task_set_saved_sp node suspended.(armv7a_continuation_sp)); split; [reflexivity|right; reflexivity].
  - exists old; split; [exact Hlookup|left; reflexivity].
Qed.

Lemma os_int_exit_entry_flag_state : parked.(FlagState) = initial.(FlagState).
Proof.
  unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
    armv7a_irq_entry_counter_state, os_sched_save_current_sp.
  rewrite (os_int_exit_entry_running _ _ _ _ _ _ _ _ _ _ _ _ entry).
  cbn [replace_IntrS TskState].
  rewrite (os_int_exit_entry_node _ _ _ _ _ _ _ _ _ _ _ _ entry).
  reflexivity.
Qed.

Lemma os_int_exit_entry_fresh_registration : forall original call,
  flag_active_fresh_registration original call initial ->
  flag_active_fresh_registration original call parked.
Proof.
  intros original call [old [[Hsame [Horigin [Hlookup [Hgen [Hactive Hclear]]]]] Hzero]].
  pose proof (os_int_exit_first_level_entry_preserves_active _ _ _ _ _ _ _ _ _ _ _ _ entry
    original.(os_sched_call_invocation) original.(os_sched_call_origin) Hactive) as Hactive_after.
  destruct (os_int_exit_entry_task_lookup _ _ Hlookup) as [current [Hcurrent Hshape]].
  exists current; destruct Hshape as [-> | ->];
    (split; [exact (conj Hsame (conj Horigin (conj Hcurrent (conj Hgen (conj Hactive_after Hclear)))))|exact Hzero]).
Qed.

Lemma os_int_exit_entry_first_observation : forall mode original original_state call,
  flag_pend_first_observation mode original original_state call initial |--
  flag_pend_first_observation mode original original_state call parked.
Proof.
  intros mode original original_state call heap [Hregistration Hempty]; split; [|exact Hempty].
  intro Hcondition; apply os_int_exit_entry_fresh_registration, Hregistration, Hcondition.
Qed.

Lemma os_int_exit_entry_fresh_observation : forall original call,
  flag_pend_fresh_observation original call initial |--
  flag_pend_fresh_observation original call parked.
Proof.
  intros original call heap [Hregistration Hempty]; split; [|exact Hempty].
  apply os_int_exit_entry_fresh_registration; exact Hregistration.
Qed.

Lemma os_int_exit_entry_waiting_receipt : forall original pointer call,
  flag_pend_waiting_receipt sg original pointer call initial |--
  flag_pend_waiting_receipt sg original pointer call parked.
Proof.
  intros original pointer call heap [Houtcome [Hregistration Hnode_owner]].
  assert (Hregistration_after : flag_active_waiting_registration original pointer call parked).
  { destruct Hregistration as [old [[Hsame [Horigin [Hlookup [Hgen [Hactive Hclear]]]]] Hpointer]].
    pose proof (os_int_exit_first_level_entry_preserves_active _ _ _ _ _ _ _ _ _ _ _ _ entry
      original.(os_sched_call_invocation) original.(os_sched_call_origin) Hactive) as Hactive_after.
    destruct (os_int_exit_entry_task_lookup _ _ Hlookup) as [current [Hcurrent Hshape]].
    exists current; rewrite os_int_exit_entry_flag_state.
    destruct Hshape as [-> | ->];
      (split; [exact (conj Hsame (conj Horigin (conj Hcurrent (conj Hgen (conj Hactive_after Hclear)))))|exact Hpointer]). }
  split.
  - destruct Houtcome as [old [Hlookup Hresult]].
    destruct (os_int_exit_entry_task_lookup _ _ Hlookup) as [current [Hcurrent Hshape]].
    exists current; rewrite os_int_exit_entry_flag_state.
    split; [exact Hcurrent|]. destruct Hshape as [-> | ->]; exact Hresult.
  - split; [exact Hregistration_after|].
    unfold flag_pend_sched_node_fields_rep in *; rewrite os_int_exit_entry_flag_state; exact Hnode_owner.
Qed.

End ActualEntry.
End ReturnedIRQEntryReceipts.

Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module ReturnedIRQEntryReceiptEquality.
Import PrimitiveComponent PendPhaseCandidate OSIntExitCCallEnvelope
  ReturnedIRQEntryResources ReturnedIRQEntryReceipts FlagWaitingRecovery.

Section ActualEntry.
Context (environment : TaskStackCallEnvironment) (sg : StableGlobVars)
  (initial : UCOS2_Verify_State) (node : TaskAbstractState) (handler : OsIntExitCallContext)
  (suspended : Armv7aContinuation) (publication : nat) (local : Armv7aContinuation -> Assertion)
  (frame : Assertion) (before saved_heap body_heap : model).
Context (entry : os_int_exit_first_level_entry_c_completion environment sg initial node handler suspended
  publication local frame before saved_heap body_heap).
Let parked := armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
  suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments).

Lemma os_int_exit_entry_task_lookup_inverse : forall slot current,
  parked.(TskState).(inUsedTaskStates) slot = Some current ->
  exists old, initial.(TskState).(inUsedTaskStates) slot = Some old /\
    (current = old \/ current = task_set_saved_sp old suspended.(armv7a_continuation_sp)).
Proof.
  intros slot current Hlookup.
  pose proof (os_int_exit_first_level_entry_task_fields _ _ _ _ _ _ _ _ _ _ _ _ entry) as Htasks.
  fold parked in Htasks; rewrite Htasks in Hlookup.
  cbn [glob_task_set_parked_stacks glob_task_set_usedtask inUsedTaskStates] in Hlookup.
  destruct (Z.eqb slot handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot)) eqn:Heq.
  - apply Z.eqb_eq in Heq; subst slot. injection Hlookup as Hequal; subst current.
    exists node; split; [exact (os_int_exit_entry_node _ _ _ _ _ _ _ _ _ _ _ _ entry)|right; reflexivity].
  - exists current; split; [exact Hlookup|left; reflexivity].
Qed.

Lemma os_int_exit_entry_active_inverse : forall invocation origin,
  task_invocation_active parked.(TskState) invocation origin ->
  task_invocation_active initial.(TskState) invocation origin.
Proof.
  intros invocation origin [Hregistered [Hretired Hlive]].
  pose proof (os_int_exit_first_level_entry_task_fields _ _ _ _ _ _ _ _ _ _ _ _ entry) as Htasks.
  fold parked in Htasks; rewrite Htasks in Hregistered, Hretired.
  split; [exact Hregistered|]. split; [exact Hretired|].
  destruct origin as [|slot generation]; [exact I|].
  destruct Hlive as [current [Hlookup Hgeneration]].
  destruct (os_int_exit_entry_task_lookup_inverse _ _ Hlookup) as [old [Hinitial Hshape]].
  exists old; split; [exact Hinitial|].
  destruct Hshape as [-> | ->]; exact Hgeneration.
Qed.

Lemma os_int_exit_entry_waiting_receipt_inverse : forall original pointer call,
  flag_pend_waiting_receipt sg original pointer call parked |--
  flag_pend_waiting_receipt sg original pointer call initial.
Proof.
  intros original pointer call heap [Houtcome [Hregistration Hnode_owner]].
  pose proof (os_int_exit_entry_flag_state _ _ _ _ _ _ _ _ _ _ _ _ entry) as Hflags.
  fold parked in Hflags.
  assert (Hregistration_initial : flag_active_waiting_registration original pointer call initial).
  { destruct Hregistration as [current [[Hsame [Horigin [Hlookup [Hgen [Hactive Hclear]]]]] Hpointer]].
    pose proof (os_int_exit_entry_active_inverse _ _ Hactive) as Hactive_initial.
    destruct (os_int_exit_entry_task_lookup_inverse _ _ Hlookup) as [old [Hinitial Hshape]].
    exists old. rewrite Hflags in Hpointer.
    destruct Hshape as [-> | ->];
      (split; [exact (conj Hsame (conj Horigin (conj Hinitial (conj Hgen (conj Hactive_initial Hclear)))))|exact Hpointer]). }
  split.
  - destruct Houtcome as [current [Hlookup Hresult]].
    destruct (os_int_exit_entry_task_lookup_inverse _ _ Hlookup) as [old [Hinitial Hshape]].
    exists old; rewrite Hflags in Hresult.
    split; [exact Hinitial|]. destruct Hshape as [-> | ->]; exact Hresult.
  - split; [exact Hregistration_initial|].
    unfold flag_pend_sched_node_fields_rep in *; rewrite Hflags in Hnode_owner; exact Hnode_owner.
Qed.

(** This equality is derived from the actual entry's field update. It
    transports a receipt interpretation without changing its heap or any
    of the saved execution/source witnesses. *)
Lemma os_int_exit_entry_waiting_receipt_eq : forall original pointer call,
  flag_pend_waiting_receipt sg original pointer call initial =
  flag_pend_waiting_receipt sg original pointer call parked.
Proof.
  intros original pointer call; apply functional_extensionality; intro heap.
  apply propositional_extensionality; split.
  - exact (os_int_exit_entry_waiting_receipt _ _ _ _ _ _ _ _ _ _ _ _ entry original pointer call heap).
  - exact (os_int_exit_entry_waiting_receipt_inverse original pointer call heap).
Qed.
End ActualEntry.
End ReturnedIRQEntryReceiptEquality.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module ReturnedIRQEntryIdle.
Import PrimitiveComponent OSIntExitCCallEnvelope ReturnedIRQEntryReceipts.

Section ActualEntry.
Context (environment : TaskStackCallEnvironment) (sg : StableGlobVars)
  (initial : UCOS2_Verify_State) (node : TaskAbstractState) (handler : OsIntExitCallContext)
  (suspended : Armv7aContinuation) (publication : nat) (local : Armv7aContinuation -> Assertion)
  (frame : Assertion) (before saved_heap body_heap : model).
Context (entry : os_int_exit_first_level_entry_c_completion environment sg initial node handler suspended
  publication local frame before saved_heap body_heap).
Let parked := armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
  suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments).

Lemma os_int_exit_entry_preserves_idle_ready :
  task_idle_ready sg initial.(TskState) -> task_idle_ready sg parked.(TskState).
Proof.
  intros [idle [old [Hlookup [Hpriority Hready]]]].
  destruct (os_int_exit_entry_task_lookup _ _ _ _ _ _ _ _ _ _ _ _ entry idle old Hlookup)
    as [current [Hcurrent Hshape]].
  exists idle, current; split; [exact Hcurrent|].
  destruct Hshape as [-> | ->]; split; assumption.
Qed.

Lemma os_int_exit_entry_preserves_non_idle : forall call,
  flag_pend_non_idle_at sg call initial -> flag_pend_non_idle_at sg call parked.
Proof.
  intros call [old [Hlookup [Hgeneration Hpriority]]].
  destruct (os_int_exit_entry_task_lookup _ _ _ _ _ _ _ _ _ _ _ _ entry
    call.(os_sched_call_stack).(stackLeaseSlot) old Hlookup) as [current [Hcurrent Hshape]].
  exists current; split; [exact Hcurrent|].
  destruct Hshape as [-> | ->]; split; assumption.
Qed.

End ActualEntry.
End ReturnedIRQEntryIdle.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import CriticalComponent PrimitiveComponent PendPhaseCandidate SelectedReturnedCProgram.
Import SelectedIRQWrapperCompletion OSIntExitReturnedC ReturnedLocalSource.
Import FlagWaitingRecovery FlagWaitingSuccessor FlagWaitingReceiptReindex.
Import FlagWaitingNodeInclusion FlagWaitingMultiPointer FlagWaitingPendingResult.
Import FlagWaitingLinkedReturn FlagWaitingPendingReturn FlagWaitingReturnedFields FlagWaitingReturnedSequence.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module ReturnedWaitingConsequence.
Import FlagWaitingReturnedOwner.

Lemma kernel_program_returned_os_int_exit_waiting_receipt_consequence :
  forall environment critical sg original pointer call initial first_heap input stopped observed read_heap observation_frame
    state before local suspended node handler frame middle after
    (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin))
      initial first_heap input stopped state before
      (os_int_exit_returned_c_input environment sg state local suspended
        (flag_pend_waiting_receipt sg original pointer call initial) handler frame)),
  task_in_range sg initial.(TskState) ->
  ((exists waiter, state.(FlagState).(flagWaitNodes) pointer = Some waiter) \/
    initial.(FlagState).(flagWaitNodes) pointer = None) ->
  os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame state local suspended
    (flag_pend_waiting_receipt sg original pointer call initial) call node handler frame before middle after ->
  irq_wrapper_c_output environment sg (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state)
    local suspended (flag_pend_waiting_receipt sg original pointer call initial) call handler
    (unmap_table_rep sg ** frame) |--
  (irq_wrapper_c_output environment sg (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state)
    local suspended
    (flag_pend_waiting_receipt sg original pointer (armv7a_continuation_resumed_call suspended call)
      (os_int_exit_wrapper_restored_state (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state)
        suspended.(armv7a_continuation_stack))) call handler (unmap_table_rep sg ** frame)).
Proof.
  intros environment critical sg original pointer call initial first_heap input stopped observed read_heap observation_frame
    state before local suspended node handler frame middle after run Hrange Hcase Hcomplete.
  pose proof (proj2 (os_int_exit_returned_c_completion_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete)) as Houtput.
  pose proof (os_int_exit_returned_c_completion_wrapper _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete) as Hwrapper.
  assert (Hextract : irq_wrapper_c_output environment sg
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) local suspended
      (flag_pend_waiting_receipt sg original pointer call initial) call handler (unmap_table_rep sg ** frame) |--
    coq_prop (UCOS2_state_inv sg (os_int_exit_wrapper_restored_state
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) suspended.(armv7a_continuation_stack)) /\
      flag_active_waiting_registration original pointer call initial /\ flag_pend_wait_outcome original pointer initial)).
  { unfold irq_wrapper_c_output, flag_source_save_input, kernel_continuation_call_closed,
      kernel_continuation_inv, UCOS2_fields_inv,
      flag_pend_waiting_receipt, flag_active_waiting; entailer!. }
  destruct (Hextract after Houtput) as [Hvalid [Hregistration Houtcome]].
  destruct (flag_waiting_registration_call_activity _ _ _ _ Hregistration) as [Horigin Hactive].
  pose proof (kernel_program_returned_os_int_exit_source_from_active environment critical sg call
    initial first_heap input stopped observed read_heap observation_frame state before local suspended
    (flag_pend_waiting_receipt sg original pointer call initial) node handler frame middle after
    run Hrange Horigin Hactive Hcomplete) as Hreturned.
  pose proof (irq_wrapper_c_completion_normal_return _ _ _ _ _ _ _ _ _ _ _ _ initial Hwrapper Horigin) as Hnormal.
  assert (Hsame : task_tcb_init_stack_same_call (armv7a_continuation_resumed_call suspended call) original).
  { destruct Hregistration as [task [[Hsame0 Hrest] Hpointer]].
    destruct Hsame0 as [Hi [Ho Hs]]; destruct (proj1 Hnormal) as [Hi' [Ho' Hs']].
    unfold task_tcb_init_stack_same_call; repeat split; congruence. }
  destruct (kernel_program_returned_c_sequence_waiting_fields _ _ _ _ _ _ _ _ _ _ _ _ run)
    as [Hnodes Hfields].
  assert (Hstep : os_int_exit_returned_c_step environment critical sg state before
    (os_int_exit_returned_c_input environment sg state local suspended
      (flag_pend_waiting_receipt sg original pointer call initial) handler frame) false
    (os_int_exit_wrapper_restored_state (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state)
      suspended.(armv7a_continuation_stack)) after
    (irq_wrapper_c_output environment sg (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state)
      local suspended (flag_pend_waiting_receipt sg original pointer call initial) call handler
      (unmap_table_rep sg ** frame))).
  { econstructor; exact Hcomplete. }
  destruct (os_int_exit_returned_c_step_waiting_fields _ _ _ _ _ _ _ _ _ _ Hstep)
    as [Hnodes' Hfields'].
  destruct (Hfields original.(os_sched_call_origin)) as [Hmulti [Hpending Hdetached]].
  destruct (Hfields' original.(os_sched_call_origin)) as [Hmulti' [Hpending' Hdetached']].
  assert (Hcase' : (exists waiter, (os_int_exit_wrapper_restored_state
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state)
      suspended.(armv7a_continuation_stack)).(FlagState).(flagWaitNodes) pointer = Some waiter) \/
    initial.(FlagState).(flagWaitNodes) pointer = None).
  { destruct observed.(SchedState).(isRunning); exact Hcase. }
  assert (Hrecover : flag_pend_waiting_receipt sg original pointer call initial |--
    flag_pend_waiting_receipt sg original pointer (armv7a_continuation_resumed_call suspended call)
      (os_int_exit_wrapper_restored_state (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state)
        suspended.(armv7a_continuation_stack))).
  { eapply flag_waiting_receipt_from_returned_observations;
      [exact Hregistration|exact Houtcome|exact Hvalid
      |eapply flag_wait_nodes_included_trans; eassumption
      |auto|auto|auto|exact Hcase'|exact Hsame|exact Hreturned]. }
  unfold irq_wrapper_c_output, flag_source_save_input.
  sep_apply_l_atomic Hrecover; entailer!.
Qed.

Import SelectedLocalRecovery ReturnedIdleSource.

Lemma kernel_program_returned_os_int_exit_waiting_caller_consequence :
  forall environment critical sg original pointer call initial first_heap input stopped observed read_heap observation_frame
    state before local suspended node handler private_frame middle after
    (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin))
      initial first_heap input stopped state before
      (os_int_exit_returned_c_input environment sg state local suspended
        (flag_pend_waiting_receipt sg original pointer call initial) handler private_frame)),
  kernel_program_returned_sequence_idle_source environment critical sg
    call.(os_sched_call_invocation) call.(os_sched_call_origin) _ _ _ _ _ _ _ run ->
  task_in_range sg initial.(TskState) -> initial.(SchedState).(isRunning) = true ->
  task_idle_ready sg initial.(TskState) -> flag_pend_non_idle_at sg original initial ->
  ((exists waiter, state.(FlagState).(flagWaitNodes) pointer = Some waiter) \/
    initial.(FlagState).(flagWaitNodes) pointer = None) ->
  os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
    state local suspended (flag_pend_waiting_receipt sg original pointer call initial)
    call node handler private_frame before middle after ->
  kernel_call_task_source (armv7a_continuation_resumed_call suspended call)
    (os_int_exit_wrapper_restored_state
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) suspended.(armv7a_continuation_stack)) /\
  kernel_call_normal_return call initial (armv7a_continuation_resumed_call suspended call)
    (os_int_exit_wrapper_restored_state
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) suspended.(armv7a_continuation_stack)) /\
  (irq_wrapper_c_output environment sg
    (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) local suspended
    (flag_pend_waiting_receipt sg original pointer call initial) call handler
    (unmap_table_rep sg ** private_frame) |--
  (flag_pend_caller_save_input environment critical local (flag_pend_wait_active sg original pointer) sg
    (FlagPendTaskCaller (armv7a_continuation_resumed_call suspended call))
    (armv7a_continuation_resumed_call suspended call)
    (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr))
    (os_int_exit_wrapper_restored_state
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) suspended.(armv7a_continuation_stack)) **
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** private_frame))).
Proof.
  intros environment critical sg original pointer call initial first_heap input stopped observed read_heap observation_frame
    state before local suspended node handler private_frame middle after run Hidle_source Hrange Hrunning Hidle Hnonidle Hcase Hcomplete.
  pose proof (proj2 (os_int_exit_returned_c_completion_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete)) as Houtput.
  assert (Hextract : irq_wrapper_c_output environment sg
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) local suspended
      (flag_pend_waiting_receipt sg original pointer call initial) call handler (unmap_table_rep sg ** private_frame) |--
    coq_prop (flag_active_waiting_registration original pointer call initial)).
  { unfold irq_wrapper_c_output, flag_source_save_input, flag_pend_waiting_receipt, flag_active_waiting; entailer!. }
  pose proof (Hextract after Houtput) as Hregistration.
  destruct (flag_waiting_registration_call_activity _ _ _ _ Hregistration) as [Horigin Hactive].
  pose proof (kernel_program_returned_os_int_exit_source_from_active environment critical sg call
    initial first_heap input stopped observed read_heap observation_frame state before local suspended
    (flag_pend_waiting_receipt sg original pointer call initial) node handler private_frame middle after
    run Hrange Horigin Hactive Hcomplete) as Hreturned.
  pose proof (os_int_exit_returned_c_completion_wrapper _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete) as Hwrapper.
  pose proof (irq_wrapper_c_completion_normal_return _ _ _ _ _ _ _ _ _ _ _ _ initial Hwrapper Horigin) as Hnormal.
  assert (Hsame : task_tcb_init_stack_same_call call original).
  { destruct Hregistration as [task [[Hsame Hrest] Hpointer]]; exact Hsame. }
  pose (terminal := @KernelProgramReturnedExit environment critical sg
    call.(os_sched_call_invocation) call.(os_sched_call_origin) _ _ _ _ _ _ _
    (@OSIntExitReturnedCStep environment critical sg observed read_heap observation_frame
      state local suspended (flag_pend_waiting_receipt sg original pointer call initial)
      call node handler private_frame before middle after Hcomplete)).
  pose (last := KernelCSequenceAtom _ _ _ _ _ _ _ _ terminal).
  pose (whole := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ run (fun heap H => H) last).
  assert (Hwhole_idle : kernel_program_returned_sequence_idle_source environment critical sg
    call.(os_sched_call_invocation) call.(os_sched_call_origin) _ _ _ _ _ _ _ whole).
  { unfold whole, kernel_program_returned_sequence_idle_source; apply KernelCSourceThen; [exact Hidle_source|].
    unfold last; apply KernelCSourceAtom; unfold terminal; constructor. }
  destruct (kernel_program_returned_completed_idle_non_idle environment critical sg call
    (armv7a_continuation_resumed_call suspended call) _ _ _ _ _ _ _ whole Hwhole_idle
    Hrange Horigin Hactive Hrunning Hnormal Hreturned) as [Hstop [Hidle_final Hnonidle_final]].
  assert (Hinitial_nonidle : flag_pend_non_idle_at sg call initial).
  { unfold flag_pend_non_idle_at in *; rewrite (proj2 (proj2 Hsame)); exact Hnonidle. }
  specialize (Hnonidle_final Hinitial_nonidle).
  assert (Hfinal_nonidle : flag_pend_non_idle_at sg original
    (os_int_exit_wrapper_restored_state
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) suspended.(armv7a_continuation_stack))).
  { unfold flag_pend_non_idle_at in *.
    rewrite (proj2 (proj2 (proj1 Hnormal))), (proj2 (proj2 Hsame)) in Hnonidle_final; exact Hnonidle_final. }
  pose proof (kernel_program_returned_os_int_exit_waiting_receipt_consequence environment critical sg original pointer call initial
    first_heap input stopped observed read_heap observation_frame state before local suspended node handler private_frame middle after
    run Hrange Hcase Hcomplete) as Hcurrent_consequence.
  assert (Hstack : call.(os_sched_call_stack) = suspended.(armv7a_continuation_stack)).
  { pose proof (proj2 (irq_wrapper_c_binding _ _ _ _ _ _ _ _ _ _ _ _ Hwrapper)) as Hbinding.
    rewrite (irq_wrapper_c_saved_call _ _ _ _ _ _ _ _ _ _ _ _ Hwrapper) in Hbinding; exact Hbinding. }
  pose proof (irq_wrapper_c_output_caller_input environment critical sg
    (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) local suspended
    (flag_pend_waiting_receipt sg original pointer (armv7a_continuation_resumed_call suspended call)
      (os_int_exit_wrapper_restored_state
        (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) suspended.(armv7a_continuation_stack)))
    call handler private_frame Horigin Hstack) as Hopen.
  split; [exact Hreturned|]; split; [exact Hnormal|].
  sep_apply_l_atomic Hcurrent_consequence.
  sep_apply_l_atomic Hopen.
  unfold flag_pend_caller_save_input, flag_pend_active_save_input; Intros.
  unfold flag_pend_waiting_receipt, flag_pend_wait_active; entailer!.
Qed.

End ReturnedWaitingConsequence.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module ReturnedIRQWaitingCaller.
Import PrimitiveComponent PendPhaseCandidate SelectedReturnedCProgram SelectedReturnedCSource
  SelectedIRQWrapperCompletion OSIntExitReturnedC OSIntExitCCallControl OSIntExitCCallEnvelope
  OSIntExitCCallCompletion ReturnedIRQEntryReceipts ReturnedIRQEntryReceiptEquality ReturnedIRQEntryIdle
  ReturnedIRQCallSource SelectedEnvironmentCProgram SelectedEnvironmentCSource
  FlagWaitingRecovery FlagWaitingReturnedOwner ReturnedIdleSource ReturnedWaitingConsequence.

Section ActualCall.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (reference original : OsSchedCallContext) (pointer : addr).
Context (initial : UCOS2_Verify_State) (entry_node : TaskAbstractState)
  (handler : OsIntExitCallContext) (suspended : Armv7aContinuation)
  (publication : nat) (entry_local : Armv7aContinuation -> Assertion) (entry_frame : Assertion)
  (before saved_heap body_heap : model).
Let parked := armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
  suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments).
Let receipt := flag_pend_waiting_receipt sg reference pointer original initial.
Context (body_input : Assertion) (prefix_stop : bool) (observed : UCOS2_Verify_State)
  (read_heap : model) (prefix_output read_input : Assertion) (acquire_stop : bool)
  (entry : UCOS2_Verify_State) (acquired_heap : model) (acquire_output : Assertion).
Context (prefix : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  parked body_heap body_input prefix_stop observed read_heap prefix_output).
Context (acquire : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  observed read_heap read_input acquire_stop entry acquired_heap acquire_output).
Context (observation_frame : Assertion) (local : Armv7aContinuation -> Assertion)
  (node : TaskAbstractState) (private_frame : Assertion) (middle after : model).
Context (returned : os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
  entry local suspended receipt original node handler private_frame acquired_heap middle after).
Context (call : os_int_exit_first_level_c_call environment critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin)
  initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
  body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
  prefix acquire local receipt private_frame).
Let final := os_int_exit_wrapper_restored_state
  (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry) suspended.(armv7a_continuation_stack).
Let resumed := armv7a_continuation_resumed_call suspended original.
Let final_owner := flag_pend_caller_save_input environment critical local
  (flag_pend_wait_active sg reference pointer) sg (FlagPendTaskCaller resumed) resumed
  (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) final **
  (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** private_frame).

Lemma os_int_exit_waiting_c_call_caller_output :
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ acquire ->
  task_idle_ready sg initial.(TskState) -> flag_pend_non_idle_at sg reference initial ->
  ((exists waiter, entry.(FlagState).(flagWaitNodes) pointer = Some waiter) \/
    initial.(FlagState).(flagWaitNodes) pointer = None) ->
  kernel_call_task_source resumed final /\ kernel_call_normal_return original initial resumed final /\
  kernel_call_control_rely sg initial final /\
  (irq_wrapper_c_output environment sg
    (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
    local suspended receipt original handler (unmap_table_rep sg ** private_frame) |-- final_owner).
Proof.
  intros Hprefix_idle Hacquire_idle Hidle Hnonidle Hcase.
  pose proof (os_int_exit_first_level_c_call_control environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local receipt original node private_frame middle after returned call) as Hcontrol.
  destruct call as [Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge].
  pose proof (proj2 (os_int_exit_first_level_entry_c_resources _ _ _ _ _ _ _ _ _ _ _ _ Hentry)) as Hparked_owner.
  assert (Hextract_range : os_int_exit_first_level_entry_output environment sg initial handler suspended entry_local entry_frame |--
    coq_prop (task_in_range sg parked.(TskState))).
  { unfold os_int_exit_first_level_entry_output, UCOS2_fields_inv; Intros.
    pose proof (proj1 (proj2 H)) as Hrange; entailer!. }
  pose proof (Hextract_range body_heap Hparked_owner) as Hrange.
  pose proof (os_int_exit_entry_waiting_receipt_eq environment sg initial entry_node handler suspended
    publication entry_local entry_frame before saved_heap body_heap Hentry reference pointer original) as Hreceipt.
  fold parked in Hreceipt.
  pose proof returned as Hreturned_parked.
  unfold receipt in Hreturned_parked; rewrite Hreceipt in Hreturned_parked.
  pose proof Hreturn_bridge as Hreturn_parked.
  unfold receipt in Hreturn_parked; rewrite Hreceipt in Hreturn_parked.
  pose (middle_run := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ prefix Hread_bridge acquire).
  pose (body_run := KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hparked_owner Hentry_bridge middle_run Hreturn_parked).
  assert (Hbody_idle : kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ body_run).
  { unfold body_run, kernel_program_returned_sequence_idle_source; apply KernelCSourceAdapt.
    unfold middle_run; apply KernelCSourceThen; assumption. }
  assert (Hparked_running : parked.(SchedState).(isRunning) = true).
  { unfold parked; rewrite (os_int_exit_entry_sched_state _ _ _ _ _ _ _ _ _ _ _ _ Hentry).
    exact (os_int_exit_entry_running _ _ _ _ _ _ _ _ _ _ _ _ Hentry). }
  pose proof (os_int_exit_entry_preserves_idle_ready _ _ _ _ _ _ _ _ _ _ _ _ Hentry Hidle) as Hparked_idle.
  pose proof (os_int_exit_entry_preserves_non_idle _ _ _ _ _ _ _ _ _ _ _ _ Hentry reference Hnonidle) as Hparked_nonidle.
  assert (Hparked_case : (exists waiter, entry.(FlagState).(flagWaitNodes) pointer = Some waiter) \/
    parked.(FlagState).(flagWaitNodes) pointer = None).
  { unfold parked; rewrite (os_int_exit_entry_flag_state _ _ _ _ _ _ _ _ _ _ _ _ Hentry); exact Hcase. }
  destruct (kernel_program_returned_os_int_exit_waiting_caller_consequence environment critical sg reference pointer original
    parked body_heap _ (orb prefix_stop acquire_stop) observed read_heap observation_frame entry acquired_heap
    local suspended node handler private_frame middle after body_run Hbody_idle Hrange Hparked_running Hparked_idle
    Hparked_nonidle Hparked_case Hreturned_parked) as [Hsource [Hnormal_parked Hrecover]].
  pose proof (proj2 (os_int_exit_returned_c_completion_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ returned)) as Houtput.
  assert (Hextract : irq_wrapper_c_output environment sg
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
      local suspended receipt original handler (unmap_table_rep sg ** private_frame) |--
    coq_prop (flag_active_waiting_registration reference pointer original initial)).
  { unfold receipt, irq_wrapper_c_output, flag_source_save_input, flag_pend_waiting_receipt, flag_active_waiting; entailer!. }
  destruct (flag_waiting_registration_call_activity _ _ _ _ (Hextract after Houtput)) as [Horigin Hactive].
  pose proof (os_int_exit_returned_c_completion_wrapper _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ returned) as Hwrapper.
  pose proof (irq_wrapper_c_completion_normal_return _ _ _ _ _ _ _ _ _ _ _ _ initial Hwrapper Horigin) as Hnormal.
  split; [exact Hsource|]. split; [exact Hnormal|]. split; [exact Hcontrol|].
  unfold receipt; rewrite Hreceipt; exact Hrecover.
Qed.

Lemma os_int_exit_waiting_c_call_sequence : forall event_observer,
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ acquire ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ acquire ->
  task_idle_ready sg initial.(TskState) -> flag_pend_non_idle_at sg reference initial ->
  ((exists waiter, entry.(FlagState).(flagWaitNodes) pointer = Some waiter) \/
    initial.(FlagState).(flagWaitNodes) pointer = None) ->
  exists (run : kernel_c_sequence
    (kernel_program_environment_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial before (os_int_exit_first_level_entry_input environment sg initial handler suspended entry_local entry_frame)
    (orb prefix_stop (orb acquire_stop false)) final after
    (coq_prop (kernel_call_task_source resumed final /\ kernel_call_normal_return original initial resumed final /\
      kernel_call_control_rely sg initial final) && final_owner)),
  kernel_program_environment_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ run.
Proof.
  intros event_observer Hprefix_source Hacquire_source Hprefix_idle Hacquire_idle Hidle Hnonidle Hcase.
  destruct (os_int_exit_waiting_c_call_caller_output Hprefix_idle Hacquire_idle Hidle Hnonidle Hcase)
    as [Hreturned [Hnormal [Hcontrol Hrecover]]].
  destruct call as [Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge].
  pose (actual := @OSIntExitFirstLevelCStep environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local receipt original node private_frame middle after
    Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge returned).
  pose (step := @KernelProgramEnvironmentIRQCall environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ actual).
  pose (one := KernelCSequenceAtom _ _ _ _ _ _ _ _ step).
  pose proof (proj1 (os_int_exit_first_level_c_step_resources _ _ _ _ _ _ _ _ _ _ _ _ actual)) as Hinput.
  assert (Hpost : irq_wrapper_c_output environment sg
    (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
    local suspended receipt original handler (unmap_table_rep sg ** private_frame) |--
    coq_prop (kernel_call_task_source resumed final /\ kernel_call_normal_return original initial resumed final /\
      kernel_call_control_rely sg initial final) && final_owner).
  { intros heap Howned; split; [exact (conj Hreturned (conj Hnormal Hcontrol))|exact (Hrecover heap Howned)]. }
  exists (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput (fun heap H => H) one Hpost).
  unfold kernel_program_environment_c_sequence_source; apply KernelCSourceAdapt.
  unfold one; apply KernelCSourceAtom; unfold step; apply KernelProgramEnvironmentIRQCallSource.
  unfold actual; constructor; assumption.
Qed.

End ActualCall.
End ReturnedIRQWaitingCaller.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations PendPhaseCandidate.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagPendFreshSourceRecovery.
Import FlagPendFreshRecovery FlagPendFreshSource SelectedCProgram
  SelectedIRQWrapperCompletion SelectedIRQWrapperSegment.

Lemma irq_wrapper_c_step_preserves_fresh_fields :
  forall environment sg entry before input stopped returned after output origin,
  irq_wrapper_c_step environment sg entry before input stopped returned after output ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros environment sg entry before input stopped returned after output origin Hstep Hfields.
  destruct Hstep; eapply flag_pend_fresh_fields_used_eq; [reflexivity|exact Hfields].
Qed.

Lemma kernel_program_wrapper_c_step_preserves_fresh_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  kernel_program_wrapper_c_step environment critical sg observer observer_origin
    entry before input stopped returned after output ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin
    Hstep Hfields; destruct Hstep.
  - eapply kernel_program_selected_c_step_preserves_fresh_fields; eassumption.
  - eapply irq_wrapper_c_step_preserves_fresh_fields; eassumption.
Qed.

Lemma kernel_program_wrapper_c_sequence_preserves_fresh_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  kernel_c_sequence (kernel_program_wrapper_c_step environment critical sg observer observer_origin)
    entry before input stopped returned after output ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin Hrun.
  induction Hrun; intro Hfields.
  - exact Hfields.
  - eapply kernel_program_wrapper_c_step_preserves_fresh_fields; eassumption.
  - apply IHHrun2, IHHrun1, Hfields.
  - apply IHHrun, Hfields.
Qed.

(** The endpoint source and same-call facts are the internal results of a
    completed C return.  This resource consequence reinterprets the saved
    pure receipt at that same returned state, retaining its original heap. *)
Lemma kernel_program_wrapper_fresh_observation :
  forall environment critical sg observer observer_origin entry before input stopped current after output
    original prior returned,
  kernel_c_sequence (kernel_program_wrapper_c_step environment critical sg observer observer_origin)
    entry before input stopped current after output ->
  task_tcb_init_stack_same_call returned original ->
  kernel_call_task_source returned current ->
  flag_pend_fresh_observation original prior entry |--
    flag_pend_fresh_observation original returned current.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped current after output
    original prior returned Hrun Hsame Hsource heap [Hregistration Hempty].
  apply (flag_pend_fresh_observation_from_returned_source original returned current Hsame Hsource);
    [|exact Hempty].
  eapply kernel_program_wrapper_c_sequence_preserves_fresh_fields; [exact Hrun|].
  exact (flag_active_fresh_registration_fields original prior entry Hregistration).
Qed.

Lemma kernel_program_wrapper_first_observation :
  forall environment critical sg observer observer_origin entry before input stopped current after output
    mode original initial prior returned,
  kernel_c_sequence (kernel_program_wrapper_c_step environment critical sg observer observer_origin)
    entry before input stopped current after output ->
  task_tcb_init_stack_same_call returned original ->
  ((flag_pend_valid_mode mode \/ flag_pend_task_entry original initial) ->
    kernel_call_task_source returned current) ->
  flag_pend_first_observation mode original initial prior entry |--
    flag_pend_first_observation mode original initial returned current.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped current after output
    mode original initial prior returned Hrun Hsame Hsource heap [Hregistration Hempty].
  apply (flag_pend_first_observation_from_returned_source mode original initial returned current Hsame Hsource);
    [|exact Hempty].
  intro Hguard.
  eapply kernel_program_wrapper_c_sequence_preserves_fresh_fields; [exact Hrun|].
  exact (flag_active_fresh_registration_fields original prior entry (Hregistration Hguard)).
Qed.

(** This is a concrete completion producer: the returned TaskSource is
    constructed from the same initial source, prefix and actual wrapper
    read/restore.  It is not a premise supplied by the public C caller. *)
Lemma selected_irq_wrapper_fresh_observation :
  forall environment critical sg original initial first_heap input stopped state before
    local suspended receipt node handler frame after
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap input stopped state before
      (irq_wrapper_c_input environment sg state local suspended receipt handler frame)),
  task_in_range sg initial.(TskState) ->
  kernel_call_task_source original initial ->
  irq_wrapper_c_completion environment sg state local suspended receipt original node handler frame before after ->
  flag_pend_fresh_observation original original initial |--
    flag_pend_fresh_observation original (armv7a_continuation_resumed_call suspended original)
      (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)).
Proof.
  intros environment critical sg original initial first_heap input stopped state before
    local suspended receipt node handler frame after run Hrange Hinitial Hcomplete.
  destruct (selected_sequence_irq_wrapper_completion environment critical sg original initial first_heap
    input stopped state before local suspended receipt node handler frame after run Hrange Hinitial Hcomplete)
    as [Hfull [Hreturned Hnormal]].
  eapply kernel_program_wrapper_fresh_observation;
    [exact Hfull|exact (proj1 Hnormal)|exact Hreturned].
Qed.

Lemma selected_irq_wrapper_first_observation :
  forall environment critical sg mode original initial first_heap input stopped state before
    local suspended receipt node handler frame after
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap input stopped state before
      (irq_wrapper_c_input environment sg state local suspended receipt handler frame)),
  task_in_range sg initial.(TskState) ->
  kernel_call_task_source original initial ->
  irq_wrapper_c_completion environment sg state local suspended receipt original node handler frame before after ->
  flag_pend_first_observation mode original initial original initial |--
    flag_pend_first_observation mode original initial (armv7a_continuation_resumed_call suspended original)
      (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)).
Proof.
  intros environment critical sg mode original initial first_heap input stopped state before
    local suspended receipt node handler frame after run Hrange Hinitial Hcomplete.
  destruct (selected_sequence_irq_wrapper_completion environment critical sg original initial first_heap
    input stopped state before local suspended receipt node handler frame after run Hrange Hinitial Hcomplete)
    as [Hfull [Hreturned Hnormal]].
  eapply kernel_program_wrapper_first_observation;
    [exact Hfull|exact (proj1 Hnormal)|intro Hguard; exact Hreturned].
Qed.

End FlagPendFreshSourceRecovery.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SelectedReturnedFresh.
Import SelectedReturnedCProgram FlagPendFreshRecovery FlagPendFreshSourceRecovery OSIntExitReturnedFresh.

Lemma kernel_program_returned_c_step_preserves_fresh_fields :
  forall environment critical sg observer origin initial before input stopped current after output actual_origin,
  kernel_program_returned_c_step environment critical sg observer origin
    initial before input stopped current after output ->
  flag_pend_fresh_fields_at_origin actual_origin initial ->
  flag_pend_fresh_fields_at_origin actual_origin current.
Proof.
  intros until actual_origin; intros Hstep Hfields; destruct Hstep.
  - eapply kernel_program_wrapper_c_step_preserves_fresh_fields; eassumption.
  - eapply os_int_exit_returned_c_step_preserves_fresh_fields; eassumption.
Qed.

Lemma kernel_program_returned_c_sequence_preserves_fresh_fields :
  forall environment critical sg observer origin initial before input stopped current after output actual_origin,
  kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
    initial before input stopped current after output ->
  flag_pend_fresh_fields_at_origin actual_origin initial ->
  flag_pend_fresh_fields_at_origin actual_origin current.
Proof.
  intros until actual_origin; intro Hrun; induction Hrun; intro Hfields.
  - exact Hfields.
  - eapply kernel_program_returned_c_step_preserves_fresh_fields; eassumption.
  - apply IHHrun2, IHHrun1; exact Hfields.
  - apply IHHrun; exact Hfields.
Qed.

End SelectedReturnedFresh.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module ReturnedFreshRecovery.
Import PrimitiveComponent PendPhaseCandidate SelectedReturnedCProgram.
Import SelectedIRQWrapperCompletion OSIntExitReturnedC SelectedLocalRecovery.
Import FlagPendFreshRecovery SelectedReturnedFresh ReturnedLocalSource.

Lemma flag_active_fresh_registration_call_activity : forall reference call state,
  flag_active_fresh_registration reference call state ->
  call.(os_sched_call_origin) = RunningInvocation call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) /\
  task_invocation_active state.(TskState) call.(os_sched_call_invocation) call.(os_sched_call_origin).
Proof.
  intros reference call state [task [[Hsame [Horigin [Hnode [Hgeneration [Hactive Hclear]]]]] Hnone]].
  destruct Hsame as [Hinv [Hcall_origin Hstack]].
  split; [rewrite Hcall_origin, Hstack; exact Horigin|rewrite Hinv, Hcall_origin; exact Hactive].
Qed.

(** Registration is the saved receipt's actual initial observation.  The
    selected descriptor supplies the final slot/generation/current reads. *)
Lemma kernel_program_returned_irq_wrapper_fresh_registration :
  forall environment critical sg reference call initial first_heap input stopped state before
    local suspended receipt node handler frame after
    (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin))
      initial first_heap input stopped state before
      (irq_wrapper_c_input environment sg state local suspended receipt handler frame)),
  task_in_range sg initial.(TskState) ->
  flag_active_fresh_registration reference call initial ->
  irq_wrapper_c_completion environment sg state local suspended receipt call node handler frame before after ->
  kernel_call_task_source (armv7a_continuation_resumed_call suspended call)
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) /\
  kernel_call_normal_return call initial (armv7a_continuation_resumed_call suspended call)
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) /\
  flag_active_fresh_registration reference (armv7a_continuation_resumed_call suspended call)
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)).
Proof.
  intros environment critical sg reference call initial first_heap input stopped state before
    local suspended receipt node handler frame after run Hrange Hregistration Hcomplete.
  destruct (flag_active_fresh_registration_call_activity _ _ _ Hregistration) as [Horigin Hactive].
  pose proof (kernel_program_returned_irq_wrapper_source_from_active environment critical sg call
    initial first_heap input stopped state before local suspended receipt node handler frame after
    run Hrange Horigin Hactive Hcomplete) as Hreturned.
  pose proof (irq_wrapper_c_completion_normal_return _ _ _ _ _ _ _ _ _ _ _ _ initial Hcomplete Horigin) as Hnormal.
  assert (Hsame : task_tcb_init_stack_same_call (armv7a_continuation_resumed_call suspended call) reference).
  { destruct Hregistration as [task [[Hsame0 Hrest] Hnode]].
    destruct Hsame0 as [Hi [Ho Hs]]; destruct (proj1 Hnormal) as [Hi' [Ho' Hs']].
    unfold task_tcb_init_stack_same_call; repeat split; congruence. }
  assert (Hfields : flag_pend_fresh_fields_at_origin reference.(os_sched_call_origin)
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack))).
  { change (flag_pend_fresh_fields_at_origin reference.(os_sched_call_origin) state).
    eapply kernel_program_returned_c_sequence_preserves_fresh_fields; [exact run|].
    exact (flag_active_fresh_registration_fields _ _ _ Hregistration). }
  split; [exact Hreturned|]; split; [exact Hnormal|].
  eapply flag_active_fresh_registration_from_returned_source; eassumption.
Qed.

Lemma kernel_program_returned_os_int_exit_fresh_registration :
  forall environment critical sg reference call initial first_heap input stopped observed read_heap observation_frame
    state before local suspended receipt node handler frame middle after
    (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin))
      initial first_heap input stopped state before
      (os_int_exit_returned_c_input environment sg state local suspended receipt handler frame)),
  task_in_range sg initial.(TskState) ->
  flag_active_fresh_registration reference call initial ->
  os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
    state local suspended receipt call node handler frame before middle after ->
  kernel_call_task_source (armv7a_continuation_resumed_call suspended call)
    (os_int_exit_wrapper_restored_state
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state)
      suspended.(armv7a_continuation_stack)) /\
  kernel_call_normal_return call initial (armv7a_continuation_resumed_call suspended call)
    (os_int_exit_wrapper_restored_state
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state)
      suspended.(armv7a_continuation_stack)) /\
  flag_active_fresh_registration reference (armv7a_continuation_resumed_call suspended call)
    (os_int_exit_wrapper_restored_state
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state)
      suspended.(armv7a_continuation_stack)).
Proof.
  intros environment critical sg reference call initial first_heap input stopped observed read_heap observation_frame
    state before local suspended receipt node handler frame middle after run Hrange Hregistration Hcomplete.
  destruct (flag_active_fresh_registration_call_activity _ _ _ Hregistration) as [Horigin Hactive].
  pose proof (kernel_program_returned_os_int_exit_source_from_active environment critical sg call
    initial first_heap input stopped observed read_heap observation_frame state before local suspended receipt
    node handler frame middle after run Hrange Horigin Hactive Hcomplete) as Hreturned.
  pose proof (os_int_exit_returned_c_completion_wrapper _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete) as Hwrapper.
  pose proof (irq_wrapper_c_completion_normal_return _ _ _ _ _ _ _ _ _ _ _ _ initial Hwrapper Horigin) as Hnormal.
  assert (Hsame : task_tcb_init_stack_same_call (armv7a_continuation_resumed_call suspended call) reference).
  { destruct Hregistration as [task [[Hsame0 Hrest] Hnode]].
    destruct Hsame0 as [Hi [Ho Hs]]; destruct (proj1 Hnormal) as [Hi' [Ho' Hs']].
    unfold task_tcb_init_stack_same_call; repeat split; congruence. }
  assert (Hfields : flag_pend_fresh_fields_at_origin reference.(os_sched_call_origin)
    (os_int_exit_wrapper_restored_state
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state)
      suspended.(armv7a_continuation_stack))).
  { change (flag_pend_fresh_fields_at_origin reference.(os_sched_call_origin)
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state)).
    assert (Htasks : state.(TskState) =
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state).(TskState)).
    { symmetry; exact (proj1 (os_int_exit_checkpoint_frame observed.(SchedState).(isRunning) state)). }
    apply (proj1 (flag_pend_fresh_fields_task_state_eq reference.(os_sched_call_origin) state
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) Htasks)).
    eapply kernel_program_returned_c_sequence_preserves_fresh_fields; [exact run|].
    exact (flag_active_fresh_registration_fields _ _ _ Hregistration). }
  split; [exact Hreturned|]; split; [exact Hnormal|].
  eapply flag_active_fresh_registration_from_returned_source; eassumption.
Qed.

(** A single-cut consequence, used only after the concrete producer below
    has reconstructed the current receipt from its own execution. *)
Lemma irq_wrapper_c_output_recovered_input :
  forall environment critical sg state local suspended receipt call handler private_frame active,
  call.(os_sched_call_origin) = RunningInvocation call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  call.(os_sched_call_stack) = suspended.(armv7a_continuation_stack) ->
  (receipt |-- active (armv7a_continuation_resumed_call suspended call)
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack))) ->
  irq_wrapper_c_output environment sg state local suspended receipt call handler (unmap_table_rep sg ** private_frame) |--
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller (armv7a_continuation_resumed_call suspended call))
    (armv7a_continuation_resumed_call suspended call)
    (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr))
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) **
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** private_frame).
Proof.
  intros environment critical sg state local suspended receipt call handler private_frame active Horigin Hstack Hrecover.
  sep_apply_l_atomic (irq_wrapper_c_output_caller_input environment critical sg state local suspended receipt
    call handler private_frame Horigin Hstack).
  sep_apply_l_atomic (flag_pend_caller_save_input_receipt_consequence environment critical local
    (fun _ _ => receipt) active sg (FlagPendTaskCaller (armv7a_continuation_resumed_call suspended call))
    (armv7a_continuation_resumed_call suspended call) (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr))
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) Hrecover).
  entailer!.
Qed.


Lemma kernel_program_returned_irq_wrapper_fresh_caller_input :
  forall environment critical sg reference call initial first_heap input stopped state before
    local suspended node handler private_frame after
    (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin))
      initial first_heap input stopped state before (irq_wrapper_c_input environment sg state local suspended ((flag_pend_fresh_observation reference) call initial) handler (unmap_table_rep sg ** private_frame))),
  task_in_range sg initial.(TskState) ->
  irq_wrapper_c_completion environment sg state local suspended ((flag_pend_fresh_observation reference) call initial) call node handler
    (unmap_table_rep sg ** private_frame) before after ->
  kernel_call_task_source (armv7a_continuation_resumed_call suspended call) (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) /\
  kernel_call_normal_return call initial (armv7a_continuation_resumed_call suspended call) (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) /\
  (irq_wrapper_c_output environment sg state local suspended ((flag_pend_fresh_observation reference) call initial) call handler
      (unmap_table_rep sg ** private_frame) |--
    flag_pend_caller_save_input environment critical local (flag_pend_fresh_observation reference) sg
      (FlagPendTaskCaller (armv7a_continuation_resumed_call suspended call)) (armv7a_continuation_resumed_call suspended call)
      (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) **
      (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** private_frame)).
Proof.
  intros environment critical sg reference call initial first_heap input stopped state before
    local suspended node handler private_frame after run Hrange Hcomplete.
  pose proof (proj2 (irq_wrapper_c_completion_resources _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete)) as Houtput.
  assert (Hextract : irq_wrapper_c_output environment sg state local suspended ((flag_pend_fresh_observation reference) call initial) call handler
      (unmap_table_rep sg ** private_frame) |--
    coq_prop (flag_active_fresh_registration reference call initial) && irq_wrapper_c_output environment sg state local suspended ((flag_pend_fresh_observation reference) call initial) call handler
      (unmap_table_rep sg ** private_frame)).
  { unfold irq_wrapper_c_output, flag_source_save_input, flag_pend_fresh_observation; entailer!. }
  pose proof (proj1 (Hextract after Houtput)) as Hregistration.
  destruct (kernel_program_returned_irq_wrapper_fresh_registration environment critical sg reference call initial first_heap input stopped state before
    local suspended ((flag_pend_fresh_observation reference) call initial) node handler (unmap_table_rep sg ** private_frame) after
    run Hrange Hregistration Hcomplete)
    as [Hreturned [Hnormal Hcurrent_registration]].
  destruct (flag_active_fresh_registration_call_activity _ _ _ Hregistration) as [Horigin Hactive].
  assert (Hstack : call.(os_sched_call_stack) = suspended.(armv7a_continuation_stack)).
  { pose proof (proj2 (irq_wrapper_c_binding _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete)) as Hbinding.
    rewrite (irq_wrapper_c_saved_call _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete) in Hbinding; exact Hbinding. }
  split; [exact Hreturned|]; split; [exact Hnormal|].
  apply irq_wrapper_c_output_recovered_input; [exact Horigin|exact Hstack|].
  unfold flag_pend_fresh_observation; entailer!.
Qed.

Lemma kernel_program_returned_irq_wrapper_first_caller_input :
  forall environment critical sg mode reference reference_state call initial first_heap input stopped state before
    local suspended node handler private_frame after
    (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin))
      initial first_heap input stopped state before (irq_wrapper_c_input environment sg state local suspended ((flag_pend_first_observation mode reference reference_state) call initial) handler (unmap_table_rep sg ** private_frame))),
  task_in_range sg initial.(TskState) ->
  (flag_pend_valid_mode mode \/ flag_pend_task_entry reference reference_state) ->
  irq_wrapper_c_completion environment sg state local suspended ((flag_pend_first_observation mode reference reference_state) call initial) call node handler
    (unmap_table_rep sg ** private_frame) before after ->
  kernel_call_task_source (armv7a_continuation_resumed_call suspended call) (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) /\
  kernel_call_normal_return call initial (armv7a_continuation_resumed_call suspended call) (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) /\
  (irq_wrapper_c_output environment sg state local suspended ((flag_pend_first_observation mode reference reference_state) call initial) call handler
      (unmap_table_rep sg ** private_frame) |--
    flag_pend_caller_save_input environment critical local (flag_pend_first_observation mode reference reference_state) sg
      (FlagPendTaskCaller (armv7a_continuation_resumed_call suspended call)) (armv7a_continuation_resumed_call suspended call)
      (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) **
      (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** private_frame)).
Proof.
  intros environment critical sg mode reference reference_state call initial first_heap input stopped state before
    local suspended node handler private_frame after run Hrange Hguard Hcomplete.
  pose proof (proj2 (irq_wrapper_c_completion_resources _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete)) as Houtput.
  assert (Hextract : irq_wrapper_c_output environment sg state local suspended ((flag_pend_first_observation mode reference reference_state) call initial) call handler
      (unmap_table_rep sg ** private_frame) |--
    coq_prop (flag_active_fresh_registration reference call initial) && irq_wrapper_c_output environment sg state local suspended ((flag_pend_first_observation mode reference reference_state) call initial) call handler
      (unmap_table_rep sg ** private_frame)).
  { unfold irq_wrapper_c_output, flag_source_save_input, flag_pend_first_observation; entailer!. }
  pose proof (proj1 (Hextract after Houtput)) as Hregistration.
  destruct (kernel_program_returned_irq_wrapper_fresh_registration environment critical sg reference call initial first_heap input stopped state before
    local suspended ((flag_pend_first_observation mode reference reference_state) call initial) node handler (unmap_table_rep sg ** private_frame) after
    run Hrange Hregistration Hcomplete)
    as [Hreturned [Hnormal Hcurrent_registration]].
  destruct (flag_active_fresh_registration_call_activity _ _ _ Hregistration) as [Horigin Hactive].
  assert (Hstack : call.(os_sched_call_stack) = suspended.(armv7a_continuation_stack)).
  { pose proof (proj2 (irq_wrapper_c_binding _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete)) as Hbinding.
    rewrite (irq_wrapper_c_saved_call _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete) in Hbinding; exact Hbinding. }
  split; [exact Hreturned|]; split; [exact Hnormal|].
  apply irq_wrapper_c_output_recovered_input; [exact Horigin|exact Hstack|].
  unfold flag_pend_first_observation.
  intros heap [Hreceipt Hempty]; split; [intro Hcondition; exact Hcurrent_registration|exact Hempty].
Qed.

Lemma kernel_program_returned_os_int_exit_fresh_caller_input :
  forall environment critical sg reference call initial first_heap input stopped observed read_heap observation_frame state before
    local suspended node handler private_frame middle after
    (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin))
      initial first_heap input stopped state before (os_int_exit_returned_c_input environment sg state local suspended ((flag_pend_fresh_observation reference) call initial) handler private_frame)),
  task_in_range sg initial.(TskState) ->
  os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
    state local suspended ((flag_pend_fresh_observation reference) call initial) call node handler private_frame before middle after ->
  kernel_call_task_source (armv7a_continuation_resumed_call suspended call) (os_int_exit_wrapper_restored_state (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) suspended.(armv7a_continuation_stack)) /\
  kernel_call_normal_return call initial (armv7a_continuation_resumed_call suspended call) (os_int_exit_wrapper_restored_state (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) suspended.(armv7a_continuation_stack)) /\
  (irq_wrapper_c_output environment sg (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) local suspended ((flag_pend_fresh_observation reference) call initial) call handler
      (unmap_table_rep sg ** private_frame) |--
    flag_pend_caller_save_input environment critical local (flag_pend_fresh_observation reference) sg
      (FlagPendTaskCaller (armv7a_continuation_resumed_call suspended call)) (armv7a_continuation_resumed_call suspended call)
      (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) (os_int_exit_wrapper_restored_state (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) suspended.(armv7a_continuation_stack)) **
      (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** private_frame)).
Proof.
  intros environment critical sg reference call initial first_heap input stopped observed read_heap observation_frame state before
    local suspended node handler private_frame middle after run Hrange Hcomplete.
  pose proof (proj2 (os_int_exit_returned_c_completion_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete)) as Houtput.
  assert (Hextract : irq_wrapper_c_output environment sg (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) local suspended ((flag_pend_fresh_observation reference) call initial) call handler
      (unmap_table_rep sg ** private_frame) |--
    coq_prop (flag_active_fresh_registration reference call initial) && irq_wrapper_c_output environment sg (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) local suspended ((flag_pend_fresh_observation reference) call initial) call handler
      (unmap_table_rep sg ** private_frame)).
  { unfold irq_wrapper_c_output, flag_source_save_input, flag_pend_fresh_observation; entailer!. }
  pose proof (proj1 (Hextract after Houtput)) as Hregistration.
  destruct (kernel_program_returned_os_int_exit_fresh_registration environment critical sg reference call
    initial first_heap input stopped observed read_heap observation_frame state before local suspended ((flag_pend_fresh_observation reference) call initial)
    node handler private_frame middle after run Hrange Hregistration Hcomplete)
    as [Hreturned [Hnormal Hcurrent_registration]].
  destruct (flag_active_fresh_registration_call_activity _ _ _ Hregistration) as [Horigin Hactive].
  pose proof (os_int_exit_returned_c_completion_wrapper _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete) as Hwrapper.
  assert (Hstack : call.(os_sched_call_stack) = suspended.(armv7a_continuation_stack)).
  { pose proof (proj2 (irq_wrapper_c_binding _ _ _ _ _ _ _ _ _ _ _ _ Hwrapper)) as Hbinding.
    rewrite (irq_wrapper_c_saved_call _ _ _ _ _ _ _ _ _ _ _ _ Hwrapper) in Hbinding; exact Hbinding. }
  split; [exact Hreturned|]; split; [exact Hnormal|].
  apply irq_wrapper_c_output_recovered_input; [exact Horigin|exact Hstack|].
  unfold flag_pend_fresh_observation; entailer!.
Qed.

Lemma kernel_program_returned_os_int_exit_first_caller_input :
  forall environment critical sg mode reference reference_state call initial first_heap input stopped observed read_heap observation_frame state before
    local suspended node handler private_frame middle after
    (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin))
      initial first_heap input stopped state before (os_int_exit_returned_c_input environment sg state local suspended ((flag_pend_first_observation mode reference reference_state) call initial) handler private_frame)),
  task_in_range sg initial.(TskState) ->
  (flag_pend_valid_mode mode \/ flag_pend_task_entry reference reference_state) ->
  os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
    state local suspended ((flag_pend_first_observation mode reference reference_state) call initial) call node handler private_frame before middle after ->
  kernel_call_task_source (armv7a_continuation_resumed_call suspended call) (os_int_exit_wrapper_restored_state (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) suspended.(armv7a_continuation_stack)) /\
  kernel_call_normal_return call initial (armv7a_continuation_resumed_call suspended call) (os_int_exit_wrapper_restored_state (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) suspended.(armv7a_continuation_stack)) /\
  (irq_wrapper_c_output environment sg (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) local suspended ((flag_pend_first_observation mode reference reference_state) call initial) call handler
      (unmap_table_rep sg ** private_frame) |--
    flag_pend_caller_save_input environment critical local (flag_pend_first_observation mode reference reference_state) sg
      (FlagPendTaskCaller (armv7a_continuation_resumed_call suspended call)) (armv7a_continuation_resumed_call suspended call)
      (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) (os_int_exit_wrapper_restored_state (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) suspended.(armv7a_continuation_stack)) **
      (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** private_frame)).
Proof.
  intros environment critical sg mode reference reference_state call initial first_heap input stopped observed read_heap observation_frame state before
    local suspended node handler private_frame middle after run Hrange Hguard Hcomplete.
  pose proof (proj2 (os_int_exit_returned_c_completion_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete)) as Houtput.
  assert (Hextract : irq_wrapper_c_output environment sg (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) local suspended ((flag_pend_first_observation mode reference reference_state) call initial) call handler
      (unmap_table_rep sg ** private_frame) |--
    coq_prop (flag_active_fresh_registration reference call initial) && irq_wrapper_c_output environment sg (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) state) local suspended ((flag_pend_first_observation mode reference reference_state) call initial) call handler
      (unmap_table_rep sg ** private_frame)).
  { unfold irq_wrapper_c_output, flag_source_save_input, flag_pend_first_observation; entailer!. }
  pose proof (proj1 (Hextract after Houtput)) as Hregistration.
  destruct (kernel_program_returned_os_int_exit_fresh_registration environment critical sg reference call
    initial first_heap input stopped observed read_heap observation_frame state before local suspended ((flag_pend_first_observation mode reference reference_state) call initial)
    node handler private_frame middle after run Hrange Hregistration Hcomplete)
    as [Hreturned [Hnormal Hcurrent_registration]].
  destruct (flag_active_fresh_registration_call_activity _ _ _ Hregistration) as [Horigin Hactive].
  pose proof (os_int_exit_returned_c_completion_wrapper _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete) as Hwrapper.
  assert (Hstack : call.(os_sched_call_stack) = suspended.(armv7a_continuation_stack)).
  { pose proof (proj2 (irq_wrapper_c_binding _ _ _ _ _ _ _ _ _ _ _ _ Hwrapper)) as Hbinding.
    rewrite (irq_wrapper_c_saved_call _ _ _ _ _ _ _ _ _ _ _ _ Hwrapper) in Hbinding; exact Hbinding. }
  split; [exact Hreturned|]; split; [exact Hnormal|].
  apply irq_wrapper_c_output_recovered_input; [exact Horigin|exact Hstack|].
  unfold flag_pend_first_observation.
  intros heap [Hreceipt Hempty]; split; [intro Hcondition; exact Hcurrent_registration|exact Hempty].
Qed.

End ReturnedFreshRecovery.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module ReturnedIRQFreshCaller.
Import PrimitiveComponent PendPhaseCandidate SelectedReturnedCProgram SelectedReturnedCSource
  SelectedIRQWrapperCompletion OSIntExitReturnedC OSIntExitCCallControl OSIntExitCCallEnvelope
  OSIntExitCCallCompletion ReturnedIRQEntryReceipts ReturnedFreshRecovery
  ReturnedIRQCallSource SelectedEnvironmentCProgram SelectedEnvironmentCSource.

Section ActualCall.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (reference original : OsSchedCallContext).
Context (initial : UCOS2_Verify_State) (entry_node : TaskAbstractState)
  (handler : OsIntExitCallContext) (suspended : Armv7aContinuation)
  (publication : nat) (entry_local : Armv7aContinuation -> Assertion) (entry_frame : Assertion)
  (before saved_heap body_heap : model).
Let parked := armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
  suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments).
Let receipt := flag_pend_fresh_observation reference original initial.
Context (body_input : Assertion) (prefix_stop : bool) (observed : UCOS2_Verify_State)
  (read_heap : model) (prefix_output read_input : Assertion) (acquire_stop : bool)
  (entry : UCOS2_Verify_State) (acquired_heap : model) (acquire_output : Assertion).
Context (prefix : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  parked body_heap body_input prefix_stop observed read_heap prefix_output).
Context (acquire : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  observed read_heap read_input acquire_stop entry acquired_heap acquire_output).
Context (observation_frame : Assertion) (local : Armv7aContinuation -> Assertion)
  (node : TaskAbstractState) (private_frame : Assertion) (middle after : model).
Context (returned : os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
  entry local suspended receipt original node handler private_frame acquired_heap middle after).
Context (call : os_int_exit_first_level_c_call environment critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin)
  initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
  body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
  prefix acquire local receipt private_frame).
Let final := os_int_exit_wrapper_restored_state
  (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry) suspended.(armv7a_continuation_stack).
Let resumed := armv7a_continuation_resumed_call suspended original.
Let final_owner := flag_pend_caller_save_input environment critical local
  (flag_pend_fresh_observation reference) sg (FlagPendTaskCaller resumed) resumed
  (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) final **
  (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** private_frame).

Lemma os_int_exit_fresh_c_call_caller_output :
  kernel_call_task_source resumed final /\ kernel_call_normal_return original initial resumed final /\
  kernel_call_control_rely sg initial final /\
  (irq_wrapper_c_output environment sg
    (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
    local suspended receipt original handler (unmap_table_rep sg ** private_frame) |-- final_owner).
Proof.
  pose proof (os_int_exit_first_level_c_call_control environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local receipt original node private_frame middle after returned call) as Hcontrol.
  destruct call as [Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge].
  pose proof (proj2 (os_int_exit_first_level_entry_c_resources _ _ _ _ _ _ _ _ _ _ _ _ Hentry)) as Hparked_owner.
  assert (Hextract_range : os_int_exit_first_level_entry_output environment sg initial handler suspended entry_local entry_frame |--
    coq_prop (task_in_range sg parked.(TskState))).
  { unfold os_int_exit_first_level_entry_output, UCOS2_fields_inv; Intros.
    pose proof (proj1 (proj2 H)) as Hrange; entailer!. }
  pose proof (Hextract_range body_heap Hparked_owner) as Hrange.
  pose (middle_run := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ prefix Hread_bridge acquire).
  pose (body_run := KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hparked_owner Hentry_bridge middle_run Hreturn_bridge).
  pose proof (proj2 (os_int_exit_returned_c_completion_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ returned)) as Houtput.
  assert (Hextract : irq_wrapper_c_output environment sg
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
      local suspended receipt original handler (unmap_table_rep sg ** private_frame) |--
    coq_prop (flag_active_fresh_registration reference original initial)).
  { unfold receipt, irq_wrapper_c_output, flag_source_save_input, flag_pend_fresh_observation; entailer!. }
  pose proof (Hextract after Houtput) as Hinitial_registration.
  pose proof (os_int_exit_entry_fresh_registration environment sg initial entry_node handler suspended
    publication entry_local entry_frame before saved_heap body_heap Hentry reference original Hinitial_registration) as Hparked_registration.
  destruct (kernel_program_returned_os_int_exit_fresh_registration environment critical sg reference original
    parked body_heap _ (orb prefix_stop acquire_stop) observed read_heap observation_frame entry acquired_heap
    local suspended receipt node handler private_frame middle after body_run Hrange Hparked_registration returned)
    as [Hreturned [Hnormal_parked Hcurrent_registration]].
  destruct (flag_active_fresh_registration_call_activity _ _ _ Hinitial_registration) as [Horigin Hactive].
  pose proof (os_int_exit_returned_c_completion_wrapper _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ returned) as Hwrapper.
  pose proof (irq_wrapper_c_completion_normal_return _ _ _ _ _ _ _ _ _ _ _ _ initial Hwrapper Horigin) as Hnormal.
  assert (Hstack : original.(os_sched_call_stack) = suspended.(armv7a_continuation_stack)).
  { pose proof (proj2 (irq_wrapper_c_binding _ _ _ _ _ _ _ _ _ _ _ _ Hwrapper)) as Hbinding.
    rewrite (irq_wrapper_c_saved_call _ _ _ _ _ _ _ _ _ _ _ _ Hwrapper) in Hbinding; exact Hbinding. }
  split; [exact Hreturned|]. split; [exact Hnormal|]. split.
  - exact Hcontrol.
  - unfold final_owner, resumed, final.
    apply irq_wrapper_c_output_recovered_input; [exact Horigin|exact Hstack|].
    unfold receipt, flag_pend_fresh_observation; entailer!.
Qed.

Lemma os_int_exit_fresh_c_call_sequence : forall event_observer,
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ acquire ->
  exists (run : kernel_c_sequence
    (kernel_program_environment_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial before (os_int_exit_first_level_entry_input environment sg initial handler suspended entry_local entry_frame)
    (orb prefix_stop (orb acquire_stop false)) final after
    (coq_prop (kernel_call_task_source resumed final /\ kernel_call_normal_return original initial resumed final /\
      kernel_call_control_rely sg initial final) && final_owner)),
  kernel_program_environment_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ run.
Proof.
  intros event_observer Hprefix_source Hacquire_source.
  destruct os_int_exit_fresh_c_call_caller_output as [Hreturned [Hnormal [Hcontrol Hrecover]]].
  destruct call as [Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge].
  pose (actual := @OSIntExitFirstLevelCStep environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local receipt original node private_frame middle after
    Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge returned).
  pose (step := @KernelProgramEnvironmentIRQCall environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ actual).
  pose (one := KernelCSequenceAtom _ _ _ _ _ _ _ _ step).
  pose proof (proj1 (os_int_exit_first_level_c_step_resources _ _ _ _ _ _ _ _ _ _ _ _ actual)) as Hinput.
  assert (Hpost : irq_wrapper_c_output environment sg
    (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
    local suspended receipt original handler (unmap_table_rep sg ** private_frame) |--
    coq_prop (kernel_call_task_source resumed final /\ kernel_call_normal_return original initial resumed final /\
      kernel_call_control_rely sg initial final) && final_owner).
  { intros heap Howned; split; [exact (conj Hreturned (conj Hnormal Hcontrol))|exact (Hrecover heap Howned)]. }
  exists (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput (fun heap H => H) one Hpost).
  unfold kernel_program_environment_c_sequence_source; apply KernelCSourceAdapt.
  unfold one; apply KernelCSourceAtom; unfold step; apply KernelProgramEnvironmentIRQCallSource.
  unfold actual; constructor; assumption.
Qed.

End ActualCall.
End ReturnedIRQFreshCaller.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module ReturnedIRQFirstCaller.
Import PrimitiveComponent PendPhaseCandidate SelectedReturnedCProgram SelectedReturnedCSource
  SelectedIRQWrapperCompletion OSIntExitReturnedC OSIntExitCCallControl OSIntExitCCallEnvelope
  OSIntExitCCallCompletion ReturnedIRQEntryReceipts ReturnedFreshRecovery
  ReturnedIRQCallSource SelectedEnvironmentCProgram SelectedEnvironmentCSource.

Section ActualCall.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (reference original : OsSchedCallContext)
  (mode : Z) (reference_state : UCOS2_Verify_State).
Context (Hguard : flag_pend_valid_mode mode \/ flag_pend_task_entry reference reference_state).
Context (initial : UCOS2_Verify_State) (entry_node : TaskAbstractState)
  (handler : OsIntExitCallContext) (suspended : Armv7aContinuation)
  (publication : nat) (entry_local : Armv7aContinuation -> Assertion) (entry_frame : Assertion)
  (before saved_heap body_heap : model).
Let parked := armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
  suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments).
Let receipt := flag_pend_first_observation mode reference reference_state original initial.
Context (body_input : Assertion) (prefix_stop : bool) (observed : UCOS2_Verify_State)
  (read_heap : model) (prefix_output read_input : Assertion) (acquire_stop : bool)
  (entry : UCOS2_Verify_State) (acquired_heap : model) (acquire_output : Assertion).
Context (prefix : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  parked body_heap body_input prefix_stop observed read_heap prefix_output).
Context (acquire : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  observed read_heap read_input acquire_stop entry acquired_heap acquire_output).
Context (observation_frame : Assertion) (local : Armv7aContinuation -> Assertion)
  (node : TaskAbstractState) (private_frame : Assertion) (middle after : model).
Context (returned : os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
  entry local suspended receipt original node handler private_frame acquired_heap middle after).
Context (call : os_int_exit_first_level_c_call environment critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin)
  initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
  body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
  prefix acquire local receipt private_frame).
Let final := os_int_exit_wrapper_restored_state
  (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry) suspended.(armv7a_continuation_stack).
Let resumed := armv7a_continuation_resumed_call suspended original.
Let final_owner := flag_pend_caller_save_input environment critical local
  (flag_pend_first_observation mode reference reference_state) sg (FlagPendTaskCaller resumed) resumed
  (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) final **
  (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** private_frame).

Lemma os_int_exit_first_observation_c_call_caller_output :
  kernel_call_task_source resumed final /\ kernel_call_normal_return original initial resumed final /\
  kernel_call_control_rely sg initial final /\
  (irq_wrapper_c_output environment sg
    (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
    local suspended receipt original handler (unmap_table_rep sg ** private_frame) |-- final_owner).
Proof.
  pose proof (os_int_exit_first_level_c_call_control environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local receipt original node private_frame middle after returned call) as Hcontrol.
  destruct call as [Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge].
  pose proof (proj2 (os_int_exit_first_level_entry_c_resources _ _ _ _ _ _ _ _ _ _ _ _ Hentry)) as Hparked_owner.
  assert (Hextract_range : os_int_exit_first_level_entry_output environment sg initial handler suspended entry_local entry_frame |--
    coq_prop (task_in_range sg parked.(TskState))).
  { unfold os_int_exit_first_level_entry_output, UCOS2_fields_inv; Intros.
    pose proof (proj1 (proj2 H)) as Hrange; entailer!. }
  pose proof (Hextract_range body_heap Hparked_owner) as Hrange.
  pose (middle_run := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ prefix Hread_bridge acquire).
  pose (body_run := KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hparked_owner Hentry_bridge middle_run Hreturn_bridge).
  pose proof (proj2 (os_int_exit_returned_c_completion_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ returned)) as Houtput.
  assert (Hextract : irq_wrapper_c_output environment sg
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
      local suspended receipt original handler (unmap_table_rep sg ** private_frame) |--
    coq_prop (flag_active_fresh_registration reference original initial)).
  { unfold receipt, irq_wrapper_c_output, flag_source_save_input, flag_pend_first_observation; entailer!. }
  pose proof (Hextract after Houtput) as Hinitial_registration.
  pose proof (os_int_exit_entry_fresh_registration environment sg initial entry_node handler suspended
    publication entry_local entry_frame before saved_heap body_heap Hentry reference original Hinitial_registration) as Hparked_registration.
  destruct (kernel_program_returned_os_int_exit_fresh_registration environment critical sg reference original
    parked body_heap _ (orb prefix_stop acquire_stop) observed read_heap observation_frame entry acquired_heap
    local suspended receipt node handler private_frame middle after body_run Hrange Hparked_registration returned)
    as [Hreturned [Hnormal_parked Hcurrent_registration]].
  destruct (flag_active_fresh_registration_call_activity _ _ _ Hinitial_registration) as [Horigin Hactive].
  pose proof (os_int_exit_returned_c_completion_wrapper _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ returned) as Hwrapper.
  pose proof (irq_wrapper_c_completion_normal_return _ _ _ _ _ _ _ _ _ _ _ _ initial Hwrapper Horigin) as Hnormal.
  assert (Hstack : original.(os_sched_call_stack) = suspended.(armv7a_continuation_stack)).
  { pose proof (proj2 (irq_wrapper_c_binding _ _ _ _ _ _ _ _ _ _ _ _ Hwrapper)) as Hbinding.
    rewrite (irq_wrapper_c_saved_call _ _ _ _ _ _ _ _ _ _ _ _ Hwrapper) in Hbinding; exact Hbinding. }
  split; [exact Hreturned|]. split; [exact Hnormal|]. split.
  - exact Hcontrol.
  - unfold final_owner, resumed, final.
    apply irq_wrapper_c_output_recovered_input; [exact Horigin|exact Hstack|].
    unfold receipt, flag_pend_first_observation.
    intros heap [Hreceipt Hempty]; split; [intro Hcondition; exact Hcurrent_registration|exact Hempty].
Qed.

Lemma os_int_exit_first_observation_c_call_sequence : forall event_observer,
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ acquire ->
  exists (run : kernel_c_sequence
    (kernel_program_environment_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial before (os_int_exit_first_level_entry_input environment sg initial handler suspended entry_local entry_frame)
    (orb prefix_stop (orb acquire_stop false)) final after
    (coq_prop (kernel_call_task_source resumed final /\ kernel_call_normal_return original initial resumed final /\
      kernel_call_control_rely sg initial final) && final_owner)),
  kernel_program_environment_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ run.
Proof.
  intros event_observer Hprefix_source Hacquire_source.
  destruct os_int_exit_first_observation_c_call_caller_output as [Hreturned [Hnormal [Hcontrol Hrecover]]].
  destruct call as [Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge].
  pose (actual := @OSIntExitFirstLevelCStep environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local receipt original node private_frame middle after
    Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge returned).
  pose (step := @KernelProgramEnvironmentIRQCall environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ actual).
  pose (one := KernelCSequenceAtom _ _ _ _ _ _ _ _ step).
  pose proof (proj1 (os_int_exit_first_level_c_step_resources _ _ _ _ _ _ _ _ _ _ _ _ actual)) as Hinput.
  assert (Hpost : irq_wrapper_c_output environment sg
    (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
    local suspended receipt original handler (unmap_table_rep sg ** private_frame) |--
    coq_prop (kernel_call_task_source resumed final /\ kernel_call_normal_return original initial resumed final /\
      kernel_call_control_rely sg initial final) && final_owner).
  { intros heap Howned; split; [exact (conj Hreturned (conj Hnormal Hcontrol))|exact (Hrecover heap Howned)]. }
  exists (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput (fun heap H => H) one Hpost).
  unfold kernel_program_environment_c_sequence_source; apply KernelCSourceAdapt.
  unfold one; apply KernelCSourceAtom; unfold step; apply KernelProgramEnvironmentIRQCallSource.
  unfold actual; constructor; assumption.
Qed.

End ActualCall.
End ReturnedIRQFirstCaller.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module OSIntExitCCallReady.
Import PrimitiveComponent OSIntExitReturnedC OSIntExitCCallControl
  OSIntExitCCallEnvelope OSIntExitCCallCompletion ReturnedIRQCallSource.

Lemma flag_pend_current_ready_implies_current_consistency : forall call state,
  flag_pend_current_ready call state ->
  sched_current_consistency state.(TskState) state.(SchedState).
Proof.
  intros call state [node [[Hnode [Hcurrent [Hpriority Hrest]]] Hgeneration]].
  unfold sched_current_consistency; rewrite Hcurrent.
  exists node; exact (conj Hnode Hpriority).
Qed.

(** The post-counter selection is the actual no-switch C branch. The
    cache premise is supplied below by the same complete call, under the
    original conditional-ready antecedent. It is not a new C input. *)
Lemma os_int_exit_returned_c_completion_current_ready :
  forall environment critical sg observed read_heap observation_frame entry local suspended receipt
    original node handler frame before middle after returned,
  os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
    entry local suspended receipt original node handler frame before middle after ->
  observed.(SchedState).(isRunning) = true ->
  let current := os_int_exit_wrapper_restored_state
    (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
    suspended.(armv7a_continuation_stack) in
  os_sched_selection_enabled current = true ->
  kernel_call_task_source returned current ->
  sched_current_consistency current.(TskState) current.(SchedState) ->
  os_sched_task_current_ready returned current.
Proof.
  intros until returned; intros Hcomplete Hrunning current Henabled Hsource Hcache.
  pose proof (os_int_exit_returned_full_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete) as Hreturned.
  change (os_int_exit_return_relation critical sg handler observed entry) in Hreturned.
  destruct Hreturned as [_ Hnoswitch].
  rewrite Hrunning in Hnoswitch.
  pose proof (os_int_exit_returned_before_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete) as Hinput.
  assert (Hopen : os_int_exit_returned_c_input environment sg entry local suspended receipt handler frame |--
    coq_prop (UCOS2_state_inv sg entry) &&
    os_int_exit_returned_c_input environment sg entry local suspended receipt handler frame).
  { unfold os_int_exit_returned_c_input, UCOS2_fields_inv; entailer!. }
  pose proof (proj1 (Hopen before Hinput)) as Hvalid.
  unfold current in Henabled, Hsource, Hcache |- *; rewrite Hrunning in Henabled, Hsource, Hcache |- *.
  change (os_sched_selection_enabled (os_int_exit_after_nesting entry) = true) in Henabled.
  destruct (os_int_exit_checkpoint_current_frame true entry) as [Hcur [Hprio Hrun]].
  pose proof (proj1 (os_int_exit_checkpoint_frame true entry)) as Htasks.
  assert (Hcounted_source : kernel_call_task_source returned (os_int_exit_after_nesting entry)).
  { destruct Hsource as [Horigin [Hactive Hcurrent]].
    split; [exact Horigin|]. split.
    - change (task_invocation_active (os_int_exit_ready_checkpoint true entry).(TskState)
        returned.(os_sched_call_invocation) returned.(os_sched_call_origin)) in Hactive.
      rewrite Htasks in Hactive; exact Hactive.
    - unfold task_execution_current in Hcurrent |- *; rewrite Horigin in Hcurrent |- *.
      change ((os_int_exit_ready_checkpoint true entry).(SchedState).(curTaskID) =
        Some returned.(os_sched_call_stack).(stackLeaseSlot)) in Hcurrent.
      rewrite Hcur in Hcurrent; exact Hcurrent. }
  assert (Hcounted_cache : sched_current_consistency
    (os_int_exit_after_nesting entry).(TskState) (os_int_exit_after_nesting entry).(SchedState)).
  { change (sched_current_consistency (os_int_exit_ready_checkpoint true entry).(TskState)
      (os_int_exit_ready_checkpoint true entry).(SchedState)) in Hcache.
    unfold sched_current_consistency in Hcache |- *.
    rewrite Hcur, Hprio, Htasks in Hcache; exact Hcache. }
  pose proof (os_int_exit_returned_selection_nonempty _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hcomplete Hrunning Henabled) as Hnonempty.
  change (os_sched_task_current_ready returned (os_sched_prefix_state (os_int_exit_after_nesting entry))).
  eapply os_sched_nonswitch_current_ready_at.
  - apply os_int_exit_after_nesting_preserves_validity; exact Hvalid.
  - exact Hcounted_source.
  - exact Hcounted_cache.
  - exact Henabled.
  - exact Hnoswitch.
  - exact Hnonempty.
Qed.

(** This is exactly the old conditional-ready obligation. The TaskSource
    and normal return are produced by the actual terminal receipt; the
    entry source/ready pair remains inside the implication. *)
Lemma os_int_exit_first_level_c_step_conditional_ready :
  forall environment critical sg original initial before input stopped current after output returned,
  os_int_exit_first_level_c_step environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    initial before input stopped current after output ->
  os_sched_selection_enabled initial = true ->
  kernel_call_normal_return original initial returned current ->
  kernel_call_task_source returned current ->
  ((kernel_call_task_source original initial /\ flag_pend_current_ready original initial) ->
    flag_pend_current_ready returned current).
Proof.
  intros until returned; intros Hstep Henabled Hnormal Hreturned [Hsource Hready].
  assert (Hrange : task_in_range sg initial.(TskState)).
  { destruct Hstep.
    pose proof (proj1 (os_int_exit_first_level_entry_c_resources _ _ _ _ _ _ _ _ _ _ _ _ H)) as Hinput.
    assert (Hopen : os_int_exit_first_level_entry_input environment sg initial handler suspended entry_local entry_frame |--
      coq_prop (UCOS2_state_inv sg initial) &&
      os_int_exit_first_level_entry_input environment sg initial handler suspended entry_local entry_frame).
    { unfold os_int_exit_first_level_entry_input, UCOS2_fields_inv; entailer!. }
    exact (proj1 (proj2 (proj1 (Hopen before Hinput)))). }
  pose proof (flag_pend_current_ready_implies_current_consistency original initial Hready) as Hcache.
  pose proof (kernel_c_sequence_completed_current_cache
    (os_int_exit_first_level_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin)) sg original returned
    (os_int_exit_first_level_c_step_preserves_observer environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    (os_int_exit_first_level_c_step_observer_lifetime environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial before input stopped current after output (KernelCSequenceAtom _ _ _ _ _ _ _ _ Hstep)
    Hrange Hsource Hcache Hnormal Hreturned) as [Hstop Hfinal_cache].
  pose proof (os_int_exit_first_level_c_step_control _ _ _ _ _ _ _ _ _ _ _ _ Hstep) as Hcontrol.
  assert (Hfinal_enabled : os_sched_selection_enabled current = true).
  { unfold os_sched_selection_enabled in *; rewrite (proj2 Hcontrol); exact Henabled. }
  destruct Hstep.
  assert (Hobserved : observed.(SchedState).(isRunning) = true).
  { destruct (os_int_exit_first_level_body_acquired_control _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      prefix acquire H1 H3
      (os_int_exit_entry_running _ _ _ _ _ _ _ _ _ _ _ _ H)
      (os_int_exit_entry_zero _ _ _ _ _ _ _ _ _ _ _ _ H)) as [Hrunning Hrest].
    exact Hrunning. }
  change (os_sched_task_current_ready returned
    (os_int_exit_wrapper_restored_state (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
      suspended.(armv7a_continuation_stack))).
  eapply os_int_exit_returned_c_completion_current_ready;
    [exact H5|exact Hobserved|exact Hfinal_enabled|exact Hreturned|exact Hfinal_cache].
Qed.

End OSIntExitCCallReady.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module ReturnedIRQCallEndpoint.
Import PrimitiveComponent SelectedReturnedCProgram SelectedReturnedCSource
  SelectedIRQWrapperCompletion OSIntExitReturnedC OSIntExitCCallControl OSIntExitCCallEnvelope
  OSIntExitCCallCompletion ReturnedIRQEntryResources ReturnedIRQEntryReceipts ReturnedIRQEntryIdle
  ReturnedIRQCallSource ReturnedIdleSource OSIntExitCCallReady.

Section ActualCall.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (original : OsSchedCallContext).
Context (initial : UCOS2_Verify_State) (entry_node : TaskAbstractState)
  (handler : OsIntExitCallContext) (suspended : Armv7aContinuation)
  (publication : nat) (entry_local : Armv7aContinuation -> Assertion) (entry_frame : Assertion)
  (before saved_heap body_heap : model).
Let parked := armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
  suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments).
Context (body_input : Assertion) (prefix_stop : bool) (observed : UCOS2_Verify_State)
  (read_heap : model) (prefix_output read_input : Assertion) (acquire_stop : bool)
  (entry : UCOS2_Verify_State) (acquired_heap : model) (acquire_output : Assertion).
Context (prefix : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  parked body_heap body_input prefix_stop observed read_heap prefix_output).
Context (acquire : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  observed read_heap read_input acquire_stop entry acquired_heap acquire_output).
Context (observation_frame : Assertion) (local : Armv7aContinuation -> Assertion)
  (receipt : Assertion) (node : TaskAbstractState) (private_frame : Assertion) (middle after : model).
Context (returned : os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
  entry local suspended receipt original node handler private_frame acquired_heap middle after).
Context (call : os_int_exit_first_level_c_call environment critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin)
  initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
  body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
  prefix acquire local receipt private_frame).
Let final := os_int_exit_wrapper_restored_state
  (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry) suspended.(armv7a_continuation_stack).
Let resumed := armv7a_continuation_resumed_call suspended original.

(** These are source certificates on the two original C executions.
    The TaskDelete stopped branch remains in the carrier. *)
Lemma os_int_exit_first_level_c_call_endpoint :
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ acquire ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active initial.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  os_sched_selection_enabled initial = true ->
  kernel_call_normal_return original initial resumed final ->
  kernel_call_task_source resumed final ->
  flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original)
    original initial resumed final.
Proof.
  intros Hprefix_idle Hacquire_idle Horigin Hactive Henabled Hnormal Hreturned.
  pose (tail := os_int_exit_first_level_c_tail environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local receipt original node private_frame middle after returned call).
  assert (Htail_idle : kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ tail).
  { unfold tail, kernel_program_returned_sequence_idle_source; cbn [os_int_exit_first_level_c_tail].
    apply KernelCSourceAdapt, KernelCSourceThen; [exact Hprefix_idle|].
    apply KernelCSourceThen; [exact Hacquire_idle|].
    apply KernelCSourceAtom, KernelReturnedIdleExit. }
  pose proof (os_int_exit_first_level_c_call_control environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local receipt original node private_frame middle after returned call) as Hcontrol.
  destruct call as [Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge].
  pose proof (proj2 (os_int_exit_first_level_entry_c_resources _ _ _ _ _ _ _ _ _ _ _ _ Hentry)) as Hparked.
  assert (Hextract : os_int_exit_first_level_entry_output environment sg initial handler suspended entry_local entry_frame |--
    coq_prop (task_in_range sg parked.(TskState))).
  { unfold os_int_exit_first_level_entry_output, UCOS2_fields_inv; Intros.
    pose proof (proj1 (proj2 H)) as Hrange; entailer!. }
  pose proof (Hextract body_heap Hparked) as Hrange.
  pose proof (os_int_exit_first_level_entry_preserves_active _ _ _ _ _ _ _ _ _ _ _ _ Hentry
    original.(os_sched_call_invocation) original.(os_sched_call_origin) Hactive) as Hparked_active.
  assert (Hparked_running : parked.(SchedState).(isRunning) = true).
  { unfold parked; rewrite (os_int_exit_entry_sched_state _ _ _ _ _ _ _ _ _ _ _ _ Hentry).
    exact (os_int_exit_entry_running _ _ _ _ _ _ _ _ _ _ _ _ Hentry). }
  pose proof (os_int_exit_returned_c_completion_wrapper _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ returned) as Hwrapper.
  pose proof (irq_wrapper_c_completion_normal_return _ _ _ _ _ _ _ _ _ _ _ _ parked Hwrapper Horigin) as Hparked_normal.
  destruct (kernel_program_returned_completed_idle_non_idle environment critical sg original resumed
    _ _ _ _ _ _ _ tail Htail_idle Hrange Horigin Hparked_active Hparked_running Hparked_normal Hreturned)
    as [Hstop [Hidle Hnonidle]].
  pose (actual := @OSIntExitFirstLevelCStep environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local receipt original node private_frame middle after
    Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge returned).
  split.
  - eapply os_int_exit_first_level_c_step_conditional_ready;
      [exact actual|exact Henabled|exact Hnormal|exact Hreturned].
  - split.
    + intros [_ Hinitial]; apply Hidle.
      eapply os_int_exit_entry_preserves_idle_ready; [exact Hentry|exact Hinitial].
    + split.
      * intros [_ Hinitial]; apply Hnonidle.
        eapply os_int_exit_entry_preserves_non_idle; [exact Hentry|exact Hinitial].
      * exact (conj Hnormal (fun _ => Hcontrol)).
Qed.

End ActualCall.
End ReturnedIRQCallEndpoint.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module ReturnedIRQReceiptInput.
Import PrimitiveComponent OSIntExitCCallEnvelope.

Lemma flag_pend_caller_save_input_irq_receipt :
  forall environment critical local active receipt sg original mask initial handler suspended private_frame,
  handler.(os_int_exit_interrupted_call) = original ->
  handler.(os_int_exit_interrupted_mask) = mask ->
  suspended.(armv7a_continuation_stack) = original.(os_sched_call_stack) ->
  initial.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) = None ->
  (active original initial |-- receipt) ->
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller original) original mask initial **
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** private_frame) |--
  os_int_exit_first_level_entry_input environment sg initial handler suspended
    (kernel_irq_fields_local local suspended receipt)
    (unmap_table_rep sg ** private_frame).
Proof.
  intros environment critical local active receipt sg original mask initial handler suspended private_frame
    Hcall Hmask Hstack Hnone Hrecover.
  assert (Habsent : initial.(TskState).(parkedTaskStacks)
      (task_stack_key suspended.(armv7a_continuation_stack)) = None) by (rewrite Hstack; exact Hnone).
  assert (Hreceipt : kernel_irq_fields_local local suspended receipt suspended =
      coq_prop (suspended = suspended) && receipt).
  { unfold kernel_irq_fields_local; destruct task_stack_key_eq_dec; [reflexivity|contradiction]. }
  unfold flag_pend_caller_save_input, flag_pend_active_save_input,
    os_sched_fields_save_input, os_sched_fields_capsules,
    os_int_exit_first_level_entry_input, os_int_exit_frame_save_pre.
  rewrite Hcall, Hmask, Hreceipt; Intros.
  sep_apply_l_atomic (proj1 (kernel_irq_fields_local_map_absent
    _ _ _ environment.(task_stack_call_continuations) initial.(TskState)
    initial.(TskState).(parkedTaskStacks) local suspended receipt Habsent)).
  sep_apply_l_atomic Hrecover; entailer!.
Qed.

End ReturnedIRQReceiptInput.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module ReturnedIRQFamilyEnvironment.
Import PrimitiveComponent PendPhaseCandidate SelectedReturnedCProgram SelectedReturnedCSource
  SelectedIRQWrapperCompletion OSIntExitReturnedC OSIntExitCCallControl OSIntExitCCallEnvelope
  OSIntExitCCallCompletion ReturnedIRQEntryResources ReturnedIRQEntryReceipts ReturnedIRQEntryIdle
  ReturnedIRQCallSource SelectedEnvironmentCProgram SelectedEnvironmentCSource
  SelectedEnvironmentScopedEnvironment ReturnedIRQCallEndpoint ReturnedIRQReceiptInput
  FlagWaitingRecovery FlagWaitingReturnedOwner ReturnedIdleSource.

Section ActualCall.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (original : OsSchedCallContext).
Context (initial : UCOS2_Verify_State) (entry_node : TaskAbstractState)
  (handler : OsIntExitCallContext) (suspended : Armv7aContinuation) (publication : nat).
Context (input_local : Armv7aContinuation -> Assertion) (active : OsSchedCallContext -> UCOS2_Verify_State -> Assertion)
  (receipt private_input : Assertion).
Let entry_local := kernel_irq_fields_local input_local suspended receipt.
Let entry_frame := unmap_table_rep sg ** private_input.
Context (before saved_heap body_heap : model).
Let parked := armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
  suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments).
Context (body_input : Assertion) (prefix_stop : bool) (observed : UCOS2_Verify_State)
  (read_heap : model) (prefix_output read_input : Assertion) (acquire_stop : bool)
  (entry : UCOS2_Verify_State) (acquired_heap : model) (acquire_output : Assertion).
Context (prefix : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  parked body_heap body_input prefix_stop observed read_heap prefix_output).
Context (acquire : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  observed read_heap read_input acquire_stop entry acquired_heap acquire_output).
Context (observation_frame : Assertion) (local : Armv7aContinuation -> Assertion)
  (node : TaskAbstractState) (private_output : Assertion) (middle after : model).
Context (returned : os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
  entry local suspended receipt original node handler private_output acquired_heap middle after).
Context (call : os_int_exit_first_level_c_call environment critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin)
  initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
  body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
  prefix acquire local receipt private_output).
Let final := os_int_exit_wrapper_restored_state
  (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry) suspended.(armv7a_continuation_stack).
Let resumed := armv7a_continuation_resumed_call suspended original.
Let private_before_owner := task_stack_fragments_rep handler.(os_int_exit_handler_stack)
  handler.(os_int_exit_handler_fragments) ** private_input.
Let private_after_owner := task_stack_fragments_rep handler.(os_int_exit_handler_stack)
  handler.(os_int_exit_handler_fragments) ** private_output.

(** This local constructor combines source-preserving adaptations.  The
    exported family producers below prove both receipt consequences from
    their actual C completion; callers do not supply a recovery law. *)
Local Lemma recovered_call_environment : forall event_observer,
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ acquire ->
  (active original initial |-- receipt) ->
  (flag_pend_caller_save_input environment critical input_local active sg (FlagPendTaskCaller original)
    original handler.(os_int_exit_interrupted_mask) initial ** private_before_owner) before ->
  flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original) original initial resumed final ->
  (irq_wrapper_c_output environment sg
    (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
    local suspended receipt original handler (unmap_table_rep sg ** private_output) |--
    flag_pend_caller_save_input environment critical local active sg (FlagPendTaskCaller resumed) resumed
      (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) final ** private_after_owner) ->
  exists (run : flag_pend_scoped_environment_run environment critical input_local local active sg
    original handler.(os_int_exit_interrupted_mask) initial before private_before_owner
    (orb prefix_stop (orb acquire_stop false)) resumed final after private_after_owner),
  flag_pend_scoped_environment_source environment critical input_local local active sg event_observer
    original handler.(os_int_exit_interrupted_mask) initial before private_before_owner
    (orb prefix_stop (orb acquire_stop false)) resumed final after private_after_owner run.
Proof.
  intros event_observer Hprefix_source Hacquire_source Hreceipt Hinput Hendpoint Hrecover.
  pose proof (os_int_exit_first_level_c_call_original environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local receipt original node private_output middle after returned call) as Hcall.
  destruct call as [Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge].
  destruct (armv7a_save_transition_observations _ _ _ environment.(task_stack_call_continuations)
    handler suspended before saved_heap (os_int_exit_entry_actual_save _ _ _ _ _ _ _ _ _ _ _ _ Hentry))
    as [Hentry_source [Hsaved_call [Hbinding [Hmask Hrest]]]].
  assert (Hstack : suspended.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { unfold armv7a_continuation_binding in Hbinding; rewrite Hsaved_call in Hbinding.
    rewrite Hcall; symmetry; exact (proj2 Hbinding). }
  assert (Hnone : initial.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) = None).
  { rewrite Hcall; exact (os_int_exit_entry_not_parked _ _ _ _ _ _ _ _ _ _ _ _ Hentry). }
  pose proof (flag_pend_caller_save_input_irq_receipt environment critical input_local active receipt sg
    original handler.(os_int_exit_interrupted_mask) initial handler suspended private_input
    (eq_sym Hcall) eq_refl Hstack Hnone Hreceipt) as Hpre.
  pose (actual := @OSIntExitFirstLevelCStep environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local receipt original node private_output middle after
    Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge returned).
  pose (step := @KernelProgramEnvironmentIRQCall environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ actual).
  pose (one := KernelCSequenceAtom _ _ _ _ _ _ _ _ step).
  assert (Hpost : irq_wrapper_c_output environment sg
    (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
    local suspended receipt original handler (unmap_table_rep sg ** private_output) |--
    coq_prop (flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original)
      original initial resumed final) &&
    (flag_pend_caller_save_input environment critical local active sg (FlagPendTaskCaller resumed)
      resumed handler.(os_int_exit_interrupted_mask) final ** private_after_owner)).
  { intros heap Howned; split; [exact Hendpoint|].
    rewrite <- Hmask; exact (Hrecover heap Howned). }
  exists (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput Hpre one Hpost).
  unfold flag_pend_scoped_environment_source, kernel_program_environment_c_sequence_source.
  apply KernelCSourceAdapt; unfold one; apply KernelCSourceAtom.
  unfold step; apply KernelProgramEnvironmentIRQCallSource; unfold actual; constructor; assumption.
Qed.

End ActualCall.


Section FreshCall.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (original : OsSchedCallContext).
Context (reference : OsSchedCallContext).
Context (initial : UCOS2_Verify_State) (entry_node : TaskAbstractState)
  (handler : OsIntExitCallContext) (suspended : Armv7aContinuation) (publication : nat).
Context (input_local : Armv7aContinuation -> Assertion) (private_input : Assertion).
Let active := flag_pend_fresh_observation reference.
Let receipt := active original initial.
Let entry_local := kernel_irq_fields_local input_local suspended receipt.
Let entry_frame := unmap_table_rep sg ** private_input.
Context (before saved_heap body_heap : model).
Let parked := armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
  suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments).
Context (body_input : Assertion) (prefix_stop : bool) (observed : UCOS2_Verify_State)
  (read_heap : model) (prefix_output read_input : Assertion) (acquire_stop : bool)
  (entry : UCOS2_Verify_State) (acquired_heap : model) (acquire_output : Assertion).
Context (prefix : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  parked body_heap body_input prefix_stop observed read_heap prefix_output).
Context (acquire : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  observed read_heap read_input acquire_stop entry acquired_heap acquire_output).
Context (observation_frame : Assertion) (local : Armv7aContinuation -> Assertion)
  (node : TaskAbstractState) (private_output : Assertion) (middle after : model).
Context (returned : os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
  entry local suspended receipt original node handler private_output acquired_heap middle after).
Context (call : os_int_exit_first_level_c_call environment critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin)
  initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
  body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
  prefix acquire local receipt private_output).
Let final := os_int_exit_wrapper_restored_state
  (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry) suspended.(armv7a_continuation_stack).
Let resumed := armv7a_continuation_resumed_call suspended original.
Let private_before_owner := task_stack_fragments_rep handler.(os_int_exit_handler_stack)
  handler.(os_int_exit_handler_fragments) ** private_input.
Let private_after_owner := task_stack_fragments_rep handler.(os_int_exit_handler_stack)
  handler.(os_int_exit_handler_fragments) ** private_output.

Lemma os_int_exit_fresh_call_environment : forall event_observer,
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ acquire ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ acquire ->
  os_sched_selection_enabled initial = true ->
  (flag_pend_caller_save_input environment critical input_local active sg (FlagPendTaskCaller original)
    original handler.(os_int_exit_interrupted_mask) initial ** private_before_owner) before ->
  kernel_call_task_source resumed final /\
  exists (run : flag_pend_scoped_environment_run environment critical input_local local active sg
    original handler.(os_int_exit_interrupted_mask) initial before private_before_owner
    (orb prefix_stop (orb acquire_stop false)) resumed final after private_after_owner),
  flag_pend_scoped_environment_source environment critical input_local local active sg event_observer
    original handler.(os_int_exit_interrupted_mask) initial before private_before_owner
    (orb prefix_stop (orb acquire_stop false)) resumed final after private_after_owner run.
Proof.
  intros event_observer Hprefix_source Hacquire_source Hprefix_idle Hacquire_idle Henabled Hinput.
  assert (Hextract : (flag_pend_caller_save_input environment critical input_local active sg
      (FlagPendTaskCaller original) original handler.(os_int_exit_interrupted_mask) initial ** private_before_owner) |--
      coq_prop (flag_active_fresh_registration reference original initial)).
  { unfold active, flag_pend_caller_save_input, flag_pend_active_save_input, flag_pend_fresh_observation; entailer!. }
  destruct (ReturnedFreshRecovery.flag_active_fresh_registration_call_activity _ _ _ (Hextract before Hinput))
    as [Horigin Hactive].
  destruct (ReturnedIRQFreshCaller.os_int_exit_fresh_c_call_caller_output environment critical sg reference original
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local node private_output middle after returned call)
    as [Hreturned [Hnormal [Hcontrol Hrecover]]].
  pose proof (os_int_exit_first_level_c_call_endpoint environment critical sg original
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local receipt node private_output middle after returned call
    Hprefix_idle Hacquire_idle Horigin Hactive Henabled Hnormal Hreturned) as Hendpoint.
  split; [exact Hreturned|].
  eapply (recovered_call_environment environment critical sg original initial entry_node handler suspended
    publication input_local active receipt private_input before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local node private_output middle after returned call event_observer);
    [exact Hprefix_source|exact Hacquire_source| |exact Hinput|exact Hendpoint|exact Hrecover].
  intros heap H; exact H.
Qed.

End FreshCall.

Section FirstCall.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (original : OsSchedCallContext).
Context (mode : Z) (reference : OsSchedCallContext) (reference_state : UCOS2_Verify_State).
Context (initial : UCOS2_Verify_State) (entry_node : TaskAbstractState)
  (handler : OsIntExitCallContext) (suspended : Armv7aContinuation) (publication : nat).
Context (input_local : Armv7aContinuation -> Assertion) (private_input : Assertion).
Let active := flag_pend_first_observation mode reference reference_state.
Let receipt := active original initial.
Let entry_local := kernel_irq_fields_local input_local suspended receipt.
Let entry_frame := unmap_table_rep sg ** private_input.
Context (before saved_heap body_heap : model).
Let parked := armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
  suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments).
Context (body_input : Assertion) (prefix_stop : bool) (observed : UCOS2_Verify_State)
  (read_heap : model) (prefix_output read_input : Assertion) (acquire_stop : bool)
  (entry : UCOS2_Verify_State) (acquired_heap : model) (acquire_output : Assertion).
Context (prefix : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  parked body_heap body_input prefix_stop observed read_heap prefix_output).
Context (acquire : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  observed read_heap read_input acquire_stop entry acquired_heap acquire_output).
Context (observation_frame : Assertion) (local : Armv7aContinuation -> Assertion)
  (node : TaskAbstractState) (private_output : Assertion) (middle after : model).
Context (returned : os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
  entry local suspended receipt original node handler private_output acquired_heap middle after).
Context (call : os_int_exit_first_level_c_call environment critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin)
  initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
  body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
  prefix acquire local receipt private_output).
Let final := os_int_exit_wrapper_restored_state
  (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry) suspended.(armv7a_continuation_stack).
Let resumed := armv7a_continuation_resumed_call suspended original.
Let private_before_owner := task_stack_fragments_rep handler.(os_int_exit_handler_stack)
  handler.(os_int_exit_handler_fragments) ** private_input.
Let private_after_owner := task_stack_fragments_rep handler.(os_int_exit_handler_stack)
  handler.(os_int_exit_handler_fragments) ** private_output.

Lemma os_int_exit_first_call_environment : forall event_observer,
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ acquire ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ acquire ->
  os_sched_selection_enabled initial = true ->
  (flag_pend_valid_mode mode \/ flag_pend_task_entry reference reference_state) ->
  (flag_pend_caller_save_input environment critical input_local active sg (FlagPendTaskCaller original)
    original handler.(os_int_exit_interrupted_mask) initial ** private_before_owner) before ->
  kernel_call_task_source resumed final /\
  exists (run : flag_pend_scoped_environment_run environment critical input_local local active sg
    original handler.(os_int_exit_interrupted_mask) initial before private_before_owner
    (orb prefix_stop (orb acquire_stop false)) resumed final after private_after_owner),
  flag_pend_scoped_environment_source environment critical input_local local active sg event_observer
    original handler.(os_int_exit_interrupted_mask) initial before private_before_owner
    (orb prefix_stop (orb acquire_stop false)) resumed final after private_after_owner run.
Proof.
  intros event_observer Hprefix_source Hacquire_source Hprefix_idle Hacquire_idle Henabled Hguard Hinput.
  assert (Hextract : (flag_pend_caller_save_input environment critical input_local active sg
      (FlagPendTaskCaller original) original handler.(os_int_exit_interrupted_mask) initial ** private_before_owner) |--
      coq_prop (flag_active_fresh_registration reference original initial)).
  { unfold active, flag_pend_caller_save_input, flag_pend_active_save_input, flag_pend_first_observation; entailer!. }
  destruct (ReturnedFreshRecovery.flag_active_fresh_registration_call_activity _ _ _ (Hextract before Hinput))
    as [Horigin Hactive].
  destruct (ReturnedIRQFirstCaller.os_int_exit_first_observation_c_call_caller_output environment critical sg reference original mode reference_state Hguard
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local node private_output middle after returned call)
    as [Hreturned [Hnormal [Hcontrol Hrecover]]].
  pose proof (os_int_exit_first_level_c_call_endpoint environment critical sg original
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local receipt node private_output middle after returned call
    Hprefix_idle Hacquire_idle Horigin Hactive Henabled Hnormal Hreturned) as Hendpoint.
  split; [exact Hreturned|].
  eapply (recovered_call_environment environment critical sg original initial entry_node handler suspended
    publication input_local active receipt private_input before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local node private_output middle after returned call event_observer);
    [exact Hprefix_source|exact Hacquire_source| |exact Hinput|exact Hendpoint|exact Hrecover].
  intros heap H; exact H.
Qed.

End FirstCall.

Section WaitingCall.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (original : OsSchedCallContext).
Context (reference : OsSchedCallContext) (pointer : addr).
Context (initial : UCOS2_Verify_State) (entry_node : TaskAbstractState)
  (handler : OsIntExitCallContext) (suspended : Armv7aContinuation) (publication : nat).
Context (input_local : Armv7aContinuation -> Assertion) (private_input : Assertion).
Let active := flag_pend_wait_active sg reference pointer.
Let receipt := flag_pend_waiting_receipt sg reference pointer original initial.
Let entry_local := kernel_irq_fields_local input_local suspended receipt.
Let entry_frame := unmap_table_rep sg ** private_input.
Context (before saved_heap body_heap : model).
Let parked := armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
  suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments).
Context (body_input : Assertion) (prefix_stop : bool) (observed : UCOS2_Verify_State)
  (read_heap : model) (prefix_output read_input : Assertion) (acquire_stop : bool)
  (entry : UCOS2_Verify_State) (acquired_heap : model) (acquire_output : Assertion).
Context (prefix : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  parked body_heap body_input prefix_stop observed read_heap prefix_output).
Context (acquire : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  observed read_heap read_input acquire_stop entry acquired_heap acquire_output).
Context (observation_frame : Assertion) (local : Armv7aContinuation -> Assertion)
  (node : TaskAbstractState) (private_output : Assertion) (middle after : model).
Context (returned : os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
  entry local suspended receipt original node handler private_output acquired_heap middle after).
Context (call : os_int_exit_first_level_c_call environment critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin)
  initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
  body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
  prefix acquire local receipt private_output).
Let final := os_int_exit_wrapper_restored_state
  (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry) suspended.(armv7a_continuation_stack).
Let resumed := armv7a_continuation_resumed_call suspended original.
Let private_before_owner := task_stack_fragments_rep handler.(os_int_exit_handler_stack)
  handler.(os_int_exit_handler_fragments) ** private_input.
Let private_after_owner := task_stack_fragments_rep handler.(os_int_exit_handler_stack)
  handler.(os_int_exit_handler_fragments) ** private_output.

Lemma os_int_exit_waiting_call_environment : forall event_observer,
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ acquire ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ acquire ->
  os_sched_selection_enabled initial = true ->
  ((exists waiter, entry.(FlagState).(flagWaitNodes) pointer = Some waiter) \/
    initial.(FlagState).(flagWaitNodes) pointer = None) ->
  (flag_pend_caller_save_input environment critical input_local active sg (FlagPendTaskCaller original)
    original handler.(os_int_exit_interrupted_mask) initial ** private_before_owner) before ->
  kernel_call_task_source resumed final /\
  exists (run : flag_pend_scoped_environment_run environment critical input_local local active sg
    original handler.(os_int_exit_interrupted_mask) initial before private_before_owner
    (orb prefix_stop (orb acquire_stop false)) resumed final after private_after_owner),
  flag_pend_scoped_environment_source environment critical input_local local active sg event_observer
    original handler.(os_int_exit_interrupted_mask) initial before private_before_owner
    (orb prefix_stop (orb acquire_stop false)) resumed final after private_after_owner run.
Proof.
  intros event_observer Hprefix_source Hacquire_source Hprefix_idle Hacquire_idle Henabled Hcase Hinput.
  assert (Hextract : (flag_pend_caller_save_input environment critical input_local active sg
      (FlagPendTaskCaller original) original handler.(os_int_exit_interrupted_mask) initial ** private_before_owner) |--
      coq_prop (flag_active_waiting_registration reference pointer original initial /\
        task_idle_ready sg initial.(TskState) /\ flag_pend_non_idle_at sg reference initial)).
  { unfold active, flag_pend_caller_save_input, flag_pend_active_save_input, flag_pend_wait_active, flag_active_waiting; entailer!. }
  destruct (Hextract before Hinput) as [Hregistration [Hidle Hnonidle]].
  destruct (flag_waiting_registration_call_activity _ _ _ _ Hregistration) as [Horigin Hactive].
  destruct (ReturnedIRQWaitingCaller.os_int_exit_waiting_c_call_caller_output environment critical sg reference original pointer
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local node private_output middle after returned call Hprefix_idle Hacquire_idle Hidle Hnonidle Hcase)
    as [Hreturned [Hnormal [Hcontrol Hrecover]]].
  pose proof (os_int_exit_first_level_c_call_endpoint environment critical sg original
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local receipt node private_output middle after returned call
    Hprefix_idle Hacquire_idle Horigin Hactive Henabled Hnormal Hreturned) as Hendpoint.
  split; [exact Hreturned|].
  eapply (recovered_call_environment environment critical sg original initial entry_node handler suspended
    publication input_local active receipt private_input before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local node private_output middle after returned call event_observer);
    [exact Hprefix_source|exact Hacquire_source| |exact Hinput|exact Hendpoint|exact Hrecover].
  unfold active, receipt, flag_pend_wait_active, flag_pend_waiting_receipt; entailer!.
Qed.

End WaitingCall.

End ReturnedIRQFamilyEnvironment.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SelectedSequenceScopedLift.
Import PrimitiveComponent SelectedCProgram SelectedCSource
  SelectedIRQWrapperSegment SelectedIRQWrapperSource SelectedReturnedCProgram SelectedReturnedCSource
  SelectedEnvironmentCProgram SelectedEnvironmentCSource SelectedEnvironmentScopedEnvironment.

Definition kernel_program_selected_environment_sequence
  environment critical sg observer origin state before input stopped current after output
  (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    state before input stopped current after output) :
  kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer origin)
    state before input stopped current after output :=
  kernel_program_environment_sequence_include environment critical sg observer origin _ _ _ _ _ _ _
    (kernel_program_returned_sequence_include environment critical sg observer origin _ _ _ _ _ _ _
      (kernel_program_wrapper_sequence_include environment critical sg observer origin _ _ _ _ _ _ _ run)).

Lemma kernel_program_selected_environment_sequence_source :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      state before input stopped current after output),
  kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ run ->
  kernel_program_environment_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _
    (kernel_program_selected_environment_sequence environment critical sg observer origin _ _ _ _ _ _ _ run).
Proof.
  intros until run; intro Hsource; unfold kernel_program_selected_environment_sequence.
  apply kernel_program_environment_sequence_include_source,
    kernel_program_returned_sequence_include_source,
    kernel_program_wrapper_sequence_include_source; exact Hsource.
Qed.

(** The original selected run itself is embedded, including its source
    proof. Empty private resources preserve the two original heap cuts. *)
Lemma selected_c_sequence_scoped_environment :
  forall environment critical local next_local active sg event_observer original mask initial before
    stopped returned current after
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial before
      (flag_pend_caller_save_input environment critical local active sg
        (FlagPendTaskCaller original) original mask initial)
      stopped current after
      (coq_prop (flag_pend_call_endpoint_observations environment sg
        (FlagPendTaskCaller original) original initial returned current) &&
       flag_pend_caller_save_input environment critical next_local active sg
        (FlagPendTaskCaller returned) returned mask current)),
  kernel_program_selected_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer
    _ _ _ _ _ _ _ run ->
  exists (scoped : flag_pend_scoped_environment_run environment critical local next_local active sg
    original mask initial before emp stopped returned current after emp),
  flag_pend_scoped_environment_source environment critical local next_local active sg event_observer
    original mask initial before emp stopped returned current after emp scoped.
Proof.
  intros until run; intro Hsource.
  pose (included := kernel_program_selected_environment_sequence environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ run).
  pose proof (kernel_program_selected_environment_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ run Hsource) as Hincluded.
  pose proof (proj1 (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ included)) as Hinput.
  assert (Hintro : flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller original) original mask initial |--
    flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller original) original mask initial ** emp) by entailer!.
  assert (Hpre : flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller original) original mask initial ** emp |--
    flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller original) original mask initial) by entailer!.
  assert (Hpost : coq_prop (flag_pend_call_endpoint_observations environment sg
    (FlagPendTaskCaller original) original initial returned current) &&
    flag_pend_caller_save_input environment critical next_local active sg
      (FlagPendTaskCaller returned) returned mask current |--
    coq_prop (flag_pend_call_endpoint_observations environment sg
    (FlagPendTaskCaller original) original initial returned current) &&
    (flag_pend_caller_save_input environment critical next_local active sg
      (FlagPendTaskCaller returned) returned mask current ** emp)) by entailer!.
  exists (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ (Hintro before Hinput) Hpre included Hpost).
  unfold flag_pend_scoped_environment_source, kernel_program_environment_c_sequence_source.
  apply KernelCSourceAdapt; exact Hincluded.
Qed.

End SelectedSequenceScopedLift.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SelectedFreshEnvironment.
Import PrimitiveComponent PendPhaseCandidate SelectedCProgram SelectedCSource
  FlagPendFreshRecovery FlagPendFreshSource SelectedSequenceScopedLift
  SelectedEnvironmentCProgram SelectedEnvironmentCSource SelectedEnvironmentScopedEnvironment
  SelectedCompletionComposition.

Lemma selected_sequence_fresh_receipt :
  forall environment critical sg observer origin initial before input stopped current after output
    reference original returned,
  kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    initial before input stopped current after output ->
  task_tcb_init_stack_same_call returned original ->
  kernel_call_task_source returned current ->
  flag_pend_fresh_observation reference original initial |--
    flag_pend_fresh_observation reference returned current.
Proof.
  intros until returned; intros Hrun Hsame Hreturned heap [Hregistration Hempty].
  assert (Hsame_reference : task_tcb_init_stack_same_call returned reference).
  { destruct Hregistration as [task [[Hinitial Hrest] Hclear]].
    unfold task_tcb_init_stack_same_call in *; destruct Hsame as [Hi [Ho Hs]].
    destruct Hinitial as [Hi' [Ho' Hs']]; repeat split; congruence. }
  apply (flag_pend_fresh_observation_from_returned_source reference returned current Hsame_reference Hreturned);
    [|exact Hempty].
  eapply kernel_program_selected_c_sequence_preserves_fresh_fields; [exact Hrun|].
  exact (flag_active_fresh_registration_fields reference original initial Hregistration).
Qed.

Lemma selected_sequence_first_receipt :
  forall environment critical sg observer origin initial before input stopped current after output
    mode reference reference_state original returned,
  kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    initial before input stopped current after output ->
  task_tcb_init_stack_same_call returned original ->
  kernel_call_task_source returned current ->
  flag_pend_first_observation mode reference reference_state original initial |--
    flag_pend_first_observation mode reference reference_state returned current.
Proof.
  intros until returned; intros Hrun Hsame Hreturned heap [Hregistration Hempty].
  split; [|exact Hempty]; intro Hguard.
  exact (proj1 (selected_sequence_fresh_receipt environment critical sg observer origin
    initial before input stopped current after output reference original returned Hrun Hsame Hreturned
    heap (conj (Hregistration Hguard) Hempty))).
Qed.

Local Lemma selected_receipt_return_environment :
  forall environment critical initial_local next_local active receipt frame sg original saved acquired initial first_heap
    stopped returned current restored arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written middle final_cursor after
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap
      (flag_pend_caller_save_input environment critical initial_local active sg
        (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial)
      stopped current restored
      (coq_prop (flag_pend_call_endpoint_observations environment sg
        (FlagPendTaskCaller original) original initial returned current) &&
       flag_pend_caller_restore_input environment critical next_local (fun _ _ => receipt ** frame) sg
        (FlagPendTaskCaller returned) returned saved acquired current)),
  kernel_program_selected_c_sequence_source environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ run ->
  (receipt |-- active returned current) ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor restored written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  exists (scoped : flag_pend_scoped_environment_run environment critical initial_local next_local active sg
    original (armv7a_irq_fiq_mask saved) initial first_heap emp
    (orb stopped false) returned current after frame),
  flag_pend_scoped_environment_source environment critical initial_local next_local active sg None
    original (armv7a_irq_fiq_mask saved) initial first_heap emp
    (orb stopped false) returned current after frame scoped.
Proof.
  intros until run; intros Hsource Hrecover Hr0 Hmask Hprefix Hsuffix.
  destruct (selected_c_sequence_restore_preserves_packet environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None next_local
    (fun _ _ => receipt ** frame) returned saved acquired initial first_heap _ stopped current restored _
    arch restore cursor written middle final_cursor after run Hsource Hr0 Hmask Hprefix Hsuffix)
    as [completed [Hprimitive Hcompleted_source]].
  pose (included := kernel_program_selected_environment_sequence environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ completed).
  pose proof (kernel_program_selected_environment_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ completed Hcompleted_source) as Hincluded.
  pose proof (proj1 (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ included)) as Hinput.
  assert (Hintro : flag_pend_caller_save_input environment critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial |--
    flag_pend_caller_save_input environment critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial ** emp) by entailer!.
  assert (Hpre : flag_pend_caller_save_input environment critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial ** emp |--
    flag_pend_caller_save_input environment critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial) by entailer!.
  assert (Hpost :
    coq_prop (flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original)
      original initial returned current) &&
    (flag_pend_task_restore_c_event environment critical next_local (fun _ _ => receipt ** frame) sg
      returned saved acquired current restored after).(flag_pend_event_output) |--
    coq_prop (flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original)
      original initial returned current) &&
    (flag_pend_caller_save_input environment critical next_local active sg
      (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current ** frame)).
  { cbn [flag_pend_task_restore_c_event flag_pend_event_output].
    unfold flag_pend_caller_save_input, flag_pend_active_save_input; Intros.
    sep_apply_l_atomic Hrecover; entailer!. }
  exists (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ (Hintro first_heap Hinput) Hpre included Hpost).
  unfold flag_pend_scoped_environment_source, kernel_program_environment_c_sequence_source.
  apply KernelCSourceAdapt; exact Hincluded.
Qed.

Lemma selected_fresh_return_environment :
  forall environment critical initial_local next_local frame sg reference original saved acquired initial first_heap
    stopped returned current restored arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written middle final_cursor after
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap
      (flag_pend_caller_save_input environment critical initial_local (flag_pend_fresh_observation reference) sg
        (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial)
      stopped current restored
      (coq_prop (flag_pend_call_endpoint_observations environment sg
        (FlagPendTaskCaller original) original initial returned current) &&
       flag_pend_caller_restore_input environment critical next_local
        (fun _ _ => flag_pend_fresh_observation reference original initial ** frame) sg
        (FlagPendTaskCaller returned) returned saved acquired current)),
  kernel_program_selected_c_sequence_source environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ run ->
  kernel_call_task_source returned current ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor restored written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  exists (scoped : flag_pend_scoped_environment_run environment critical initial_local next_local
    (flag_pend_fresh_observation reference) sg original (armv7a_irq_fiq_mask saved) initial first_heap emp
    (orb stopped false) returned current after frame),
  flag_pend_scoped_environment_source environment critical initial_local next_local (flag_pend_fresh_observation reference) sg None
    original (armv7a_irq_fiq_mask saved) initial first_heap emp
    (orb stopped false) returned current after frame scoped.
Proof.
  intros until run; intros Hsource Hreturned Hr0 Hmask Hprefix Hsuffix.
  pose proof (proj1 (proj2 (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ run))) as Hendpoint.
  destruct Hendpoint as [Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]].
  eapply (selected_receipt_return_environment environment critical initial_local next_local
    (flag_pend_fresh_observation reference) (flag_pend_fresh_observation reference original initial)
    frame sg original saved acquired initial first_heap stopped returned current restored arch restore
    cursor written middle final_cursor after run); try eassumption.
  eapply selected_sequence_fresh_receipt; [exact run|exact (proj1 Hnormal)|exact Hreturned].
Qed.

Lemma selected_first_return_environment :
  forall environment critical initial_local next_local frame sg mode reference reference_state original saved acquired initial first_heap
    stopped returned current restored arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written middle final_cursor after
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap
      (flag_pend_caller_save_input environment critical initial_local
        (flag_pend_first_observation mode reference reference_state) sg
        (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial)
      stopped current restored
      (coq_prop (flag_pend_call_endpoint_observations environment sg
        (FlagPendTaskCaller original) original initial returned current) &&
       flag_pend_caller_restore_input environment critical next_local
        (fun _ _ => flag_pend_first_observation mode reference reference_state original initial ** frame) sg
        (FlagPendTaskCaller returned) returned saved acquired current)),
  kernel_program_selected_c_sequence_source environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ run ->
  kernel_call_task_source returned current ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor restored written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  exists (scoped : flag_pend_scoped_environment_run environment critical initial_local next_local
    (flag_pend_first_observation mode reference reference_state) sg
    original (armv7a_irq_fiq_mask saved) initial first_heap emp
    (orb stopped false) returned current after frame),
  flag_pend_scoped_environment_source environment critical initial_local next_local
    (flag_pend_first_observation mode reference reference_state) sg None
    original (armv7a_irq_fiq_mask saved) initial first_heap emp
    (orb stopped false) returned current after frame scoped.
Proof.
  intros until run; intros Hsource Hreturned Hr0 Hmask Hprefix Hsuffix.
  pose proof (proj1 (proj2 (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ run))) as Hendpoint.
  destruct Hendpoint as [Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]].
  eapply (selected_receipt_return_environment environment critical initial_local next_local
    (flag_pend_first_observation mode reference reference_state)
    (flag_pend_first_observation mode reference reference_state original initial)
    frame sg original saved acquired initial first_heap stopped returned current restored arch restore
    cursor written middle final_cursor after run); try eassumption.
  eapply selected_sequence_first_receipt; [exact run|exact (proj1 Hnormal)|exact Hreturned].
Qed.

End SelectedFreshEnvironment.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SelectedFamilyScope.
Import PrimitiveComponent PendPhaseCandidate SelectedCProgram SelectedCSource
  SelectedFreshEnvironment SelectedSequenceScopedLift SelectedEnvironmentCProgram
  SelectedEnvironmentCSource SelectedEnvironmentScopedEnvironment SelectedCompletionComposition.

Lemma selected_receipt_return_environment :
  forall environment critical initial_local next_local initial_private active receipt frame sg original saved acquired initial first_heap
    stopped returned current restored arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written middle final_cursor after
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap
      (flag_pend_caller_save_input environment critical initial_local active sg
        (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial ** initial_private)
      stopped current restored
      (coq_prop (flag_pend_call_endpoint_observations environment sg
        (FlagPendTaskCaller original) original initial returned current) &&
       flag_pend_caller_restore_input environment critical next_local (fun _ _ => receipt ** frame) sg
        (FlagPendTaskCaller returned) returned saved acquired current)),
  kernel_program_selected_c_sequence_source environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ run ->
  (receipt |-- active returned current) ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor restored written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  exists (scoped : flag_pend_scoped_environment_run environment critical initial_local next_local active sg
    original (armv7a_irq_fiq_mask saved) initial first_heap initial_private
    (orb stopped false) returned current after frame),
  flag_pend_scoped_environment_source environment critical initial_local next_local active sg None
    original (armv7a_irq_fiq_mask saved) initial first_heap initial_private
    (orb stopped false) returned current after frame scoped.
Proof.
  intros until run; intros Hsource Hrecover Hr0 Hmask Hprefix Hsuffix.
  destruct (selected_c_sequence_restore_preserves_packet environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None next_local
    (fun _ _ => receipt ** frame) returned saved acquired initial first_heap _ stopped current restored _
    arch restore cursor written middle final_cursor after run Hsource Hr0 Hmask Hprefix Hsuffix)
    as [completed [Hprimitive Hcompleted_source]].
  pose (included := kernel_program_selected_environment_sequence environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ completed).
  pose proof (kernel_program_selected_environment_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ completed Hcompleted_source) as Hincluded.
  pose proof (proj1 (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ included)) as Hinput.
  assert (Hpost :
    coq_prop (flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original)
      original initial returned current) &&
    (flag_pend_task_restore_c_event environment critical next_local (fun _ _ => receipt ** frame) sg
      returned saved acquired current restored after).(flag_pend_event_output) |--
    coq_prop (flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original)
      original initial returned current) &&
    (flag_pend_caller_save_input environment critical next_local active sg
      (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current ** frame)).
  { cbn [flag_pend_task_restore_c_event flag_pend_event_output].
    unfold flag_pend_caller_save_input, flag_pend_active_save_input; Intros.
    sep_apply_l_atomic Hrecover; entailer!. }
  exists (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput (fun heap Howner => Howner) included Hpost).
  unfold flag_pend_scoped_environment_source, kernel_program_environment_c_sequence_source.
  apply KernelCSourceAdapt; exact Hincluded.
Qed.

Lemma selected_fresh_return_environment :
  forall environment critical initial_local next_local initial_private frame sg reference original saved acquired initial first_heap
    stopped returned current restored arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written middle final_cursor after
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap
      (flag_pend_caller_save_input environment critical initial_local (flag_pend_fresh_observation reference) sg
        (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial ** initial_private)
      stopped current restored
      (coq_prop (flag_pend_call_endpoint_observations environment sg
        (FlagPendTaskCaller original) original initial returned current) &&
       flag_pend_caller_restore_input environment critical next_local
        (fun _ _ => flag_pend_fresh_observation reference original initial ** frame) sg
        (FlagPendTaskCaller returned) returned saved acquired current)),
  kernel_program_selected_c_sequence_source environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ run ->
  kernel_call_task_source returned current ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor restored written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  exists (scoped : flag_pend_scoped_environment_run environment critical initial_local next_local
    (flag_pend_fresh_observation reference) sg original (armv7a_irq_fiq_mask saved) initial first_heap initial_private
    (orb stopped false) returned current after frame),
  flag_pend_scoped_environment_source environment critical initial_local next_local (flag_pend_fresh_observation reference) sg None
    original (armv7a_irq_fiq_mask saved) initial first_heap initial_private
    (orb stopped false) returned current after frame scoped.
Proof.
  intros until run; intros Hsource Hreturned Hr0 Hmask Hprefix Hsuffix.
  pose proof (proj1 (proj2 (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ run))) as Hendpoint.
  destruct Hendpoint as [Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]].
  eapply (selected_receipt_return_environment environment critical initial_local next_local initial_private
    (flag_pend_fresh_observation reference) (flag_pend_fresh_observation reference original initial)
    frame sg original saved acquired initial first_heap stopped returned current restored arch restore
    cursor written middle final_cursor after run); try eassumption.
  eapply selected_sequence_fresh_receipt; [exact run|exact (proj1 Hnormal)|exact Hreturned].
Qed.

Lemma selected_first_return_environment :
  forall environment critical initial_local next_local initial_private frame sg mode reference reference_state original saved acquired initial first_heap
    stopped returned current restored arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written middle final_cursor after
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap
      (flag_pend_caller_save_input environment critical initial_local
        (flag_pend_first_observation mode reference reference_state) sg
        (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial ** initial_private)
      stopped current restored
      (coq_prop (flag_pend_call_endpoint_observations environment sg
        (FlagPendTaskCaller original) original initial returned current) &&
       flag_pend_caller_restore_input environment critical next_local
        (fun _ _ => flag_pend_first_observation mode reference reference_state original initial ** frame) sg
        (FlagPendTaskCaller returned) returned saved acquired current)),
  kernel_program_selected_c_sequence_source environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ run ->
  kernel_call_task_source returned current ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor restored written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  exists (scoped : flag_pend_scoped_environment_run environment critical initial_local next_local
    (flag_pend_first_observation mode reference reference_state) sg
    original (armv7a_irq_fiq_mask saved) initial first_heap initial_private
    (orb stopped false) returned current after frame),
  flag_pend_scoped_environment_source environment critical initial_local next_local
    (flag_pend_first_observation mode reference reference_state) sg None
    original (armv7a_irq_fiq_mask saved) initial first_heap initial_private
    (orb stopped false) returned current after frame scoped.
Proof.
  intros until run; intros Hsource Hreturned Hr0 Hmask Hprefix Hsuffix.
  pose proof (proj1 (proj2 (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ run))) as Hendpoint.
  destruct Hendpoint as [Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]].
  eapply (selected_receipt_return_environment environment critical initial_local next_local initial_private
    (flag_pend_first_observation mode reference reference_state)
    (flag_pend_first_observation mode reference reference_state original initial)
    frame sg original saved acquired initial first_heap stopped returned current restored arch restore
    cursor written middle final_cursor after run); try eassumption.
  eapply selected_sequence_first_receipt; [exact run|exact (proj1 Hnormal)|exact Hreturned].
Qed.

End SelectedFamilyScope.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import CriticalComponent PrimitiveComponent PendPhaseCandidate SelectedCProgram.
Import FlagWaitingRecovery FlagWaitingSuccessor FlagWaitingDetachedSequence.
Import FlagWaitingReceiptReindex FlagWaitingNodeInclusion FlagWaitingMultiPointer.
Import FlagWaitingLinkedReturn FlagWaitingPendingResult FlagWaitingPendingReturn.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagWaitingSelectedTake.

(** The original TaskSource is the real outer-completion premise.  The
    saved waiting registration supplies only same-call, never current-task.
    These facts are extracted from this run's two actual resource endpoints. *)
Lemma selected_waiting_return_facts :
  forall environment critical sg reference pointer original initial initial_local
    first_heap initial_private saved acquired stopped returned current after
    next_local receipt frame
    (run : kernel_c_sequence
      (kernel_program_selected_c_step environment critical sg
        original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap
      (flag_pend_caller_save_input environment critical initial_local
        (flag_pend_wait_active sg reference pointer) sg (FlagPendTaskCaller original)
        original (armv7a_irq_fiq_mask saved) initial ** initial_private)
      stopped current after
      (coq_prop (flag_pend_call_endpoint_observations environment sg
        (FlagPendTaskCaller original) original initial returned current) &&
       flag_pend_caller_restore_input environment critical next_local
        (fun _ _ => receipt ** frame) sg (FlagPendTaskCaller returned)
        returned saved acquired current)),
  kernel_call_task_source original initial ->
  task_tcb_init_stack_same_call returned reference /\
  UCOS2_state_inv sg current /\
  task_idle_ready sg current.(TskState) /\
  flag_pend_non_idle_at sg reference current.
Proof.
  intros environment critical sg reference pointer original initial initial_local
    first_heap initial_private saved acquired stopped returned current after
    next_local receipt frame run Horiginal.
  destruct (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ run)
    as [Hinput [Hendpoint Houtput]].
  assert (Hproject :
    flag_pend_caller_save_input environment critical initial_local
      (flag_pend_wait_active sg reference pointer) sg (FlagPendTaskCaller original)
      original (armv7a_irq_fiq_mask saved) initial ** initial_private |--
    coq_prop (flag_active_waiting_registration reference pointer original initial /\
      task_idle_ready sg initial.(TskState) /\ flag_pend_non_idle_at sg reference initial)).
  { unfold flag_pend_caller_save_input, flag_pend_active_save_input,
      flag_pend_wait_active, flag_active_waiting; entailer!. }
  destruct (Hproject first_heap Hinput) as [Hregistration [Hidle Hnonidle]].
  destruct Hregistration as [task [[Hsame Htask] Hpointer]].
  destruct Hsame as [Hi [Ho Hstack]].
  destruct Hendpoint as [Hready [Hidle_after [Hnonidle_after [Hnormal Hcontrol]]]].
  destruct (proj1 Hnormal) as [Hi' [Ho' Hstack']].
  assert (Hsame_reference : task_tcb_init_stack_same_call returned reference).
  { unfold task_tcb_init_stack_same_call; repeat split; congruence. }
  assert (Hidle_current : task_idle_ready sg current.(TskState)).
  { first [exact (Hidle_after Hidle) | exact (Hidle_after (conj Horiginal Hidle))]. }
  assert (Hnonidle_original : flag_pend_non_idle_at sg original initial).
  { unfold flag_pend_non_idle_at in *; rewrite Hstack; exact Hnonidle. }
  assert (Hnonidle_returned : flag_pend_non_idle_at sg returned current).
  { first [exact (Hnonidle_after Hnonidle_original) |
      exact (Hnonidle_after (conj Horiginal Hnonidle_original))]. }
  assert (Hnonidle_current : flag_pend_non_idle_at sg reference current).
  { unfold flag_pend_non_idle_at in *; rewrite Hstack', Hstack in Hnonidle_returned;
      exact Hnonidle_returned. }
  exact (conj Hsame_reference
    (conj (proj1 (flag_pend_caller_restore_input_state_inv environment critical next_local
      (fun _ _ => receipt ** frame) sg (FlagPendTaskCaller returned) returned saved acquired current
      after Houtput)) (conj Hidle_current Hnonidle_current))).
Qed.

(** A surviving public node is re-observed through the actual run.  The
    original fixed receipt is emp at the linked node; no private node bytes
    are created.  Both pending and timeout remain represented. *)
Lemma selected_linked_waiting_receipt :
  forall environment critical sg reference pointer original initial initial_local
    first_heap initial_private saved acquired stopped returned current after
    next_local frame waiter
    (run : kernel_c_sequence
      (kernel_program_selected_c_step environment critical sg
        original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap
      (flag_pend_caller_save_input environment critical initial_local
        (flag_pend_wait_active sg reference pointer) sg (FlagPendTaskCaller original)
        original (armv7a_irq_fiq_mask saved) initial ** initial_private)
      stopped current after
      (coq_prop (flag_pend_call_endpoint_observations environment sg
        (FlagPendTaskCaller original) original initial returned current) &&
       flag_pend_caller_restore_input environment critical next_local
        (fun _ _ => flag_pend_waiting_receipt sg reference pointer original initial ** frame)
        sg (FlagPendTaskCaller returned) returned saved acquired current)),
  kernel_call_task_source original initial ->
  kernel_call_task_source returned current ->
  current.(FlagState).(flagWaitNodes) pointer = Some waiter ->
  flag_pend_waiting_receipt sg reference pointer original initial |--
    flag_pend_wait_active sg reference pointer returned current.
Proof.
  intros environment critical sg reference pointer original initial initial_local
    first_heap initial_private saved acquired stopped returned current after
    next_local frame waiter run Horiginal Hreturned Hnode.
  destruct (selected_waiting_return_facts environment critical sg reference pointer original initial initial_local
    first_heap initial_private saved acquired stopped returned current after next_local
    (flag_pend_waiting_receipt sg reference pointer original initial) frame run Horiginal)
    as [Hsame [Hvalid [Hidle Hnonidle]]].
  pose proof (proj2 (proj2 (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ run)))
    as Houtput.
  assert (Hproject :
    flag_pend_caller_restore_input environment critical next_local
      (fun _ _ => flag_pend_waiting_receipt sg reference pointer original initial ** frame)
      sg (FlagPendTaskCaller returned) returned saved acquired current |--
    coq_prop (flag_active_waiting_registration reference pointer original initial /\
      flag_pend_wait_outcome reference pointer initial)).
  { unfold flag_pend_caller_restore_input, flag_pend_active_restore_input,
      flag_pend_waiting_receipt, flag_active_waiting; entailer!. }
  destruct (Hproject after Houtput) as [Hregistration Houtcome].
  pose proof (kernel_program_selected_c_sequence_nodes_included _ _ _ _ _ _ _ _ _ _ _ _ run) as Hnodes.
  destruct (Hnodes pointer waiter Hnode) as [previous [Hprevious Hidentity]].
  pose proof (kernel_program_selected_c_sequence_preserves_zero_multi_fields environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _
    reference.(os_sched_call_origin) run
    (flag_waiting_registration_zero_multi_fields _ _ _ _ Hregistration)) as Hmulti.
  pose proof (kernel_program_selected_c_sequence_preserves_pending_result_fields environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _
    reference.(os_sched_call_origin) run
    (flag_waiting_linked_initial_pending_result _ _ _ _ _ Hprevious Hregistration Houtcome)) as Hpending.
  destruct (flag_waiting_linked_current_observations sg initial current reference original returned pointer
    previous waiter Hregistration Hprevious Hnodes Hnode Hvalid Hmulti Hpending Hsame Hreturned)
    as [Hregistration' Houtcome'].
  unfold flag_pend_waiting_receipt, flag_pend_wait_active, flag_active_waiting,
    flag_pend_sched_node_fields_rep; rewrite Hprevious, Hnode; entailer!.
Qed.

(** This entry is already detached by its actual Post/Del producer.  The
    fixed receipt owns the private fields, and the same run transports its
    result/delay/event fields.  It does not consume an old linked receipt. *)
Lemma selected_detached_waiting_receipt :
  forall environment critical sg reference pointer original initial initial_local
    first_heap initial_private saved acquired stopped returned current after
    next_local frame
    (run : kernel_c_sequence
      (kernel_program_selected_c_step environment critical sg
        original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap
      (flag_pend_caller_save_input environment critical initial_local
        (flag_pend_wait_active sg reference pointer) sg (FlagPendTaskCaller original)
        original (armv7a_irq_fiq_mask saved) initial ** initial_private)
      stopped current after
      (coq_prop (flag_pend_call_endpoint_observations environment sg
        (FlagPendTaskCaller original) original initial returned current) &&
       flag_pend_caller_restore_input environment critical next_local
        (fun _ _ => flag_pend_waiting_receipt sg reference pointer original initial ** frame)
        sg (FlagPendTaskCaller returned) returned saved acquired current)),
  kernel_call_task_source original initial ->
  kernel_call_task_source returned current ->
  initial.(FlagState).(flagWaitNodes) pointer = None ->
  flag_pend_waiting_receipt sg reference pointer original initial |--
    flag_pend_wait_active sg reference pointer returned current.
Proof.
  intros environment critical sg reference pointer original initial initial_local
    first_heap initial_private saved acquired stopped returned current after
    next_local frame run Horiginal Hreturned Hnone.
  destruct (selected_waiting_return_facts environment critical sg reference pointer original initial initial_local
    first_heap initial_private saved acquired stopped returned current after next_local
    (flag_pend_waiting_receipt sg reference pointer original initial) frame run Horiginal)
    as [Hsame [Hvalid [Hidle Hnonidle]]].
  pose proof (proj2 (proj2 (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ run)))
    as Houtput.
  assert (Hproject :
    flag_pend_caller_restore_input environment critical next_local
      (fun _ _ => flag_pend_waiting_receipt sg reference pointer original initial ** frame)
      sg (FlagPendTaskCaller returned) returned saved acquired current |--
    coq_prop (flag_active_waiting_registration reference pointer original initial /\
      flag_pend_wait_outcome reference pointer initial)).
  { unfold flag_pend_caller_restore_input, flag_pend_active_restore_input,
      flag_pend_waiting_receipt, flag_active_waiting; entailer!. }
  destruct (Hproject after Houtput) as [Hregistration Houtcome].
  assert (Hfields : flag_pend_detached_fields_at_origin reference.(os_sched_call_origin) initial).
  { destruct Hregistration as [task [[Hsame0 [Horigin [Hlookup [Hgen [Hactive Hclear]]]]] Hpointer]].
    destruct Houtcome as [observed [Hobserved Hresult]].
    assert (observed = task) by congruence; subst observed.
    rewrite Hnone in Hpointer, Hresult; rewrite Horigin.
    intros next Hnext Hg; assert (next = task) by congruence; subst next.
    unfold flag_pend_detached_task_fields; tauto. }
  pose proof (kernel_program_selected_c_sequence_preserves_detached_fields environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _
    reference.(os_sched_call_origin) run Hfields) as Hfields_current.
  assert (Hnone_current : current.(FlagState).(flagWaitNodes) pointer = None).
  { eapply flag_wait_nodes_included_absent;
      [eapply kernel_program_selected_c_sequence_nodes_included; exact run|exact Hnone]. }
  pose proof (flag_pend_detached_receipt_current sg reference pointer original initial returned current
    Hnone Hnone_current Hfields_current Hsame Hreturned) as Hrecover.
  assert (Hactive : flag_pend_waiting_receipt sg reference pointer returned current |--
    flag_pend_wait_active sg reference pointer returned current).
  { unfold flag_pend_waiting_receipt, flag_pend_wait_active; entailer!. }
  intros heap Howned; exact (Hactive heap (Hrecover heap Howned)).
Qed.

(** Keep the exact caller owner and private frame from the same return heap.
    The disjunction distinguishes the two source phases above, not a new
    public API precondition.  Linked -> detached publication uses the
    separate actual helper/Next cut and its suffix below. *)
Lemma selected_waiting_return_owner :
  forall environment critical sg reference pointer original initial initial_local
    first_heap initial_private saved acquired stopped returned current after next_local frame
    (run : kernel_c_sequence
      (kernel_program_selected_c_step environment critical sg
        original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap
      (flag_pend_caller_save_input environment critical initial_local
        (flag_pend_wait_active sg reference pointer) sg (FlagPendTaskCaller original)
        original (armv7a_irq_fiq_mask saved) initial ** initial_private)
      stopped current after
      (coq_prop (flag_pend_call_endpoint_observations environment sg
        (FlagPendTaskCaller original) original initial returned current) &&
       flag_pend_caller_restore_input environment critical next_local
        (fun _ _ => flag_pend_waiting_receipt sg reference pointer original initial ** frame)
        sg (FlagPendTaskCaller returned) returned saved acquired current)),
  kernel_call_task_source original initial ->
  kernel_call_task_source returned current ->
  ((exists waiter, current.(FlagState).(flagWaitNodes) pointer = Some waiter) \/
    initial.(FlagState).(flagWaitNodes) pointer = None) ->
  (coq_prop (flag_pend_call_endpoint_observations environment sg
    (FlagPendTaskCaller original) original initial returned current) &&
   flag_pend_caller_restore_input environment critical next_local
    (fun call state => flag_pend_wait_active sg reference pointer call state ** frame)
    sg (FlagPendTaskCaller returned) returned saved acquired current) after.
Proof.
  intros environment critical sg reference pointer original initial initial_local
    first_heap initial_private saved acquired stopped returned current after
    next_local frame run Horiginal Hreturned Hcase.
  assert (Hrecover : flag_pend_waiting_receipt sg reference pointer original initial |--
    flag_pend_wait_active sg reference pointer returned current).
  { destruct Hcase as [[waiter Hnode]|Hnone].
    - eapply selected_linked_waiting_receipt; eassumption.
    - eapply selected_detached_waiting_receipt; eassumption. }
  pose proof (proj2 (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ run)) as Houtput.
  match type of Houtput with ?P after => match goal with |- ?Q after => assert (Hpost : P |-- Q) end end.
  { unfold flag_pend_caller_restore_input, flag_pend_active_restore_input; Intros.
    sep_apply_l_atomic Hrecover; entailer!. }
  exact (Hpost after Houtput).
Qed.

End FlagWaitingSelectedTake.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module CompletedSelectedFamily.
Import PrimitiveComponent CriticalComponent PendPhaseCandidate SelectedCProgram SelectedCSource TerminalCallValue.
Import FlagPendSchedulerResources SelectedOuterCompletion SelectedFamilyScope.
Import SelectedEnvironmentCProgram SelectedEnvironmentCSource SelectedEnvironmentScopedEnvironment.
Import SelectedEnvironmentPhaseEffects CompletedCallerEvents.

(** Each family below consumes the existing concrete last selector and
    return completion.  Its fixed saved receipt is reinterpreted by the
    same C sequence.  The extra physical frame remains private. *)

Section Taskfresh.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources).
Let configured := task_sw_hook_call_environment environment.
Context (task_abi : Armv7aTaskContextABI configured.(task_stack_call_external)
  configured.(task_stack_call_platform) configured.(task_stack_call_port)
  configured.(task_stack_call_continuations)).
Context (sg : StableGlobVars) (frame : Assertion) (original : OsSchedCallContext)
  (saved : Z) (acquired : UCOS2_Verify_State) (other : Armv7aContinuation -> Assertion)
  (initial : UCOS2_Verify_State) (first_heap : model)
  (initial_local : Armv7aContinuation -> Assertion) (initial_private : Assertion) (reference : OsSchedCallContext).
Let active := flag_pend_fresh_observation reference.
Let receipt := active original initial.
Let input := flag_pend_caller_save_input configured critical initial_local active sg
  (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial ** initial_private.
Context (prefix_stop : bool) (prefix_output : Assertion) (last_entry : UCOS2_Verify_State)
  (context : OsSchedCallContext) (saved_sp : Z) (outgoing : TaskStackFragments)
  (hooked : UCOS2_Verify_State) (incoming : TaskStackLease) (resumed : TaskStackFragments).
Context (Hswitch : os_sched_requests_switch last_entry = true)
  (Hsave : configured.(task_stack_call_external).(os_sched_arch_save_source) context saved_sp outgoing)
  (Hhook : kernel_client_step configured.(task_stack_call_external).(os_sched_hook_action)
    sg (os_sched_save_current_sp (os_sched_prefix_state last_entry)
      context.(os_sched_call_stack).(stackLeaseSlot) saved_sp) hooked)
  (Hdestination : os_sched_destination_binding configured.(task_stack_call_external)
    context outgoing hooked incoming resumed).
Let call := {| InstallComponent.task_install_fields_context := context;
               InstallComponent.task_install_fields_outgoing := outgoing;
               InstallComponent.task_install_fields_incoming := incoming;
               InstallComponent.task_install_fields_resumed := resumed;
               InstallComponent.task_install_fields_entry := hooked |}.
Let local := kernel_sched_saved_local_resource_at configured.(task_stack_call_platform)
  critical sg hooked.(TskState) original saved acquired receipt other.
Let rest := armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame.
Context (before installed : model) (sp : Z)
  (actual : sched_install_heap_fragment sg before installed (task_slot_addr sg incoming.(stackLeaseSlot)) sp).
Context (complete : InstallComponent.task_install_c_segment configured local sg rest call before installed sp actual).
Context (prefix : kernel_c_sequence (kernel_program_selected_c_step configured critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin))
  initial first_heap input prefix_stop hooked before prefix_output).
Context (bridge : prefix_output |-- InstallComponent.task_install_fields_entry_owner configured local sg call ** rest).
Context (Hsource : kernel_program_selected_c_sequence_source configured critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix)
  (Hidle : SelectedIdleComposition.kernel_program_selected_sequence_idle_source configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix)
  (Hrange : task_in_range sg initial.(TskState))
  (Horiginal : kernel_call_task_source original initial)
  (Hrunning : initial.(SchedState).(isRunning) = true)
  (Henabled : os_sched_selection_enabled initial = true)
  (Hincoming : incoming = original.(os_sched_call_stack))
  (Hcoverage : task_stack_live_coverage hooked.(TskState)
    (Some (task_stack_key context.(os_sched_call_stack)))).

Lemma selected_task_fresh_environment :
  exists selected, forall restored,
  armv7a_task_restore_transition task_abi context selected installed restored ->
  let current := InstallComponent.task_install_fields_current call in
  let returned := kernel_selected_call selected current in
  forall close_arch
    (close : Armv7aRestoreResourceABI configured.(task_stack_call_external)
      configured.(task_stack_call_platform) critical close_arch)
    cursor written middle final_cursor environment_heap,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition close cursor restored written middle ->
  armv7a_restore_suffix_transition close written middle final_cursor environment_heap ->
  kernel_call_task_source returned current /\
  exists (scoped : flag_pend_scoped_environment_run configured critical initial_local other active sg
    original (armv7a_irq_fiq_mask saved) initial first_heap initial_private
    (orb (orb prefix_stop false) false) returned current environment_heap frame),
  flag_pend_scoped_environment_source configured critical initial_local other active sg None
    original (armv7a_irq_fiq_mask saved) initial first_heap initial_private
    (orb (orb prefix_stop false) false) returned current environment_heap frame scoped.
Proof.
  destruct (task_selected_c_completion_outer_sequence environment critical task_abi sg None frame
    original saved acquired receipt other initial first_heap input prefix_stop prefix_output
    last_entry context saved_sp outgoing hooked incoming resumed Hswitch Hsave Hhook Hdestination
    before installed sp actual complete prefix bridge Hsource Hidle Hrange Horiginal Hrunning
    Henabled Hincoming Hcoverage) as [selected Hselected].
  exists selected; intros restored Hrestore current returned close_arch close cursor written middle final_cursor
    environment_heap Hr0 Hmask Hprefix Hsuffix.
  destruct (Hselected restored Hrestore) as [whole [Hwhole [Hreturned Hstop]]].
  split; [exact Hreturned|].
  eapply (SelectedFamilyScope.selected_fresh_return_environment configured critical initial_local other initial_private frame sg
    reference original saved acquired initial first_heap (orb prefix_stop false)
    returned current restored close_arch close cursor written middle final_cursor environment_heap whole);
    eassumption.
Qed.

Lemma selected_task_fresh_save_output :
  exists selected, forall restored,
  armv7a_task_restore_transition task_abi context selected installed restored ->
  let current := InstallComponent.task_install_fields_current call in
  let returned := kernel_selected_call selected current in
  forall close_arch
    (close : Armv7aRestoreResourceABI configured.(task_stack_call_external)
      configured.(task_stack_call_platform) critical close_arch)
    cursor written middle final_cursor environment_heap,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition close cursor restored written middle ->
  armv7a_restore_suffix_transition close written middle final_cursor environment_heap ->
  forall caller_before private_before save_arch
    (save : Armv7aSaveSuffixABI configured.(task_stack_call_external)
      configured.(task_stack_call_platform) critical save_arch)
    registers final_registers whole_after,
  flag_pend_caller_save_input configured critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial caller_before ->
  initial_private private_before -> join caller_before private_before first_heap ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current environment_heap
    final_registers current whole_after ->
  exists caller_after,
  flag_pend_selected_caller_save_output configured critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial
    caller_before final_registers.(kernel_save_r0) caller_after.
Proof.
  destruct selected_task_fresh_environment as [selected Hselected].
  exists selected; intros restored Hrestore current returned close_arch close cursor written middle final_cursor environment_heap
    Hr0 Hmask Hclose_prefix Hclose_suffix caller_before private_before save_arch save
    registers final_registers whole_after Hinput Hprivate Hjoin Hword Hvalid Hsaved_mask Hsuffix.
  destruct (Hselected restored Hrestore close_arch close cursor written middle final_cursor environment_heap
    Hr0 Hmask Hclose_prefix Hclose_suffix) as [Hreturned [run Hrun_source]].
  destruct (os_sched_continuation_c_save_execution_from_environment configured critical initial_local other active sg
    original (armv7a_irq_fiq_mask saved) initial caller_before initial_private frame private_before first_heap
    (orb (orb prefix_stop false) false) returned current environment_heap save_arch save registers final_registers whole_after
    run Hrun_source Hinput Hprivate Hjoin Hword Hvalid Hsaved_mask Hsuffix) as [caller_after Hactual].
  exists caller_after.
  eapply scoped_save_event_output, scoped_save_execution_complete_event; eassumption.
Qed.

Lemma selected_task_fresh_restore_output :
  exists selected, forall restored,
  armv7a_task_restore_transition task_abi context selected installed restored ->
  let current := InstallComponent.task_install_fields_current call in
  let returned := kernel_selected_call selected current in
  forall close_arch
    (close : Armv7aRestoreResourceABI configured.(task_stack_call_external)
      configured.(task_stack_call_platform) critical close_arch)
    cursor written middle final_cursor environment_heap,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition close cursor restored written middle ->
  armv7a_restore_suffix_transition close written middle final_cursor environment_heap ->
  forall caller_before private_before whole_before caller_acquired restore_arch
    (restore : Armv7aRestoreResourceABI configured.(task_stack_call_external)
      configured.(task_stack_call_platform) critical restore_arch)
    caller_cursor caller_written caller_final whole_after,
  caller_cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask caller_cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input configured critical initial_local active sg
    (FlagPendTaskCaller original) original saved caller_acquired initial caller_before ->
  initial_private private_before -> join caller_before private_before whole_before ->
  armv7a_restore_prefix_transition restore caller_cursor whole_before caller_written first_heap ->
  armv7a_restore_suffix_transition restore caller_written environment_heap caller_final whole_after ->
  exists caller_after,
  flag_pend_selected_caller_restore_output configured critical initial_local active sg
    (FlagPendTaskCaller original) original saved caller_acquired initial caller_before caller_after.
Proof.
  destruct selected_task_fresh_environment as [selected Hselected].
  exists selected; intros restored Hrestore current returned close_arch close cursor written middle final_cursor environment_heap
    Hr0 Hmask Hclose_prefix Hclose_suffix caller_before private_before whole_before caller_acquired restore_arch restore
    caller_cursor caller_written caller_final whole_after Hcaller_r0 Hcaller_mask Hinput Hprivate Hjoin Hprefix Hsuffix.
  destruct (Hselected restored Hrestore close_arch close cursor written middle final_cursor environment_heap
    Hr0 Hmask Hclose_prefix Hclose_suffix) as [Hreturned [run Hrun_source]].
  destruct (os_sched_continuation_c_restore_execution_from_environment configured critical initial_local other active sg
    original saved caller_acquired initial caller_before initial_private frame private_before whole_before
    (orb (orb prefix_stop false) false) returned current environment_heap restore_arch restore
    caller_cursor caller_written first_heap caller_final whole_after run Hcaller_r0 Hcaller_mask Hinput Hprivate Hjoin
    Hprefix Hrun_source Hsuffix) as [caller_after Hactual].
  exists caller_after.
  eapply scoped_restore_event_output, scoped_restore_execution_complete_event; eassumption.
Qed.
End Taskfresh.


Section Taskfirst.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources).
Let configured := task_sw_hook_call_environment environment.
Context (task_abi : Armv7aTaskContextABI configured.(task_stack_call_external)
  configured.(task_stack_call_platform) configured.(task_stack_call_port)
  configured.(task_stack_call_continuations)).
Context (sg : StableGlobVars) (frame : Assertion) (original : OsSchedCallContext)
  (saved : Z) (acquired : UCOS2_Verify_State) (other : Armv7aContinuation -> Assertion)
  (initial : UCOS2_Verify_State) (first_heap : model)
  (initial_local : Armv7aContinuation -> Assertion) (initial_private : Assertion) (mode : Z) (reference : OsSchedCallContext) (reference_state : UCOS2_Verify_State).
Let active := flag_pend_first_observation mode reference reference_state.
Let receipt := active original initial.
Let input := flag_pend_caller_save_input configured critical initial_local active sg
  (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial ** initial_private.
Context (prefix_stop : bool) (prefix_output : Assertion) (last_entry : UCOS2_Verify_State)
  (context : OsSchedCallContext) (saved_sp : Z) (outgoing : TaskStackFragments)
  (hooked : UCOS2_Verify_State) (incoming : TaskStackLease) (resumed : TaskStackFragments).
Context (Hswitch : os_sched_requests_switch last_entry = true)
  (Hsave : configured.(task_stack_call_external).(os_sched_arch_save_source) context saved_sp outgoing)
  (Hhook : kernel_client_step configured.(task_stack_call_external).(os_sched_hook_action)
    sg (os_sched_save_current_sp (os_sched_prefix_state last_entry)
      context.(os_sched_call_stack).(stackLeaseSlot) saved_sp) hooked)
  (Hdestination : os_sched_destination_binding configured.(task_stack_call_external)
    context outgoing hooked incoming resumed).
Let call := {| InstallComponent.task_install_fields_context := context;
               InstallComponent.task_install_fields_outgoing := outgoing;
               InstallComponent.task_install_fields_incoming := incoming;
               InstallComponent.task_install_fields_resumed := resumed;
               InstallComponent.task_install_fields_entry := hooked |}.
Let local := kernel_sched_saved_local_resource_at configured.(task_stack_call_platform)
  critical sg hooked.(TskState) original saved acquired receipt other.
Let rest := armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame.
Context (before installed : model) (sp : Z)
  (actual : sched_install_heap_fragment sg before installed (task_slot_addr sg incoming.(stackLeaseSlot)) sp).
Context (complete : InstallComponent.task_install_c_segment configured local sg rest call before installed sp actual).
Context (prefix : kernel_c_sequence (kernel_program_selected_c_step configured critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin))
  initial first_heap input prefix_stop hooked before prefix_output).
Context (bridge : prefix_output |-- InstallComponent.task_install_fields_entry_owner configured local sg call ** rest).
Context (Hsource : kernel_program_selected_c_sequence_source configured critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix)
  (Hidle : SelectedIdleComposition.kernel_program_selected_sequence_idle_source configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix)
  (Hrange : task_in_range sg initial.(TskState))
  (Horiginal : kernel_call_task_source original initial)
  (Hrunning : initial.(SchedState).(isRunning) = true)
  (Henabled : os_sched_selection_enabled initial = true)
  (Hincoming : incoming = original.(os_sched_call_stack))
  (Hcoverage : task_stack_live_coverage hooked.(TskState)
    (Some (task_stack_key context.(os_sched_call_stack)))).

Lemma selected_task_first_environment :
  exists selected, forall restored,
  armv7a_task_restore_transition task_abi context selected installed restored ->
  let current := InstallComponent.task_install_fields_current call in
  let returned := kernel_selected_call selected current in
  forall close_arch
    (close : Armv7aRestoreResourceABI configured.(task_stack_call_external)
      configured.(task_stack_call_platform) critical close_arch)
    cursor written middle final_cursor environment_heap,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition close cursor restored written middle ->
  armv7a_restore_suffix_transition close written middle final_cursor environment_heap ->
  kernel_call_task_source returned current /\
  exists (scoped : flag_pend_scoped_environment_run configured critical initial_local other active sg
    original (armv7a_irq_fiq_mask saved) initial first_heap initial_private
    (orb (orb prefix_stop false) false) returned current environment_heap frame),
  flag_pend_scoped_environment_source configured critical initial_local other active sg None
    original (armv7a_irq_fiq_mask saved) initial first_heap initial_private
    (orb (orb prefix_stop false) false) returned current environment_heap frame scoped.
Proof.
  destruct (task_selected_c_completion_outer_sequence environment critical task_abi sg None frame
    original saved acquired receipt other initial first_heap input prefix_stop prefix_output
    last_entry context saved_sp outgoing hooked incoming resumed Hswitch Hsave Hhook Hdestination
    before installed sp actual complete prefix bridge Hsource Hidle Hrange Horiginal Hrunning
    Henabled Hincoming Hcoverage) as [selected Hselected].
  exists selected; intros restored Hrestore current returned close_arch close cursor written middle final_cursor
    environment_heap Hr0 Hmask Hprefix Hsuffix.
  destruct (Hselected restored Hrestore) as [whole [Hwhole [Hreturned Hstop]]].
  split; [exact Hreturned|].
  eapply (SelectedFamilyScope.selected_first_return_environment configured critical initial_local other initial_private frame sg
    mode reference reference_state original saved acquired initial first_heap (orb prefix_stop false)
    returned current restored close_arch close cursor written middle final_cursor environment_heap whole);
    eassumption.
Qed.

Lemma selected_task_first_save_output :
  exists selected, forall restored,
  armv7a_task_restore_transition task_abi context selected installed restored ->
  let current := InstallComponent.task_install_fields_current call in
  let returned := kernel_selected_call selected current in
  forall close_arch
    (close : Armv7aRestoreResourceABI configured.(task_stack_call_external)
      configured.(task_stack_call_platform) critical close_arch)
    cursor written middle final_cursor environment_heap,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition close cursor restored written middle ->
  armv7a_restore_suffix_transition close written middle final_cursor environment_heap ->
  forall caller_before private_before save_arch
    (save : Armv7aSaveSuffixABI configured.(task_stack_call_external)
      configured.(task_stack_call_platform) critical save_arch)
    registers final_registers whole_after,
  flag_pend_caller_save_input configured critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial caller_before ->
  initial_private private_before -> join caller_before private_before first_heap ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current environment_heap
    final_registers current whole_after ->
  exists caller_after,
  flag_pend_selected_caller_save_output configured critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial
    caller_before final_registers.(kernel_save_r0) caller_after.
Proof.
  destruct selected_task_first_environment as [selected Hselected].
  exists selected; intros restored Hrestore current returned close_arch close cursor written middle final_cursor environment_heap
    Hr0 Hmask Hclose_prefix Hclose_suffix caller_before private_before save_arch save
    registers final_registers whole_after Hinput Hprivate Hjoin Hword Hvalid Hsaved_mask Hsuffix.
  destruct (Hselected restored Hrestore close_arch close cursor written middle final_cursor environment_heap
    Hr0 Hmask Hclose_prefix Hclose_suffix) as [Hreturned [run Hrun_source]].
  destruct (os_sched_continuation_c_save_execution_from_environment configured critical initial_local other active sg
    original (armv7a_irq_fiq_mask saved) initial caller_before initial_private frame private_before first_heap
    (orb (orb prefix_stop false) false) returned current environment_heap save_arch save registers final_registers whole_after
    run Hrun_source Hinput Hprivate Hjoin Hword Hvalid Hsaved_mask Hsuffix) as [caller_after Hactual].
  exists caller_after.
  eapply scoped_save_event_output, scoped_save_execution_complete_event; eassumption.
Qed.

Lemma selected_task_first_restore_output :
  exists selected, forall restored,
  armv7a_task_restore_transition task_abi context selected installed restored ->
  let current := InstallComponent.task_install_fields_current call in
  let returned := kernel_selected_call selected current in
  forall close_arch
    (close : Armv7aRestoreResourceABI configured.(task_stack_call_external)
      configured.(task_stack_call_platform) critical close_arch)
    cursor written middle final_cursor environment_heap,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition close cursor restored written middle ->
  armv7a_restore_suffix_transition close written middle final_cursor environment_heap ->
  forall caller_before private_before whole_before caller_acquired restore_arch
    (restore : Armv7aRestoreResourceABI configured.(task_stack_call_external)
      configured.(task_stack_call_platform) critical restore_arch)
    caller_cursor caller_written caller_final whole_after,
  caller_cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask caller_cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input configured critical initial_local active sg
    (FlagPendTaskCaller original) original saved caller_acquired initial caller_before ->
  initial_private private_before -> join caller_before private_before whole_before ->
  armv7a_restore_prefix_transition restore caller_cursor whole_before caller_written first_heap ->
  armv7a_restore_suffix_transition restore caller_written environment_heap caller_final whole_after ->
  exists caller_after,
  flag_pend_selected_caller_restore_output configured critical initial_local active sg
    (FlagPendTaskCaller original) original saved caller_acquired initial caller_before caller_after.
Proof.
  destruct selected_task_first_environment as [selected Hselected].
  exists selected; intros restored Hrestore current returned close_arch close cursor written middle final_cursor environment_heap
    Hr0 Hmask Hclose_prefix Hclose_suffix caller_before private_before whole_before caller_acquired restore_arch restore
    caller_cursor caller_written caller_final whole_after Hcaller_r0 Hcaller_mask Hinput Hprivate Hjoin Hprefix Hsuffix.
  destruct (Hselected restored Hrestore close_arch close cursor written middle final_cursor environment_heap
    Hr0 Hmask Hclose_prefix Hclose_suffix) as [Hreturned [run Hrun_source]].
  destruct (os_sched_continuation_c_restore_execution_from_environment configured critical initial_local other active sg
    original saved caller_acquired initial caller_before initial_private frame private_before whole_before
    (orb (orb prefix_stop false) false) returned current environment_heap restore_arch restore
    caller_cursor caller_written first_heap caller_final whole_after run Hcaller_r0 Hcaller_mask Hinput Hprivate Hjoin
    Hprefix Hrun_source Hsuffix) as [caller_after Hactual].
  exists caller_after.
  eapply scoped_restore_event_output, scoped_restore_execution_complete_event; eassumption.
Qed.
End Taskfirst.

Section IRQfresh.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources).
Let configured := task_sw_hook_call_environment environment.
Context (sg : StableGlobVars) (frame : Assertion) (original : OsSchedCallContext)
  (saved : Z) (acquired : UCOS2_Verify_State) (other : Armv7aContinuation -> Assertion)
  (initial : UCOS2_Verify_State) (first_heap : model)
  (initial_local : Armv7aContinuation -> Assertion) (initial_private : Assertion) (reference : OsSchedCallContext).
Let active := flag_pend_fresh_observation reference.
Let receipt := active original initial.
Let input := flag_pend_caller_save_input configured critical initial_local active sg
  (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial ** initial_private.
Context (handler : OsIntExitCallContext) (entry : UCOS2_Verify_State) (transfer : OsIntExitTransfer)
  (before prepared hooked_heap installed restored : model) (selected : Armv7aContinuation).
Context (source : os_int_exit_transfer_source configured.(task_stack_call_external)
    environment.(task_stack_call_port) sg handler entry transfer)
  (prefix_execution : IRQAcquiredCPrefix.os_int_exit_acquired_switch_prefix_execution sg entry before prepared)
  (hook : kernel_heap_execution [] prepared hooked_heap)
  (install : sched_install_heap_fragment sg hooked_heap installed
    (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp))
  (restore_execution : armv7a_restore_transition configured.(task_stack_call_continuations)
    handler selected installed restored).
Context (complete : IRQAcquiredReturn.kernel_irq_acquired_c_completion environment critical sg handler entry transfer
  original saved acquired receipt other frame before prepared hooked_heap installed selected restored
  source prefix_execution hook install restore_execution).
Context (prefix_stop : bool) (prefix_output : Assertion).
Context (prefix : kernel_c_sequence (kernel_program_selected_c_step configured critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin))
  initial first_heap input prefix_stop entry before prefix_output).
Context (bridge : prefix_output |-- IRQCPrefix.os_int_exit_prefix_fields_owner
  configured critical sg handler entry original saved acquired receipt other frame).
Context (Hsource : kernel_program_selected_c_sequence_source configured critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix)
  (Hidle : SelectedIdleComposition.kernel_program_selected_sequence_idle_source configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix)
  (Hrange : task_in_range sg initial.(TskState))
  (Horiginal : kernel_call_task_source original initial)
  (Hrunning : initial.(SchedState).(isRunning) = true)
  (Henabled : os_sched_selection_enabled initial = true).
Let returned := kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack) transfer.(os_int_exit_incoming_fragments).
Let current := os_int_exit_installed_state transfer.
Let private_output := task_stack_fragments_rep handler.(os_int_exit_handler_stack)
  handler.(os_int_exit_handler_fragments) ** frame.

Lemma selected_irq_fresh_environment :
  forall close_arch
    (close : Armv7aRestoreResourceABI configured.(task_stack_call_external)
      configured.(task_stack_call_platform) critical close_arch)
    cursor written middle final_cursor environment_heap,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition close cursor restored written middle ->
  armv7a_restore_suffix_transition close written middle final_cursor environment_heap ->
  kernel_call_task_source returned current /\
  exists (scoped : flag_pend_scoped_environment_run configured critical initial_local other active sg
    original (armv7a_irq_fiq_mask saved) initial first_heap initial_private
    (orb (orb prefix_stop false) false) returned current environment_heap private_output),
  flag_pend_scoped_environment_source configured critical initial_local other active sg None
    original (armv7a_irq_fiq_mask saved) initial first_heap initial_private
    (orb (orb prefix_stop false) false) returned current environment_heap private_output scoped.
Proof.
  intros close_arch close cursor written middle final_cursor environment_heap Hr0 Hmask Hprefix Hsuffix.
  destruct (irq_acquired_c_completion_outer_sequence environment critical sg None handler entry transfer
    original saved acquired receipt other frame before prepared hooked_heap installed selected restored
    source prefix_execution hook install restore_execution initial first_heap input prefix_stop prefix_output
    prefix bridge Hsource Hidle Hrange Horiginal Hrunning Henabled complete)
    as [whole [Hwhole [Hwhole_idle [Hreturned Hstop]]]].
  split; [exact Hreturned|].
  assert (Hreceipt : IRQSelectedCompletion.irq_selected_suffix_receipt handler receipt frame |--
    receipt ** private_output).
  { unfold IRQSelectedCompletion.irq_selected_suffix_receipt, private_output; entailer!. }
  assert (Howner : IRQSelectedCompletion.irq_selected_suffix_output configured critical sg handler transfer
    original saved acquired receipt other frame |--
    flag_pend_caller_restore_input configured critical other (fun _ _ => receipt ** private_output) sg
      (FlagPendTaskCaller returned) returned saved acquired current).
  { unfold IRQSelectedCompletion.irq_selected_suffix_output.
    eapply SelectedLocalRecovery.flag_pend_caller_restore_input_receipt_consequence; exact Hreceipt. }
  pose proof (proj1 (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ whole)) as Hinput.
  pose (adjusted := KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput (fun heap Howned => Howned)
    whole (fun heap Howned => conj (proj1 Howned) (Howner heap (proj2 Howned)))).
  assert (Hadjusted : kernel_program_selected_c_sequence_source configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ adjusted).
  { apply KernelCSourceAdapt; exact Hwhole. }
  eapply (SelectedFamilyScope.selected_fresh_return_environment configured critical initial_local other
    initial_private private_output sg reference original saved acquired initial first_heap (orb prefix_stop false)
    returned current restored close_arch close cursor written middle final_cursor environment_heap adjusted);
    eassumption.
Qed.

Lemma selected_irq_fresh_save_output :
  forall close_arch
    (close : Armv7aRestoreResourceABI configured.(task_stack_call_external)
      configured.(task_stack_call_platform) critical close_arch)
    cursor written middle final_cursor environment_heap,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition close cursor restored written middle ->
  armv7a_restore_suffix_transition close written middle final_cursor environment_heap ->
  forall caller_before private_before save_arch
    (save : Armv7aSaveSuffixABI configured.(task_stack_call_external)
      configured.(task_stack_call_platform) critical save_arch)
    registers final_registers whole_after,
  flag_pend_caller_save_input configured critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial caller_before ->
  initial_private private_before -> join caller_before private_before first_heap ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current environment_heap
    final_registers current whole_after ->
  exists caller_after,
  flag_pend_selected_caller_save_output configured critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial
    caller_before final_registers.(kernel_save_r0) caller_after.
Proof.
  intros close_arch close cursor written middle final_cursor environment_heap
    Hr0 Hmask Hclose_prefix Hclose_suffix caller_before private_before save_arch save
    registers final_registers whole_after Hinput Hprivate Hjoin Hword Hvalid Hsaved_mask Hsuffix.
  destruct (selected_irq_fresh_environment close_arch close cursor written middle final_cursor environment_heap
    Hr0 Hmask Hclose_prefix Hclose_suffix) as [Hreturned [run Hrun_source]].
  destruct (os_sched_continuation_c_save_execution_from_environment configured critical initial_local other active sg
    original (armv7a_irq_fiq_mask saved) initial caller_before initial_private private_output private_before first_heap
    (orb (orb prefix_stop false) false) returned current environment_heap save_arch save registers final_registers whole_after
    run Hrun_source Hinput Hprivate Hjoin Hword Hvalid Hsaved_mask Hsuffix) as [caller_after Hactual].
  exists caller_after.
  eapply scoped_save_event_output, scoped_save_execution_complete_event; eassumption.
Qed.

Lemma selected_irq_fresh_restore_output :
  forall close_arch
    (close : Armv7aRestoreResourceABI configured.(task_stack_call_external)
      configured.(task_stack_call_platform) critical close_arch)
    cursor written middle final_cursor environment_heap,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition close cursor restored written middle ->
  armv7a_restore_suffix_transition close written middle final_cursor environment_heap ->
  forall caller_before private_before whole_before caller_acquired restore_arch
    (restore : Armv7aRestoreResourceABI configured.(task_stack_call_external)
      configured.(task_stack_call_platform) critical restore_arch)
    caller_cursor caller_written caller_final whole_after,
  caller_cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask caller_cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input configured critical initial_local active sg
    (FlagPendTaskCaller original) original saved caller_acquired initial caller_before ->
  initial_private private_before -> join caller_before private_before whole_before ->
  armv7a_restore_prefix_transition restore caller_cursor whole_before caller_written first_heap ->
  armv7a_restore_suffix_transition restore caller_written environment_heap caller_final whole_after ->
  exists caller_after,
  flag_pend_selected_caller_restore_output configured critical initial_local active sg
    (FlagPendTaskCaller original) original saved caller_acquired initial caller_before caller_after.
Proof.
  intros close_arch close cursor written middle final_cursor environment_heap
    Hr0 Hmask Hclose_prefix Hclose_suffix caller_before private_before whole_before caller_acquired restore_arch restore
    caller_cursor caller_written caller_final whole_after Hcaller_r0 Hcaller_mask Hinput Hprivate Hjoin Hprefix Hsuffix.
  destruct (selected_irq_fresh_environment close_arch close cursor written middle final_cursor environment_heap
    Hr0 Hmask Hclose_prefix Hclose_suffix) as [Hreturned [run Hrun_source]].
  destruct (os_sched_continuation_c_restore_execution_from_environment configured critical initial_local other active sg
    original saved caller_acquired initial caller_before initial_private private_output private_before whole_before
    (orb (orb prefix_stop false) false) returned current environment_heap restore_arch restore
    caller_cursor caller_written first_heap caller_final whole_after run Hcaller_r0 Hcaller_mask Hinput Hprivate Hjoin
    Hprefix Hrun_source Hsuffix) as [caller_after Hactual].
  exists caller_after.
  eapply scoped_restore_event_output, scoped_restore_execution_complete_event; eassumption.
Qed.
End IRQfresh.


Section IRQfirst.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources).
Let configured := task_sw_hook_call_environment environment.
Context (sg : StableGlobVars) (frame : Assertion) (original : OsSchedCallContext)
  (saved : Z) (acquired : UCOS2_Verify_State) (other : Armv7aContinuation -> Assertion)
  (initial : UCOS2_Verify_State) (first_heap : model)
  (initial_local : Armv7aContinuation -> Assertion) (initial_private : Assertion) (mode : Z) (reference : OsSchedCallContext) (reference_state : UCOS2_Verify_State).
Let active := flag_pend_first_observation mode reference reference_state.
Let receipt := active original initial.
Let input := flag_pend_caller_save_input configured critical initial_local active sg
  (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial ** initial_private.
Context (handler : OsIntExitCallContext) (entry : UCOS2_Verify_State) (transfer : OsIntExitTransfer)
  (before prepared hooked_heap installed restored : model) (selected : Armv7aContinuation).
Context (source : os_int_exit_transfer_source configured.(task_stack_call_external)
    environment.(task_stack_call_port) sg handler entry transfer)
  (prefix_execution : IRQAcquiredCPrefix.os_int_exit_acquired_switch_prefix_execution sg entry before prepared)
  (hook : kernel_heap_execution [] prepared hooked_heap)
  (install : sched_install_heap_fragment sg hooked_heap installed
    (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp))
  (restore_execution : armv7a_restore_transition configured.(task_stack_call_continuations)
    handler selected installed restored).
Context (complete : IRQAcquiredReturn.kernel_irq_acquired_c_completion environment critical sg handler entry transfer
  original saved acquired receipt other frame before prepared hooked_heap installed selected restored
  source prefix_execution hook install restore_execution).
Context (prefix_stop : bool) (prefix_output : Assertion).
Context (prefix : kernel_c_sequence (kernel_program_selected_c_step configured critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin))
  initial first_heap input prefix_stop entry before prefix_output).
Context (bridge : prefix_output |-- IRQCPrefix.os_int_exit_prefix_fields_owner
  configured critical sg handler entry original saved acquired receipt other frame).
Context (Hsource : kernel_program_selected_c_sequence_source configured critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix)
  (Hidle : SelectedIdleComposition.kernel_program_selected_sequence_idle_source configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix)
  (Hrange : task_in_range sg initial.(TskState))
  (Horiginal : kernel_call_task_source original initial)
  (Hrunning : initial.(SchedState).(isRunning) = true)
  (Henabled : os_sched_selection_enabled initial = true).
Let returned := kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack) transfer.(os_int_exit_incoming_fragments).
Let current := os_int_exit_installed_state transfer.
Let private_output := task_stack_fragments_rep handler.(os_int_exit_handler_stack)
  handler.(os_int_exit_handler_fragments) ** frame.

Lemma selected_irq_first_environment :
  forall close_arch
    (close : Armv7aRestoreResourceABI configured.(task_stack_call_external)
      configured.(task_stack_call_platform) critical close_arch)
    cursor written middle final_cursor environment_heap,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition close cursor restored written middle ->
  armv7a_restore_suffix_transition close written middle final_cursor environment_heap ->
  kernel_call_task_source returned current /\
  exists (scoped : flag_pend_scoped_environment_run configured critical initial_local other active sg
    original (armv7a_irq_fiq_mask saved) initial first_heap initial_private
    (orb (orb prefix_stop false) false) returned current environment_heap private_output),
  flag_pend_scoped_environment_source configured critical initial_local other active sg None
    original (armv7a_irq_fiq_mask saved) initial first_heap initial_private
    (orb (orb prefix_stop false) false) returned current environment_heap private_output scoped.
Proof.
  intros close_arch close cursor written middle final_cursor environment_heap Hr0 Hmask Hprefix Hsuffix.
  destruct (irq_acquired_c_completion_outer_sequence environment critical sg None handler entry transfer
    original saved acquired receipt other frame before prepared hooked_heap installed selected restored
    source prefix_execution hook install restore_execution initial first_heap input prefix_stop prefix_output
    prefix bridge Hsource Hidle Hrange Horiginal Hrunning Henabled complete)
    as [whole [Hwhole [Hwhole_idle [Hreturned Hstop]]]].
  split; [exact Hreturned|].
  assert (Hreceipt : IRQSelectedCompletion.irq_selected_suffix_receipt handler receipt frame |--
    receipt ** private_output).
  { unfold IRQSelectedCompletion.irq_selected_suffix_receipt, private_output; entailer!. }
  assert (Howner : IRQSelectedCompletion.irq_selected_suffix_output configured critical sg handler transfer
    original saved acquired receipt other frame |--
    flag_pend_caller_restore_input configured critical other (fun _ _ => receipt ** private_output) sg
      (FlagPendTaskCaller returned) returned saved acquired current).
  { unfold IRQSelectedCompletion.irq_selected_suffix_output.
    eapply SelectedLocalRecovery.flag_pend_caller_restore_input_receipt_consequence; exact Hreceipt. }
  pose proof (proj1 (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ whole)) as Hinput.
  pose (adjusted := KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput (fun heap Howned => Howned)
    whole (fun heap Howned => conj (proj1 Howned) (Howner heap (proj2 Howned)))).
  assert (Hadjusted : kernel_program_selected_c_sequence_source configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ adjusted).
  { apply KernelCSourceAdapt; exact Hwhole. }
  eapply (SelectedFamilyScope.selected_first_return_environment configured critical initial_local other
    initial_private private_output sg mode reference reference_state original saved acquired initial first_heap (orb prefix_stop false)
    returned current restored close_arch close cursor written middle final_cursor environment_heap adjusted);
    eassumption.
Qed.

Lemma selected_irq_first_save_output :
  forall close_arch
    (close : Armv7aRestoreResourceABI configured.(task_stack_call_external)
      configured.(task_stack_call_platform) critical close_arch)
    cursor written middle final_cursor environment_heap,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition close cursor restored written middle ->
  armv7a_restore_suffix_transition close written middle final_cursor environment_heap ->
  forall caller_before private_before save_arch
    (save : Armv7aSaveSuffixABI configured.(task_stack_call_external)
      configured.(task_stack_call_platform) critical save_arch)
    registers final_registers whole_after,
  flag_pend_caller_save_input configured critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial caller_before ->
  initial_private private_before -> join caller_before private_before first_heap ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current environment_heap
    final_registers current whole_after ->
  exists caller_after,
  flag_pend_selected_caller_save_output configured critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial
    caller_before final_registers.(kernel_save_r0) caller_after.
Proof.
  intros close_arch close cursor written middle final_cursor environment_heap
    Hr0 Hmask Hclose_prefix Hclose_suffix caller_before private_before save_arch save
    registers final_registers whole_after Hinput Hprivate Hjoin Hword Hvalid Hsaved_mask Hsuffix.
  destruct (selected_irq_first_environment close_arch close cursor written middle final_cursor environment_heap
    Hr0 Hmask Hclose_prefix Hclose_suffix) as [Hreturned [run Hrun_source]].
  destruct (os_sched_continuation_c_save_execution_from_environment configured critical initial_local other active sg
    original (armv7a_irq_fiq_mask saved) initial caller_before initial_private private_output private_before first_heap
    (orb (orb prefix_stop false) false) returned current environment_heap save_arch save registers final_registers whole_after
    run Hrun_source Hinput Hprivate Hjoin Hword Hvalid Hsaved_mask Hsuffix) as [caller_after Hactual].
  exists caller_after.
  eapply scoped_save_event_output, scoped_save_execution_complete_event; eassumption.
Qed.

Lemma selected_irq_first_restore_output :
  forall close_arch
    (close : Armv7aRestoreResourceABI configured.(task_stack_call_external)
      configured.(task_stack_call_platform) critical close_arch)
    cursor written middle final_cursor environment_heap,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition close cursor restored written middle ->
  armv7a_restore_suffix_transition close written middle final_cursor environment_heap ->
  forall caller_before private_before whole_before caller_acquired restore_arch
    (restore : Armv7aRestoreResourceABI configured.(task_stack_call_external)
      configured.(task_stack_call_platform) critical restore_arch)
    caller_cursor caller_written caller_final whole_after,
  caller_cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask caller_cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input configured critical initial_local active sg
    (FlagPendTaskCaller original) original saved caller_acquired initial caller_before ->
  initial_private private_before -> join caller_before private_before whole_before ->
  armv7a_restore_prefix_transition restore caller_cursor whole_before caller_written first_heap ->
  armv7a_restore_suffix_transition restore caller_written environment_heap caller_final whole_after ->
  exists caller_after,
  flag_pend_selected_caller_restore_output configured critical initial_local active sg
    (FlagPendTaskCaller original) original saved caller_acquired initial caller_before caller_after.
Proof.
  intros close_arch close cursor written middle final_cursor environment_heap
    Hr0 Hmask Hclose_prefix Hclose_suffix caller_before private_before whole_before caller_acquired restore_arch restore
    caller_cursor caller_written caller_final whole_after Hcaller_r0 Hcaller_mask Hinput Hprivate Hjoin Hprefix Hsuffix.
  destruct (selected_irq_first_environment close_arch close cursor written middle final_cursor environment_heap
    Hr0 Hmask Hclose_prefix Hclose_suffix) as [Hreturned [run Hrun_source]].
  destruct (os_sched_continuation_c_restore_execution_from_environment configured critical initial_local other active sg
    original saved caller_acquired initial caller_before initial_private private_output private_before whole_before
    (orb (orb prefix_stop false) false) returned current environment_heap restore_arch restore
    caller_cursor caller_written first_heap caller_final whole_after run Hcaller_r0 Hcaller_mask Hinput Hprivate Hjoin
    Hprefix Hrun_source Hsuffix) as [caller_after Hactual].
  exists caller_after.
  eapply scoped_restore_event_output, scoped_restore_execution_complete_event; eassumption.
Qed.
End IRQfirst.

End CompletedSelectedFamily.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module CompletedReturnedIRQFamily.
Import PrimitiveComponent PendPhaseCandidate SelectedReturnedCProgram SelectedReturnedCSource
  SelectedIRQWrapperCompletion OSIntExitReturnedC OSIntExitCCallControl OSIntExitCCallEnvelope
  OSIntExitCCallCompletion ReturnedIdleSource
  SelectedEnvironmentCProgram SelectedEnvironmentCSource
  SelectedEnvironmentScopedSource SelectedEnvironmentScopedPrimitives SelectedEnvironmentScopedEnvironment
  SelectedEnvironmentPhaseEffects CompletedCallerEvents ReturnedIRQFamilyEnvironment.

Section FreshEvents.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (original : OsSchedCallContext).
Context (reference : OsSchedCallContext).
Context (initial : UCOS2_Verify_State) (entry_node : TaskAbstractState)
  (handler : OsIntExitCallContext) (suspended : Armv7aContinuation) (publication : nat).
Context (input_local : Armv7aContinuation -> Assertion) (private_input : Assertion).
Let active := flag_pend_fresh_observation reference.
Let receipt := active original initial.
Let entry_local := kernel_irq_fields_local input_local suspended receipt.
Let entry_frame := unmap_table_rep sg ** private_input.
Context (before saved_heap body_heap : model).
Let parked := armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
  suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments).
Context (body_input : Assertion) (prefix_stop : bool) (observed : UCOS2_Verify_State)
  (read_heap : model) (prefix_output read_input : Assertion) (acquire_stop : bool)
  (entry : UCOS2_Verify_State) (acquired_heap : model) (acquire_output : Assertion).
Context (prefix : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  parked body_heap body_input prefix_stop observed read_heap prefix_output).
Context (acquire : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  observed read_heap read_input acquire_stop entry acquired_heap acquire_output).
Context (observation_frame : Assertion) (local : Armv7aContinuation -> Assertion)
  (node : TaskAbstractState) (private_output : Assertion) (middle after : model).
Context (returned : os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
  entry local suspended receipt original node handler private_output acquired_heap middle after).
Context (call : os_int_exit_first_level_c_call environment critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin)
  initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
  body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
  prefix acquire local receipt private_output).
Let final := os_int_exit_wrapper_restored_state
  (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry) suspended.(armv7a_continuation_stack).
Let resumed := armv7a_continuation_resumed_call suspended original.
Let private_before_owner := task_stack_fragments_rep handler.(os_int_exit_handler_stack)
  handler.(os_int_exit_handler_fragments) ** private_input.
Let private_after_owner := task_stack_fragments_rep handler.(os_int_exit_handler_stack)
  handler.(os_int_exit_handler_fragments) ** private_output.


Lemma os_int_exit_fresh_call_save_output : forall caller_before private_before arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers final_registers whole_after,
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ acquire ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ acquire ->
  os_sched_selection_enabled initial = true ->
  flag_pend_caller_save_input environment critical input_local active sg (FlagPendTaskCaller original)
    original handler.(os_int_exit_interrupted_mask) initial caller_before ->
  private_before_owner private_before -> join caller_before private_before before ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = handler.(os_int_exit_interrupted_mask) ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) final after
    final_registers final whole_after ->
  exists caller_after,
    flag_pend_selected_caller_save_output environment critical input_local active sg
      (FlagPendTaskCaller original) original handler.(os_int_exit_interrupted_mask) initial
      caller_before final_registers.(kernel_save_r0) caller_after.
Proof.
  intros caller_before private_before arch save registers final_registers whole_after
    Hprefix_source Hacquire_source Hprefix_idle Hacquire_idle Henabled
    Hinput Hprivate Hjoin Hreturn Hvalid Hmask Hsuffix.
  assert (Hwhole : (flag_pend_caller_save_input environment critical input_local active sg
    (FlagPendTaskCaller original) original handler.(os_int_exit_interrupted_mask) initial **
    private_before_owner) before).
  { exists caller_before, private_before; exact (conj Hjoin (conj Hinput Hprivate)). }
  destruct (os_int_exit_fresh_call_environment environment critical sg original reference
    initial entry_node handler suspended publication input_local private_input before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local node private_output middle after returned call None
    Hprefix_source Hacquire_source Hprefix_idle Hacquire_idle Henabled Hwhole) as [Hreturned [run Hsource]].
  destruct (os_sched_continuation_c_save_execution_from_environment environment critical input_local local active sg
    original handler.(os_int_exit_interrupted_mask) initial caller_before private_before_owner private_after_owner
    private_before before (orb prefix_stop (orb acquire_stop false)) resumed final after
    arch save registers final_registers whole_after run Hsource Hinput Hprivate Hjoin
    Hreturn Hvalid Hmask Hsuffix) as [caller_after Hactual].
  exists caller_after.
  eapply scoped_save_event_output, scoped_save_execution_complete_event; eassumption.
Qed.

Lemma os_int_exit_fresh_call_restore_output : forall saved acquired caller_before private_before whole_before arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written final_cursor whole_after,
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ acquire ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ acquire ->
  os_sched_selection_enabled initial = true ->
  armv7a_irq_fiq_mask saved = handler.(os_int_exit_interrupted_mask) ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical input_local active sg
    (FlagPendTaskCaller original) original saved acquired initial caller_before ->
  private_before_owner private_before -> join caller_before private_before whole_before ->
  armv7a_restore_prefix_transition restore cursor whole_before written before ->
  armv7a_restore_suffix_transition restore written after final_cursor whole_after ->
  exists caller_after,
    flag_pend_selected_caller_restore_output environment critical input_local active sg
      (FlagPendTaskCaller original) original saved acquired initial caller_before caller_after.
Proof.
  intros saved acquired caller_before private_before whole_before arch restore cursor written final_cursor whole_after
    Hprefix_source Hacquire_source Hprefix_idle Hacquire_idle Henabled
    Hrestored_mask Hr0 Hcursor_mask Hinput Hprivate Hjoin Hprimitive_prefix Hsuffix.
  assert (Hwhole_restore : (flag_pend_caller_restore_input environment critical input_local active sg
    (FlagPendTaskCaller original) original saved acquired initial ** private_before_owner) whole_before).
  { exists caller_before, private_before; exact (conj Hjoin (conj Hinput Hprivate)). }
  destruct (flag_pend_scoped_restore_prefix_sequence environment critical input_local active sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None
    original saved acquired initial private_before_owner arch restore cursor whole_before written before
    Hr0 Hcursor_mask Hwhole_restore Hprimitive_prefix) as [primitive_run Hprimitive_source].
  pose proof (proj2 (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ primitive_run)) as Hwhole.
  rewrite Hrestored_mask in Hwhole.
  destruct (os_int_exit_fresh_call_environment environment critical sg original reference
    initial entry_node handler suspended publication input_local private_input before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local node private_output middle after returned call None
    Hprefix_source Hacquire_source Hprefix_idle Hacquire_idle Henabled Hwhole) as [Hreturned [run Hsource]].
  assert (Hsaved_environment : exists (saved_run : flag_pend_scoped_environment_run environment critical input_local local active sg
    original (armv7a_irq_fiq_mask saved) initial before private_before_owner
    (orb prefix_stop (orb acquire_stop false)) resumed final after private_after_owner),
    flag_pend_scoped_environment_source environment critical input_local local active sg None
      original (armv7a_irq_fiq_mask saved) initial before private_before_owner
      (orb prefix_stop (orb acquire_stop false)) resumed final after private_after_owner saved_run).
  { rewrite Hrestored_mask; exists run; exact Hsource. }
  destruct Hsaved_environment as [saved_run Hsaved_source].
  destruct (os_sched_continuation_c_restore_execution_from_environment environment critical input_local local active sg
    original saved acquired initial caller_before private_before_owner private_after_owner private_before whole_before
    (orb prefix_stop (orb acquire_stop false)) resumed final after arch restore cursor written before final_cursor whole_after
    saved_run Hr0 Hcursor_mask Hinput Hprivate Hjoin Hprimitive_prefix Hsaved_source Hsuffix) as [caller_after Hactual].
  exists caller_after.
  eapply scoped_restore_event_output, scoped_restore_execution_complete_event; eassumption.
Qed.

End FreshEvents.
Section FirstEvents.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (original : OsSchedCallContext).
Context (mode : Z) (reference : OsSchedCallContext) (reference_state : UCOS2_Verify_State).
Context (initial : UCOS2_Verify_State) (entry_node : TaskAbstractState)
  (handler : OsIntExitCallContext) (suspended : Armv7aContinuation) (publication : nat).
Context (input_local : Armv7aContinuation -> Assertion) (private_input : Assertion).
Let active := flag_pend_first_observation mode reference reference_state.
Let receipt := active original initial.
Let entry_local := kernel_irq_fields_local input_local suspended receipt.
Let entry_frame := unmap_table_rep sg ** private_input.
Context (before saved_heap body_heap : model).
Let parked := armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
  suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments).
Context (body_input : Assertion) (prefix_stop : bool) (observed : UCOS2_Verify_State)
  (read_heap : model) (prefix_output read_input : Assertion) (acquire_stop : bool)
  (entry : UCOS2_Verify_State) (acquired_heap : model) (acquire_output : Assertion).
Context (prefix : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  parked body_heap body_input prefix_stop observed read_heap prefix_output).
Context (acquire : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  observed read_heap read_input acquire_stop entry acquired_heap acquire_output).
Context (observation_frame : Assertion) (local : Armv7aContinuation -> Assertion)
  (node : TaskAbstractState) (private_output : Assertion) (middle after : model).
Context (returned : os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
  entry local suspended receipt original node handler private_output acquired_heap middle after).
Context (call : os_int_exit_first_level_c_call environment critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin)
  initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
  body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
  prefix acquire local receipt private_output).
Let final := os_int_exit_wrapper_restored_state
  (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry) suspended.(armv7a_continuation_stack).
Let resumed := armv7a_continuation_resumed_call suspended original.
Let private_before_owner := task_stack_fragments_rep handler.(os_int_exit_handler_stack)
  handler.(os_int_exit_handler_fragments) ** private_input.
Let private_after_owner := task_stack_fragments_rep handler.(os_int_exit_handler_stack)
  handler.(os_int_exit_handler_fragments) ** private_output.


Lemma os_int_exit_first_call_save_output : forall caller_before private_before arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers final_registers whole_after,
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ acquire ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ acquire ->
  os_sched_selection_enabled initial = true ->
  (flag_pend_valid_mode mode \/ flag_pend_task_entry reference reference_state) ->
  flag_pend_caller_save_input environment critical input_local active sg (FlagPendTaskCaller original)
    original handler.(os_int_exit_interrupted_mask) initial caller_before ->
  private_before_owner private_before -> join caller_before private_before before ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = handler.(os_int_exit_interrupted_mask) ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) final after
    final_registers final whole_after ->
  exists caller_after,
    flag_pend_selected_caller_save_output environment critical input_local active sg
      (FlagPendTaskCaller original) original handler.(os_int_exit_interrupted_mask) initial
      caller_before final_registers.(kernel_save_r0) caller_after.
Proof.
  intros caller_before private_before arch save registers final_registers whole_after
    Hprefix_source Hacquire_source Hprefix_idle Hacquire_idle Henabled Hguard
    Hinput Hprivate Hjoin Hreturn Hvalid Hmask Hsuffix.
  assert (Hwhole : (flag_pend_caller_save_input environment critical input_local active sg
    (FlagPendTaskCaller original) original handler.(os_int_exit_interrupted_mask) initial **
    private_before_owner) before).
  { exists caller_before, private_before; exact (conj Hjoin (conj Hinput Hprivate)). }
  destruct (os_int_exit_first_call_environment environment critical sg original mode reference reference_state
    initial entry_node handler suspended publication input_local private_input before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local node private_output middle after returned call None
    Hprefix_source Hacquire_source Hprefix_idle Hacquire_idle Henabled Hguard Hwhole) as [Hreturned [run Hsource]].
  destruct (os_sched_continuation_c_save_execution_from_environment environment critical input_local local active sg
    original handler.(os_int_exit_interrupted_mask) initial caller_before private_before_owner private_after_owner
    private_before before (orb prefix_stop (orb acquire_stop false)) resumed final after
    arch save registers final_registers whole_after run Hsource Hinput Hprivate Hjoin
    Hreturn Hvalid Hmask Hsuffix) as [caller_after Hactual].
  exists caller_after.
  eapply scoped_save_event_output, scoped_save_execution_complete_event; eassumption.
Qed.

Lemma os_int_exit_first_call_restore_output : forall saved acquired caller_before private_before whole_before arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written final_cursor whole_after,
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ acquire ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ acquire ->
  os_sched_selection_enabled initial = true ->
  (flag_pend_valid_mode mode \/ flag_pend_task_entry reference reference_state) ->
  armv7a_irq_fiq_mask saved = handler.(os_int_exit_interrupted_mask) ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical input_local active sg
    (FlagPendTaskCaller original) original saved acquired initial caller_before ->
  private_before_owner private_before -> join caller_before private_before whole_before ->
  armv7a_restore_prefix_transition restore cursor whole_before written before ->
  armv7a_restore_suffix_transition restore written after final_cursor whole_after ->
  exists caller_after,
    flag_pend_selected_caller_restore_output environment critical input_local active sg
      (FlagPendTaskCaller original) original saved acquired initial caller_before caller_after.
Proof.
  intros saved acquired caller_before private_before whole_before arch restore cursor written final_cursor whole_after
    Hprefix_source Hacquire_source Hprefix_idle Hacquire_idle Henabled Hguard
    Hrestored_mask Hr0 Hcursor_mask Hinput Hprivate Hjoin Hprimitive_prefix Hsuffix.
  assert (Hwhole_restore : (flag_pend_caller_restore_input environment critical input_local active sg
    (FlagPendTaskCaller original) original saved acquired initial ** private_before_owner) whole_before).
  { exists caller_before, private_before; exact (conj Hjoin (conj Hinput Hprivate)). }
  destruct (flag_pend_scoped_restore_prefix_sequence environment critical input_local active sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None
    original saved acquired initial private_before_owner arch restore cursor whole_before written before
    Hr0 Hcursor_mask Hwhole_restore Hprimitive_prefix) as [primitive_run Hprimitive_source].
  pose proof (proj2 (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ primitive_run)) as Hwhole.
  rewrite Hrestored_mask in Hwhole.
  destruct (os_int_exit_first_call_environment environment critical sg original mode reference reference_state
    initial entry_node handler suspended publication input_local private_input before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local node private_output middle after returned call None
    Hprefix_source Hacquire_source Hprefix_idle Hacquire_idle Henabled Hguard Hwhole) as [Hreturned [run Hsource]].
  assert (Hsaved_environment : exists (saved_run : flag_pend_scoped_environment_run environment critical input_local local active sg
    original (armv7a_irq_fiq_mask saved) initial before private_before_owner
    (orb prefix_stop (orb acquire_stop false)) resumed final after private_after_owner),
    flag_pend_scoped_environment_source environment critical input_local local active sg None
      original (armv7a_irq_fiq_mask saved) initial before private_before_owner
      (orb prefix_stop (orb acquire_stop false)) resumed final after private_after_owner saved_run).
  { rewrite Hrestored_mask; exists run; exact Hsource. }
  destruct Hsaved_environment as [saved_run Hsaved_source].
  destruct (os_sched_continuation_c_restore_execution_from_environment environment critical input_local local active sg
    original saved acquired initial caller_before private_before_owner private_after_owner private_before whole_before
    (orb prefix_stop (orb acquire_stop false)) resumed final after arch restore cursor written before final_cursor whole_after
    saved_run Hr0 Hcursor_mask Hinput Hprivate Hjoin Hprimitive_prefix Hsaved_source Hsuffix) as [caller_after Hactual].
  exists caller_after.
  eapply scoped_restore_event_output, scoped_restore_execution_complete_event; eassumption.
Qed.

End FirstEvents.
Section WaitingEvents.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (original : OsSchedCallContext).
Context (reference : OsSchedCallContext) (pointer : addr).
Context (initial : UCOS2_Verify_State) (entry_node : TaskAbstractState)
  (handler : OsIntExitCallContext) (suspended : Armv7aContinuation) (publication : nat).
Context (input_local : Armv7aContinuation -> Assertion) (private_input : Assertion).
Let active := flag_pend_wait_active sg reference pointer.
Let receipt := flag_pend_waiting_receipt sg reference pointer original initial.
Let entry_local := kernel_irq_fields_local input_local suspended receipt.
Let entry_frame := unmap_table_rep sg ** private_input.
Context (before saved_heap body_heap : model).
Let parked := armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
  suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments).
Context (body_input : Assertion) (prefix_stop : bool) (observed : UCOS2_Verify_State)
  (read_heap : model) (prefix_output read_input : Assertion) (acquire_stop : bool)
  (entry : UCOS2_Verify_State) (acquired_heap : model) (acquire_output : Assertion).
Context (prefix : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  parked body_heap body_input prefix_stop observed read_heap prefix_output).
Context (acquire : kernel_c_sequence
  (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
  observed read_heap read_input acquire_stop entry acquired_heap acquire_output).
Context (observation_frame : Assertion) (local : Armv7aContinuation -> Assertion)
  (node : TaskAbstractState) (private_output : Assertion) (middle after : model).
Context (returned : os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
  entry local suspended receipt original node handler private_output acquired_heap middle after).
Context (call : os_int_exit_first_level_c_call environment critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin)
  initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
  body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
  prefix acquire local receipt private_output).
Let final := os_int_exit_wrapper_restored_state
  (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry) suspended.(armv7a_continuation_stack).
Let resumed := armv7a_continuation_resumed_call suspended original.
Let private_before_owner := task_stack_fragments_rep handler.(os_int_exit_handler_stack)
  handler.(os_int_exit_handler_fragments) ** private_input.
Let private_after_owner := task_stack_fragments_rep handler.(os_int_exit_handler_stack)
  handler.(os_int_exit_handler_fragments) ** private_output.


Lemma os_int_exit_waiting_call_save_output : forall caller_before private_before arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers final_registers whole_after,
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ acquire ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ acquire ->
  os_sched_selection_enabled initial = true ->
  ((exists waiter, entry.(FlagState).(flagWaitNodes) pointer = Some waiter) \/
    initial.(FlagState).(flagWaitNodes) pointer = None) ->
  flag_pend_caller_save_input environment critical input_local active sg (FlagPendTaskCaller original)
    original handler.(os_int_exit_interrupted_mask) initial caller_before ->
  private_before_owner private_before -> join caller_before private_before before ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = handler.(os_int_exit_interrupted_mask) ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) final after
    final_registers final whole_after ->
  exists caller_after,
    flag_pend_selected_caller_save_output environment critical input_local active sg
      (FlagPendTaskCaller original) original handler.(os_int_exit_interrupted_mask) initial
      caller_before final_registers.(kernel_save_r0) caller_after.
Proof.
  intros caller_before private_before arch save registers final_registers whole_after
    Hprefix_source Hacquire_source Hprefix_idle Hacquire_idle Henabled Hcase
    Hinput Hprivate Hjoin Hreturn Hvalid Hmask Hsuffix.
  assert (Hwhole : (flag_pend_caller_save_input environment critical input_local active sg
    (FlagPendTaskCaller original) original handler.(os_int_exit_interrupted_mask) initial **
    private_before_owner) before).
  { exists caller_before, private_before; exact (conj Hjoin (conj Hinput Hprivate)). }
  destruct (os_int_exit_waiting_call_environment environment critical sg original reference pointer
    initial entry_node handler suspended publication input_local private_input before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local node private_output middle after returned call None
    Hprefix_source Hacquire_source Hprefix_idle Hacquire_idle Henabled Hcase Hwhole) as [Hreturned [run Hsource]].
  destruct (os_sched_continuation_c_save_execution_from_environment environment critical input_local local active sg
    original handler.(os_int_exit_interrupted_mask) initial caller_before private_before_owner private_after_owner
    private_before before (orb prefix_stop (orb acquire_stop false)) resumed final after
    arch save registers final_registers whole_after run Hsource Hinput Hprivate Hjoin
    Hreturn Hvalid Hmask Hsuffix) as [caller_after Hactual].
  exists caller_after.
  eapply scoped_save_event_output, scoped_save_execution_complete_event; eassumption.
Qed.

Lemma os_int_exit_waiting_call_restore_output : forall saved acquired caller_before private_before whole_before arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written final_cursor whole_after,
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ acquire ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_sequence_idle_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ acquire ->
  os_sched_selection_enabled initial = true ->
  ((exists waiter, entry.(FlagState).(flagWaitNodes) pointer = Some waiter) \/
    initial.(FlagState).(flagWaitNodes) pointer = None) ->
  armv7a_irq_fiq_mask saved = handler.(os_int_exit_interrupted_mask) ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical input_local active sg
    (FlagPendTaskCaller original) original saved acquired initial caller_before ->
  private_before_owner private_before -> join caller_before private_before whole_before ->
  armv7a_restore_prefix_transition restore cursor whole_before written before ->
  armv7a_restore_suffix_transition restore written after final_cursor whole_after ->
  exists caller_after,
    flag_pend_selected_caller_restore_output environment critical input_local active sg
      (FlagPendTaskCaller original) original saved acquired initial caller_before caller_after.
Proof.
  intros saved acquired caller_before private_before whole_before arch restore cursor written final_cursor whole_after
    Hprefix_source Hacquire_source Hprefix_idle Hacquire_idle Henabled Hcase
    Hrestored_mask Hr0 Hcursor_mask Hinput Hprivate Hjoin Hprimitive_prefix Hsuffix.
  assert (Hwhole_restore : (flag_pend_caller_restore_input environment critical input_local active sg
    (FlagPendTaskCaller original) original saved acquired initial ** private_before_owner) whole_before).
  { exists caller_before, private_before; exact (conj Hjoin (conj Hinput Hprivate)). }
  destruct (flag_pend_scoped_restore_prefix_sequence environment critical input_local active sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None
    original saved acquired initial private_before_owner arch restore cursor whole_before written before
    Hr0 Hcursor_mask Hwhole_restore Hprimitive_prefix) as [primitive_run Hprimitive_source].
  pose proof (proj2 (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ primitive_run)) as Hwhole.
  rewrite Hrestored_mask in Hwhole.
  destruct (os_int_exit_waiting_call_environment environment critical sg original reference pointer
    initial entry_node handler suspended publication input_local private_input before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local node private_output middle after returned call None
    Hprefix_source Hacquire_source Hprefix_idle Hacquire_idle Henabled Hcase Hwhole) as [Hreturned [run Hsource]].
  assert (Hsaved_environment : exists (saved_run : flag_pend_scoped_environment_run environment critical input_local local active sg
    original (armv7a_irq_fiq_mask saved) initial before private_before_owner
    (orb prefix_stop (orb acquire_stop false)) resumed final after private_after_owner),
    flag_pend_scoped_environment_source environment critical input_local local active sg None
      original (armv7a_irq_fiq_mask saved) initial before private_before_owner
      (orb prefix_stop (orb acquire_stop false)) resumed final after private_after_owner saved_run).
  { rewrite Hrestored_mask; exists run; exact Hsource. }
  destruct Hsaved_environment as [saved_run Hsaved_source].
  destruct (os_sched_continuation_c_restore_execution_from_environment environment critical input_local local active sg
    original saved acquired initial caller_before private_before_owner private_after_owner private_before whole_before
    (orb prefix_stop (orb acquire_stop false)) resumed final after arch restore cursor written before final_cursor whole_after
    saved_run Hr0 Hcursor_mask Hinput Hprivate Hjoin Hprimitive_prefix Hsaved_source Hsuffix) as [caller_after Hactual].
  exists caller_after.
  eapply scoped_restore_event_output, scoped_restore_execution_complete_event; eassumption.
Qed.

End WaitingEvents.

End CompletedReturnedIRQFamily.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module CompletedSelectedWaiting.
Import PrimitiveComponent CriticalComponent PendPhaseCandidate SelectedCProgram SelectedCSource.
Import FlagWaitingRecovery FlagWaitingSelectedTake SelectedFamilyScope.
Import SelectedEnvironmentScopedEnvironment SelectedEnvironmentPhaseEffects CompletedCallerEvents.

Section ActualWaitingReturn.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (reference original : OsSchedCallContext) (pointer : Z)
  (initial : UCOS2_Verify_State) (first_heap : model)
  (initial_local next_local : Armv7aContinuation -> Assertion)
  (initial_private frame : Assertion) (saved : Z) (acquired : UCOS2_Verify_State)
  (stopped : bool) (returned : OsSchedCallContext) (current : UCOS2_Verify_State) (restored : model).
Let active := flag_pend_wait_active sg reference pointer.
Let receipt := flag_pend_waiting_receipt sg reference pointer original initial.
Context (run : kernel_c_sequence
  (kernel_program_selected_c_step environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin))
  initial first_heap
  (flag_pend_caller_save_input environment critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial ** initial_private)
  stopped current restored
  (coq_prop (flag_pend_call_endpoint_observations environment sg
    (FlagPendTaskCaller original) original initial returned current) &&
   flag_pend_caller_restore_input environment critical next_local
    (fun _ _ => receipt ** frame) sg (FlagPendTaskCaller returned)
    returned saved acquired current)).
Context (Hsource : kernel_program_selected_c_sequence_source environment critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ run)
  (Horiginal : kernel_call_task_source original initial)
  (Hreturned : kernel_call_task_source returned current)
  (Hcase : (exists waiter, current.(FlagState).(flagWaitNodes) pointer = Some waiter) \/
    initial.(FlagState).(flagWaitNodes) pointer = None).

(** The local publisher supplies the detached entry, or the same selected
    execution still owns the linked node. Neither case assumes a future owner. *)
Lemma selected_waiting_environment_from_return :
  forall arch (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
    cursor written middle final_cursor after,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor restored written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  exists (scoped : flag_pend_scoped_environment_run environment critical initial_local next_local active sg
    original (armv7a_irq_fiq_mask saved) initial first_heap initial_private
    (orb stopped false) returned current after frame),
  flag_pend_scoped_environment_source environment critical initial_local next_local active sg None
    original (armv7a_irq_fiq_mask saved) initial first_heap initial_private
    (orb stopped false) returned current after frame scoped.
Proof.
  intros arch restore cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix.
  assert (Hrecover : receipt |-- active returned current).
  { destruct Hcase as [[waiter Hnode]|Hnone].
    - eapply selected_linked_waiting_receipt; eassumption.
    - eapply selected_detached_waiting_receipt; eassumption. }
  eapply (selected_receipt_return_environment environment critical initial_local next_local initial_private
    active receipt frame sg original saved acquired initial first_heap stopped returned current restored
    arch restore cursor written middle final_cursor after run); eassumption.
Qed.

Lemma selected_waiting_save_output :
  forall close_arch (close : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical close_arch)
    cursor written middle final_cursor environment_heap,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition close cursor restored written middle ->
  armv7a_restore_suffix_transition close written middle final_cursor environment_heap ->
  forall caller_before private_before save_arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical save_arch)
    registers final_registers whole_after,
  flag_pend_caller_save_input environment critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial caller_before ->
  initial_private private_before -> join caller_before private_before first_heap ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current environment_heap
    final_registers current whole_after ->
  exists caller_after,
  flag_pend_selected_caller_save_output environment critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial
    caller_before final_registers.(kernel_save_r0) caller_after.
Proof.
  intros close_arch close cursor written middle final_cursor environment_heap Hr0 Hmask Hclose_prefix Hclose_suffix
    caller_before private_before save_arch save registers final_registers whole_after
    Hinput Hprivate Hjoin Hword Hvalid Hsaved_mask Hsuffix.
  destruct (selected_waiting_environment_from_return close_arch close cursor written middle final_cursor
    environment_heap Hr0 Hmask Hclose_prefix Hclose_suffix) as [scoped Hscoped].
  destruct (os_sched_continuation_c_save_execution_from_environment environment critical initial_local next_local active sg
    original (armv7a_irq_fiq_mask saved) initial caller_before initial_private frame private_before first_heap
    (orb stopped false) returned current environment_heap save_arch save registers final_registers whole_after
    scoped Hscoped Hinput Hprivate Hjoin Hword Hvalid Hsaved_mask Hsuffix) as [caller_after Hactual].
  exists caller_after.
  eapply scoped_save_event_output, scoped_save_execution_complete_event; eassumption.
Qed.

Lemma selected_waiting_restore_output :
  forall close_arch (close : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical close_arch)
    cursor written middle final_cursor environment_heap,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition close cursor restored written middle ->
  armv7a_restore_suffix_transition close written middle final_cursor environment_heap ->
  forall caller_before private_before whole_before caller_acquired restore_arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical restore_arch)
    caller_cursor caller_written caller_final whole_after,
  caller_cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask caller_cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical initial_local active sg
    (FlagPendTaskCaller original) original saved caller_acquired initial caller_before ->
  initial_private private_before -> join caller_before private_before whole_before ->
  armv7a_restore_prefix_transition restore caller_cursor whole_before caller_written first_heap ->
  armv7a_restore_suffix_transition restore caller_written environment_heap caller_final whole_after ->
  exists caller_after,
  flag_pend_selected_caller_restore_output environment critical initial_local active sg
    (FlagPendTaskCaller original) original saved caller_acquired initial caller_before caller_after.
Proof.
  intros close_arch close cursor written middle final_cursor environment_heap Hr0 Hmask Hclose_prefix Hclose_suffix
    caller_before private_before whole_before caller_acquired restore_arch restore
    caller_cursor caller_written caller_final whole_after Hcaller_r0 Hcaller_mask Hinput Hprivate Hjoin Hprefix Hsuffix.
  destruct (selected_waiting_environment_from_return close_arch close cursor written middle final_cursor
    environment_heap Hr0 Hmask Hclose_prefix Hclose_suffix) as [scoped Hscoped].
  destruct (os_sched_continuation_c_restore_execution_from_environment environment critical initial_local next_local active sg
    original saved caller_acquired initial caller_before initial_private frame private_before whole_before
    (orb stopped false) returned current environment_heap restore_arch restore
    caller_cursor caller_written first_heap caller_final whole_after scoped Hcaller_r0 Hcaller_mask Hinput Hprivate Hjoin
    Hprefix Hscoped Hsuffix) as [caller_after Hactual].
  exists caller_after.
  eapply scoped_restore_event_output, scoped_restore_execution_complete_event; eassumption.
Qed.

End ActualWaitingReturn.
End CompletedSelectedWaiting.
