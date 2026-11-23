Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_signal_protocol_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.lib.task_retirement.
Require Import Ucos2Verify.lib.tick.
Require Import Coq.Lists.List Coq.ZArith.ZArith.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.

(** The fixed source disables Multi. This fact removes the physical
    fields; it does NOT assert a value for arbitrary abstract task nodes. *)
Lemma tmr_task_selected_multi_disabled : forall sg state,
  UCOS2_state_inv sg state -> sg.(osKernelConfig).(cfgEventMultiEnabled) = false.
Proof.
  intros sg state [Hprofile _].
  unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto.
Qed.

(** The actual publication constructor chooses zero for disabled optional
    metadata and writes zero through the enabled source initializer. This
    is a property of the real commit node, not of every valid TCB. *)
Lemma tmr_task_init_commit_clear_fields : forall args acquired slot image,
  flag_active_event_clear (task_tcb_init_commit_node args acquired slot image) /\
  (task_tcb_init_commit_node args acquired slot image).(tcbFlagNode) = 0.
Proof. intros; repeat split; reflexivity. Qed.

Lemma tmr_task_init_published_multi_zero : forall sg args invocation acquired current slot image node,
  (task_tcb_init_published_state sg args invocation acquired current slot image).(TskState).(inUsedTaskStates)
    slot = Some node ->
  node.(tcbEventMultiPtr) = 0.
Proof.
  intros sg args invocation acquired current slot image node Hnode.
  change ((task_commit current.(TskState) args.(initPrio) invocation
    (task_tcb_init_commit_node args acquired slot image)).(inUsedTaskStates) slot = Some node) in Hnode.
  cbn [task_commit inUsedTaskStates task_tcb_init_commit_node
    task_tcb_init_node_from_free_image taskID] in Hnode.
  destruct (Z.eq_dec slot slot); [|contradiction].
  inversion Hnode; subst; reflexivity.
Qed.

Lemma tmr_task_pend_cleanup_multi_value : forall multi clear_message node,
  (task_event_pend_cleanup multi clear_message node).(tcbEventMultiPtr) =
    if multi then 0 else node.(tcbEventMultiPtr).
Proof. intros [] clear_message node; reflexivity. Qed.

Lemma tmr_task_pend_cleanup_clear_fields : forall sg state tid node,
  sem_pend_cleanup_entry sg state tid node -> node.(tcbEventMultiPtr) = 0 ->
  let cleaned := task_event_pend_cleanup sg.(osKernelConfig).(cfgEventMultiEnabled) false node in
  (event_pend_cleanup_state sg false state tid node).(TskState).(inUsedTaskStates) tid = Some cleaned /\
  flag_active_event_clear cleaned /\ cleaned.(tcbFlagNode) = 0.
Proof.
  intros sg state tid node Hentry Hptr cleaned.
  destruct (tmr_task_pend_cleanup_unregistered sg state tid node Hentry)
    as [Hlookup [Hevent [Hmulti Hflag]]].
  split; [exact Hlookup|]. split; [|exact Hflag].
  split; [exact Hevent|]. split; [exact Hmulti|].
  unfold cleaned; rewrite tmr_task_pend_cleanup_multi_value.
  destruct sg.(osKernelConfig).(cfgEventMultiEnabled); [reflexivity|exact Hptr].
Qed.

Lemma tmr_task_stage_multi_zero_fresh : forall sg call state,
  sem_pend_task_call_stage sg call state ->
  (forall node,
    state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
    node.(tcbEventMultiPtr) = 0) ->
  flag_active_fresh_registration call call state.
Proof.
  intros sg call state [[Horigin [Hactive Hcurrent]]
    [Hrunning [node [Hready [Hgeneration [Hnonidle [Hevent [Hmulti Hflag]]]]]]]] Hptr.
  exists node; split; [|exact Hflag].
  unfold flag_active_task_fields, task_tcb_init_stack_same_call.
  split; [repeat split; reflexivity|]. split; [exact Horigin|].
  split; [exact (proj1 Hready)|]. split; [exact Hgeneration|].
  split; [exact Hactive|]. split; [exact Hevent|]. split; [exact Hmulti|].
  apply Hptr; exact (proj1 Hready).
Qed.

(** Observe only this field, retaining the exact current node lookup.
    This is not equality of complete task maps or a readiness frame. *)
Lemma tmr_task_multi_pointer_update_eq : forall tasks selected previous next tid,
  tasks.(inUsedTaskStates) selected = Some previous ->
  next.(tcbEventMultiPtr) = previous.(tcbEventMultiPtr) ->
  option_map tcbEventMultiPtr
    ((glob_task_set_usedtask tasks selected next).(inUsedTaskStates) tid) =
  option_map tcbEventMultiPtr (tasks.(inUsedTaskStates) tid).
Proof.
  intros tasks selected previous next tid Hselected Hptr.
  eapply glob_task_set_usedtask_observation; [exact Hselected|exact Hptr].
Qed.

Lemma tmr_task_tick_multi_pointer : forall node,
  (tick_task_update node).(tcbEventMultiPtr) = node.(tcbEventMultiPtr).
Proof.
  intro node.
  pose proof (tick_task_preserves_non_timeout_fields node) as Hfields.
  cbv zeta in Hfields.
  tauto.
Qed.

Lemma tmr_task_event_task_rdy_multi_pointer : forall sg before eid kind message result priority after tid,
  event_task_rdy sg before eid kind message result = Some (priority, after) ->
  option_map tcbEventMultiPtr (after.(TskState).(inUsedTaskStates) tid) =
  option_map tcbEventMultiPtr (before.(TskState).(inUsedTaskStates) tid).
Proof.
  intros sg before eid kind message result priority after tid Hstep.
  unfold event_task_rdy in Hstep.
  destruct (before.(EventState).(inUsedEventStates) eid) as [event|] in Hstep; [|discriminate].
  destruct (before.(TskState).(prioTbl) (event_wait_priority before.(TskState) event))
    as [| |selected] in Hstep; try discriminate.
  destruct (before.(TskState).(inUsedTaskStates) selected) as [previous|] eqn:Hselected in Hstep;
    [|discriminate].
  injection Hstep as Hpriority Hafter; subst after.
  eapply tmr_task_multi_pointer_update_eq; [exact Hselected|reflexivity].
Qed.

Lemma tmr_task_event_broadcast_multi_pointer : forall sg eid kind message result before priorities after,
  event_broadcast sg eid kind message result before priorities after -> forall tid,
  option_map tcbEventMultiPtr (after.(TskState).(inUsedTaskStates) tid) =
  option_map tcbEventMultiPtr (before.(TskState).(inUsedTaskStates) tid).
Proof.
  intros sg eid kind message result before priorities after Hloop.
  induction Hloop as [entry event He Hempty|
    entry event priority middle priorities after He Hnonempty Hstep Htail IH]; intros tid.
  - reflexivity.
  - rewrite (IH tid); eapply tmr_task_event_task_rdy_multi_pointer; exact Hstep.
Qed.

(** Every case is an existing source action, with its actual branch and
    canonical transformer. Unlike sem_pend_wait_effect, this theorem does
    not erase the optional pointer before proving it unchanged. *)
Lemma tmr_task_source_client_multi_pointer : forall action sg before after,
  sem_pend_projected_source_client action -> kernel_client_step action sg before after ->
  forall tid,
  option_map tcbEventMultiPtr (after.(TskState).(inUsedTaskStates) tid) =
  option_map tcbEventMultiPtr (before.(TskState).(inUsedTaskStates) tid).
Proof.
  intros action sg before after Hsource Hstep tid.
  destruct Hsource as
    [actor oldprio newprio | actor priority | actor priority | selected |
     actor eid | actor eid opt | actor selected sp | actor priority | client Hframe |
     external context outgoing incoming resumed].
  - destruct Hstep as [_ [code [_ Hstep]]].
    destruct (before.(TskState).(prioTbl) newprio) in Hstep.
    + destruct Hstep as [selected [_ [_ Hstep]]].
      destruct (before.(TskState).(prioTbl) selected) in Hstep.
      * destruct Hstep as [_ ->]; reflexivity.
      * destruct Hstep as [_ ->]; reflexivity.
      * destruct Hstep as [previous [Hprevious [_ [_ [_ ->]]]]].
        eapply tmr_task_multi_pointer_update_eq; [exact Hprevious|reflexivity].
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [_ [result [cid [current [_ [_ [_ Hstep]]]]]]].
    destruct (before.(TskState).(prioTbl) (fst (task_suspend_selection sg priority current))) in Hstep.
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [previous [Hprevious [_ ->]]].
      eapply tmr_task_multi_pointer_update_eq; [exact Hprevious|reflexivity].
  - destruct Hstep as [_ [result [_ Hstep]]].
    destruct (before.(TskState).(prioTbl) priority) in Hstep.
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [previous [Hprevious Hstep]].
      destruct (task_is_suspended previous.(stat)) in Hstep;
        destruct Hstep as [_ ->]; [|reflexivity].
      eapply tmr_task_multi_pointer_update_eq; [exact Hprevious|reflexivity].
  - destruct Hstep as [previous [Hprevious ->]].
    rewrite tick_task_step_task_state_eq by exact Hprevious.
    eapply tmr_task_multi_pointer_update_eq; [exact Hprevious|apply tmr_task_tick_multi_pointer].
  - destruct Hstep as [result [event [He Hstep]]].
    lazymatch type of Hstep with
    | (if ?test then _ else _) => destruct test in Hstep
    end.
    + destruct Hstep as [fields [_ Hstep]].
      lazymatch type of Hstep with
      | (if ?test then _ else _) => destruct test in Hstep
      end;
        destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [_ [priority Hstep]].
      eapply tmr_task_event_task_rdy_multi_pointer; exact Hstep.
  - destruct Hstep as [result [event [He Hstep]]].
    lazymatch type of Hstep with
    | (if ?test then _ else _) => destruct test in Hstep
    end.
    + destruct Hstep as [_ ->]; reflexivity.
    + lazymatch type of Hstep with
      | (if ?test then _ else _) => destruct test in Hstep
      end.
      * destruct Hstep as [priorities [Hloop _]].
        eapply tmr_task_event_broadcast_multi_pointer; exact Hloop.
      * destruct Hstep as [priority [Hstep _]].
        eapply tmr_task_event_task_rdy_multi_pointer; exact Hstep.
  - change (after = os_sched_save_current_sp before selected sp) in Hstep; subst after.
    unfold os_sched_save_current_sp.
    destruct (before.(TskState).(inUsedTaskStates) selected) as [previous|] eqn:Hselected;
      [|reflexivity].
    eapply tmr_task_multi_pointer_update_eq; [exact Hselected|reflexivity].
  - destruct Hstep as [_ [result [_ Hstep]]].
    destruct (before.(TskState).(prioTbl) priority) in Hstep.
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [previous [Hprevious Hstep]].
      lazymatch type of Hstep with
      | (if ?test then _ else _) => destruct test in Hstep
      end;
        destruct Hstep as [_ ->]; [reflexivity|].
      eapply tmr_task_multi_pointer_update_eq; [exact Hprevious|reflexivity].
  - destruct (Hframe sg before after Hstep) as [Htasks Hrest].
    rewrite Htasks; reflexivity.
  - destruct (os_sched_install_client_state_frame external context outgoing incoming resumed
      sg before after Hstep) as [Htasks Hrest].
    rewrite Htasks; reflexivity.
Qed.

Lemma tmr_task_resumption_trace_multi_pointer :
  forall clients sg observer event_observer before stopped after,
  (forall action, clients action -> sem_pend_projected_source_client action) ->
  kernel_resumption_resource_trace clients sg observer event_observer before stopped after ->
  forall tid,
  option_map tcbEventMultiPtr (after.(TskState).(inUsedTaskStates) tid) =
  option_map tcbEventMultiPtr (before.(TskState).(inUsedTaskStates) tid).
Proof.
  intros clients sg observer event_observer before stopped after Hclients Htrace.
  apply kernel_resumption_resource_trace_erases in Htrace.
  induction Htrace as [state|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intros tid; [reflexivity|].
  rewrite (IH tid); eapply tmr_task_source_client_multi_pointer; [apply Hclients; exact Hin|exact Hstep].
Qed.

Lemma tmr_task_registered_return_multi_zero :
  forall environment critical sg original returned before after node,
  (forall action, critical.(critical_region_clients) action -> sem_pend_projected_source_client action) ->
  sem_pend_modular_call_history environment critical sg original before returned after ->
  before.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(tcbEventMultiPtr) = 0 ->
  forall current,
    after.(TskState).(inUsedTaskStates) returned.(os_sched_call_stack).(stackLeaseSlot) = Some current ->
    current.(tcbEventMultiPtr) = 0.
Proof.
  intros environment critical sg original returned before after node Hclients
    [Htrace [Hsame Havailable]] Hnode Hzero current Hcurrent.
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)
    as [Hinterval Hcontrol].
  pose proof (tmr_task_resumption_trace_multi_pointer critical.(critical_region_clients)
    sg original.(os_sched_call_invocation) None before false after Hclients Hinterval
    original.(os_sched_call_stack).(stackLeaseSlot)) as Hptr.
  rewrite (proj2 (proj2 Hsame)) in Hcurrent.
  rewrite Hcurrent, Hnode in Hptr; cbn in Hptr; congruence.
Qed.

(** Create/retire effects outside the smaller projected source family also
    have concrete field producers. Publication changes old head links;
    retirement changes neighbors and removes the actual target. The latter
    does not preserve a deleted Timer task or manufacture its return. *)
Lemma tmr_task_other_publication_multi_pointer : forall tasks priority invocation node tid,
  tid <> node.(taskID) ->
  option_map tcbEventMultiPtr ((task_commit tasks priority invocation node).(inUsedTaskStates) tid) =
  option_map tcbEventMultiPtr (tasks.(inUsedTaskStates) tid).
Proof.
  intros tasks priority invocation node tid Hother.
  rewrite (task_commit_observation addr tcbEventMultiPtr tasks priority invocation node tid
    (fun _ _ _ => eq_refl)).
  destruct (Z.eq_dec tid node.(taskID)); [contradiction|reflexivity].
Qed.

Lemma tmr_task_other_recycle_multi_pointer : forall sg tasks selected priority node name tid,
  tid <> selected ->
  option_map tcbEventMultiPtr ((task_recycle sg tasks selected priority node name).(inUsedTaskStates) tid) =
  option_map tcbEventMultiPtr (tasks.(inUsedTaskStates) tid).
Proof.
  intros sg tasks selected priority node name tid Hother.
  cbn [task_recycle inUsedTaskStates].
  rewrite (task_unlink_used_map_observation addr tcbEventMultiPtr
    tasks.(inUsedTaskStates) selected node tid (fun _ _ _ => eq_refl)).
  destruct (Z.eq_dec tid selected); [contradiction|reflexivity].
Qed.

(** Exact information loss in the OLD projection, not an executable C
    counterexample. The OtherFields constructor omits multiPtr, so that
    relation alone cannot prove the Fresh field even in a disabled build. *)
Lemma tmr_task_wait_projection_allows_multi_pointer : forall node pointer,
  sem_pend_wait_effect node
    (task_set_multi_fields node pointer node.(eventMultiWaitEvents) node.(eventMultiRdy)) /\
  (task_set_multi_fields node pointer node.(eventMultiWaitEvents) node.(eventMultiRdy)).(tcbEventMultiPtr) = pointer.
Proof.
  intros node pointer; split; [|reflexivity].
  apply SemPendWaitOtherFields; repeat split; reflexivity.
Qed.
