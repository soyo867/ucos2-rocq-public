Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.event_wait Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_proofs.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_boot_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_wake_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_always_call_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_public_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_repeated_irq_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_save_irq_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_irq_register_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A source stage, not a permanent kernel invariant. A locked caller can
    have suspended itself. Once both scheduler guards permit selection,
    an ordinary returning application call owns a live runnable current
    task. The current priority cache may be stale; it is not used here.
    The source producer, rather than a CPU-token interpretation, supplies
    this OS-side fact. *)
Definition mutex_del_task_call_stage (call : OsSchedCallContext)
  (state : UCOS2_Verify_State) : Prop :=
  kernel_call_task_source call state /\
  (os_sched_selection_enabled state = true ->
   exists node,
     state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
     is_effectively_ready node.(stat) node.(dly) = true).

(** Before OSStart no task has published a blocking wait. This describes
    the boot caller's established stage; the weaker owner-use history by
    itself does not establish it. It allows object creation/deletion and
    early error returns while keeping the original Boot origin. *)
Definition mutex_del_boot_call_stage (state : UCOS2_Verify_State) : Prop :=
  state.(SchedState).(isRunning) = false /\
  forall eid event, state.(EventState).(inUsedEventStates) eid = Some event ->
    event.(waitList) = [].

Definition mutex_del_call_stage (call : OsSchedCallContext)
  (state : UCOS2_Verify_State) : Prop :=
  match call.(os_sched_call_origin) with
  | BootInvocation => mutex_del_boot_call_stage state
  | RunningInvocation _ _ => mutex_del_task_call_stage call state
  end.

Lemma mutex_del_boot_initial_call_stage : forall sg task_name flag_name memory_name names call,
  call.(os_sched_call_origin) = BootInvocation ->
  mutex_del_call_stage call (UCOS2_boot_state sg task_name flag_name memory_name names).
Proof.
  intros; unfold mutex_del_call_stage; rewrite H.
  split; [reflexivity|intros; discriminate].
Qed.

Lemma mutex_del_task_call_stage_ready : forall sg call state,
  UCOS2_state_inv sg state -> mutex_del_task_call_stage call state ->
  os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> [].
Proof.
  intros sg call state Hvalid [_ Hstage] Henabled.
  destruct (Hstage Henabled) as [node [Hnode Hready]].
  pose proof (proj1 (proj1 (proj2 (proj2 Hvalid)))) as Hsched.
  pose proof (proj1 (proj2 (proj2 Hsched)) _ _ Hnode Hready) as Hin.
  intro Hempty; rewrite Hempty in Hin; contradiction.
Qed.

(** Registration uses the already configured ordinary API boundary. The
    ABI changes execution ownership only. TCB identity, runnable status
    and the disabled-scheduler alternative are carried by OS state. *)
Lemma mutex_del_sequential_call_stage : forall previous state,
  mutex_del_call_stage previous state ->
  mutex_del_call_stage
    (kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation))
    (replace_TskS (task_begin_invocation previous.(os_sched_call_origin) state.(TskState)) state).
Proof.
  intros previous state Hstage.
  unfold mutex_del_call_stage in *.
  cbn [kernel_sequential_call os_sched_call_origin].
  destruct previous.(os_sched_call_origin) eqn:Horigin.
  - exact Hstage.
  - destruct Hstage as [[Hbinding [Hactive Hcurrent]] Hready].
    split; [|exact Hready].
    unfold kernel_call_task_source.
    cbn [kernel_sequential_call os_sched_call_origin os_sched_call_invocation os_sched_call_stack].
    split; [exact Hbinding|]. split; [|exact Hcurrent].
    rewrite <- Horigin; apply task_begin_invocation_active; exact (proj2 (proj2 Hactive)).
Qed.

(** Pointwise runnable preservation concerns real TCB Stat/Dly fields.
    It does not add a ghost state or assume an eventual scheduling return. *)
Definition mutex_del_preserves_runnable (before after : UCOS2_Verify_State) : Prop :=
  forall tid old, before.(TskState).(inUsedTaskStates) tid = Some old ->
    is_effectively_ready old.(stat) old.(dly) = true ->
    exists node, after.(TskState).(inUsedTaskStates) tid = Some node /\
      is_effectively_ready node.(stat) node.(dly) = true.

Lemma mutex_del_preserves_runnable_refl : forall state,
  mutex_del_preserves_runnable state state.
Proof. intros state tid old Hnode Hready; exists old; auto. Qed.

Lemma mutex_del_preserves_runnable_trans : forall before middle after,
  mutex_del_preserves_runnable before middle -> mutex_del_preserves_runnable middle after ->
  mutex_del_preserves_runnable before after.
Proof.
  intros before middle after Hfirst Hsecond tid old Hnode Hready.
  destruct (Hfirst tid old Hnode Hready) as [node [Hnode' Hready']].
  exact (Hsecond tid node Hnode' Hready').
Qed.

Lemma mutex_del_prepare_preserves_runnable : forall sg mutex before after,
  mutex_del_prepare sg mutex before after -> mutex_del_preserves_runnable before after.
Proof.
  intros sg mutex before after Hprepare; unfold mutex_del_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis));
    [subst; apply mutex_del_preserves_runnable_refl|].
  destruct mutex.(mfOwner) as [owner|].
  - destruct Hprepare as [node [priority [Hnode [_ ->]]]].
    unfold mutex_del_owner_priority_state; destruct Z.eq_dec.
    + intros tid old Hold Hready; exists old; exact (conj Hold Hready).
    + intros tid old Hold Hready.
      cbn [mutex_del_relocated_state replace_SchedS replace_TskS TskState
        mutex_del_relocated_tasks inUsedTaskStates glob_task_set_usedtask].
      destruct (Z.eqb tid owner) eqn:Hsame.
      * apply Z.eqb_eq in Hsame; subst tid; assert (old = node) by congruence; subst old.
        exists (mutex_priority_task node priority); split; [reflexivity|exact Hready].
      * exists old; auto.
  - subst; intros tid old Hold Hready; exists old; exact (conj Hold Hready).
Qed.

Lemma mutex_del_wake_preserves_runnable : forall sg eid kind message result before priority after,
  event_task_rdy sg before eid kind message result = Some (priority, after) ->
  mutex_del_preserves_runnable before after.
Proof.
  intros sg eid kind message result before priority after Hwake.
  unfold event_task_rdy in Hwake.
  destruct (before.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
  destruct (before.(TskState).(prioTbl) (event_wait_priority before.(TskState) event))
    as [| |slot]; try discriminate.
  destruct (before.(TskState).(inUsedTaskStates) slot) as [node|] eqn:Hnode; [|discriminate].
  injection Hwake as _ <-; intros tid old Hold Hready.
  cbn [event_wake_state replace_SchedS replace_EventS replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
  destruct (Z.eqb tid slot) eqn:Hsame.
  - apply Z.eqb_eq in Hsame; subst tid; assert (old = node) by congruence; subst old.
    exists (task_event_wake_single node kind message result); split; [reflexivity|].
    apply task_event_wake_single_keeps_ready_task_ready; exact Hready.
  - exists old; auto.
Qed.

Lemma mutex_del_broadcast_preserves_runnable : forall sg eid kind message result before priorities after,
  event_broadcast sg eid kind message result before priorities after ->
  mutex_del_preserves_runnable before after.
Proof.
  intros sg eid kind message result before priorities after Hrun; induction Hrun.
  - apply mutex_del_preserves_runnable_refl.
  - eapply mutex_del_preserves_runnable_trans; [|exact IHHrun].
    eapply mutex_del_wake_preserves_runnable; eassumption.
Qed.

Lemma mutex_del_critical_preserves_runnable : forall sg eid option before result after,
  mutex_del_critical sg eid option before result after -> mutex_del_preserves_runnable before after.
Proof.
  intros sg eid option before result after [event [mutex [_ [_ [_ Hrun]]]]].
  destruct (Z.eq_dec option 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
    + destruct Hrun as [prepared [Hprepare [-> _]]].
      change (mutex_del_preserves_runnable before prepared).
      eapply mutex_del_prepare_preserves_runnable; exact Hprepare.
    + destruct Hrun as [-> _]; apply mutex_del_preserves_runnable_refl.
  - destruct (Z.eq_dec option 1).
    + destruct Hrun as [prepared [priorities [drained [Hprepare [Hwake [-> _]]]]]].
      change (mutex_del_preserves_runnable before drained).
      eapply mutex_del_preserves_runnable_trans.
      * eapply mutex_del_prepare_preserves_runnable; exact Hprepare.
      * eapply mutex_del_broadcast_preserves_runnable; exact Hwake.
    + destruct Hrun as [-> _]; apply mutex_del_preserves_runnable_refl.
Qed.

Lemma mutex_del_prepare_interrupt_frame : forall sg mutex before after,
  mutex_del_prepare sg mutex before after -> after.(IntrState) = before.(IntrState) /\
    after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros sg mutex before after Hprepare; unfold mutex_del_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [subst; auto|].
  destruct mutex.(mfOwner) as [owner|]; [|subst; auto].
  destruct Hprepare as [node [priority [_ [_ ->]]]].
  unfold mutex_del_owner_priority_state; destruct Z.eq_dec; split; reflexivity.
Qed.

Lemma mutex_del_wake_interrupt_frame : forall sg eid kind message result before priority after,
  event_task_rdy sg before eid kind message result = Some (priority, after) ->
  after.(IntrState) = before.(IntrState) /\
    after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros sg eid kind message result before priority after Hwake; unfold event_task_rdy in Hwake.
  destruct (before.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
  destruct (before.(TskState).(prioTbl) (event_wait_priority before.(TskState) event))
    as [| |slot]; try discriminate.
  destruct (before.(TskState).(inUsedTaskStates) slot) as [node|]; [|discriminate].
  injection Hwake as _ <-; split; [reflexivity|].
  cbn [event_wake_state replace_SchedS SchedState].
  unfold sched_wake_by_status.
  match goal with |- context [if ?test then _ else _] => destruct test end; reflexivity.
Qed.

Lemma mutex_del_broadcast_interrupt_frame : forall sg eid kind message result before priorities after,
  event_broadcast sg eid kind message result before priorities after ->
  after.(IntrState) = before.(IntrState) /\
    after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros sg eid kind message result before priorities after Hrun; induction Hrun; [auto|].
  destruct (mutex_del_wake_interrupt_frame _ _ _ _ _ _ _ _ H1); intuition congruence.
Qed.

Lemma mutex_del_critical_interrupt_frame : forall sg eid option before result after,
  mutex_del_critical sg eid option before result after ->
  after.(IntrState) = before.(IntrState) /\
    after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros sg eid option before result after [event [mutex [_ [_ [_ Hrun]]]]].
  destruct (Z.eq_dec option 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
    + destruct Hrun as [prepared [Hprepare [-> _]]].
      exact (mutex_del_prepare_interrupt_frame _ _ _ _ Hprepare).
    + destruct Hrun as [-> _]; auto.
  - destruct (Z.eq_dec option 1).
    + destruct Hrun as [prepared [priorities [drained [Hprepare [Hwake [-> _]]]]]].
      destruct (mutex_del_prepare_interrupt_frame _ _ _ _ Hprepare),
        (mutex_del_broadcast_interrupt_frame _ _ _ _ _ _ _ _ Hwake); cbn; intuition congruence.
    + destruct Hrun as [-> _]; auto.
Qed.

Lemma mutex_del_call_fields_preserve_task_source : forall call before after,
  mutex_del_call_fields_eq before after -> kernel_call_task_source call before ->
  kernel_call_task_source call after.
Proof.
  intros call before after [Hnodes [Hstacks [Hlife [Hcurrent Hprivate]]]]
    [Horigin [Hactive Hexecution]].
  split; [exact Horigin|]. split.
  - unfold task_invocation_active in *; rewrite Hlife.
    destruct Hactive as [Hinv [Hret Hlive]].
    split; [exact Hinv|]. split; [exact Hret|].
    unfold task_invocation_origin_live in *; rewrite Horigin in *.
    destruct Hlive as [old [Hold Hgen]].
    specialize (Hnodes call.(os_sched_call_stack).(stackLeaseSlot)); rewrite Hold in Hnodes.
    destruct (after.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot))
      as [node|] eqn:Hnode; cbn in Hnodes; [|discriminate].
    injection Hnodes as Hgen' Hsp; exists node; split; [reflexivity|congruence].
  - unfold task_execution_current in *; rewrite Horigin in *; rewrite Hcurrent; exact Hexecution.
Qed.

(** Actual priority relocation, all wake iterations and recycle preserve
    a runnable caller. This works for all four prepare branches and every
    option; no extra case-specific ready assumption is inserted. *)
Lemma mutex_del_critical_preserves_task_call_stage : forall sg eid option before result after call,
  mutex_del_critical sg eid option before result after ->
  mutex_del_task_call_stage call before -> mutex_del_task_call_stage call after.
Proof.
  intros sg eid option before result after call Hcritical [Hsource Hready].
  split.
  - eapply mutex_del_call_fields_preserve_task_source;
      [eapply mutex_del_critical_call_fields_eq; exact Hcritical|exact Hsource].
  - intros Henabled.
    assert (Hentry_enabled : os_sched_selection_enabled before = true).
    { unfold os_sched_selection_enabled in *.
      rewrite (proj1 (mutex_del_critical_interrupt_frame _ _ _ _ _ _ Hcritical)) in Henabled.
      exact Henabled. }
    destruct (Hready Hentry_enabled) as [node [Hnode Hrun]].
    exact (mutex_del_critical_preserves_runnable _ _ _ _ _ _ Hcritical _ _ Hnode Hrun).
Qed.

Lemma mutex_del_prepare_preserves_boot_call_stage : forall sg mutex before after,
  mutex_del_prepare sg mutex before after -> mutex_del_boot_call_stage before ->
  mutex_del_boot_call_stage after.
Proof.
  intros sg mutex before after Hprepare [Hrunning Hwaits]; split.
  - rewrite (proj2 (mutex_del_prepare_interrupt_frame _ _ _ _ Hprepare)); exact Hrunning.
  - rewrite (mutex_del_prepare_event_state_eq _ _ _ _ Hprepare); exact Hwaits.
Qed.

Lemma mutex_del_boot_broadcast_empty : forall sg eid kind message result before priorities after,
  mutex_del_boot_call_stage before ->
  event_broadcast sg eid kind message result before priorities after ->
  priorities = [] /\ after = before.
Proof.
  intros sg eid kind message result before priorities after [_ Hwaits] Hbroadcast.
  inversion Hbroadcast; subst; [auto|].
  rewrite (Hwaits _ _ H) in H0; contradiction H0; reflexivity.
Qed.

Lemma mutex_del_recycle_preserves_boot_call_stage : forall sg eid event state,
  mutex_del_boot_call_stage state ->
  mutex_del_boot_call_stage (mutex_del_recycle_state sg eid event state).
Proof.
  intros sg eid event state [Hrunning Hwaits]; split; [exact Hrunning|].
  intros other node Hnode.
  change ((if Z.eq_dec other eid then None else state.(EventState).(inUsedEventStates) other) = Some node) in Hnode.
  destruct (Z.eq_dec other eid); [discriminate|eapply Hwaits; exact Hnode].
Qed.

(** Boot ALWAYS is still accepted: its existing empty wait lists make the
    source schedule-request bit false. This is a consequence of the boot
    stage and the original C guard, not a new branch in the implementation. *)
Lemma mutex_del_critical_boot_return : forall sg eid option before result after,
  mutex_del_boot_call_stage before -> mutex_del_critical sg eid option before result after ->
  snd (snd result) = false /\ mutex_del_boot_call_stage after.
Proof.
  intros sg eid option before result after Hboot
    [event [mutex [Hlookup [_ [_ Hrun]]]]].
  pose proof (proj2 Hboot eid event Hlookup) as Hempty.
  destruct (Z.eq_dec option 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
    + destruct Hrun as [prepared [Hprepare [-> ->]]]; split; [reflexivity|].
      apply mutex_del_recycle_preserves_boot_call_stage.
      eapply mutex_del_prepare_preserves_boot_call_stage; eassumption.
    + destruct Hrun as [-> ->]; auto.
  - destruct (Z.eq_dec option 1).
    + destruct Hrun as [prepared [priorities [drained [Hprepare [Hwake [-> ->]]]]]].
      assert (Hprepared : mutex_del_boot_call_stage prepared)
        by (eapply mutex_del_prepare_preserves_boot_call_stage; eassumption).
      destruct (mutex_del_boot_broadcast_empty _ _ _ _ _ _ _ _ Hprepared Hwake) as [Hpriorities ->].
      split; [rewrite Hempty; reflexivity|].
      apply mutex_del_recycle_preserves_boot_call_stage; exact Hprepared.
    + destruct Hrun as [-> ->]; auto.
Qed.

Lemma mutex_del_critical_preserves_call_stage : forall sg eid option before result after call,
  mutex_del_call_stage call before -> mutex_del_critical sg eid option before result after ->
  mutex_del_call_stage call after.
Proof.
  intros sg eid option before result after call Hstage Hcritical.
  unfold mutex_del_call_stage in *; destruct call.(os_sched_call_origin).
  - exact (proj2 (mutex_del_critical_boot_return _ _ _ _ _ _ Hstage Hcritical)).
  - eapply mutex_del_critical_preserves_task_call_stage; eassumption.
Qed.

(** The critical caller consumes the strengthened source stage to justify
    the real optional scheduler. Locked paths need no runnable task; when
    selection is enabled the same current task establishes nonemptiness.
    The full public result still requires actual Restore/scheduler returns. *)
Lemma mutex_del_critical_schedule_entry : forall sg eid option before result after call,
  mutex_del_call_stage call before -> mutex_del_critical sg eid option before result after ->
  UCOS2_state_inv sg after -> snd (snd result) = true ->
  mutex_del_task_call_stage call after /\
  (os_sched_selection_enabled after = true -> after.(SchedState).(readyList) <> []).
Proof.
  intros sg eid option before result after call Hstage Hcritical Hvalid Hschedule.
  assert (Htask : mutex_del_task_call_stage call after).
  { unfold mutex_del_call_stage in Hstage; destruct call.(os_sched_call_origin).
    - pose proof (proj1 (mutex_del_critical_boot_return _ _ _ _ _ _ Hstage Hcritical)); congruence.
    - eapply mutex_del_critical_preserves_task_call_stage; eassumption. }
  split; [exact Htask|]. intros; eapply mutex_del_task_call_stage_ready; eassumption.
Qed.

Definition mutex_del_source_entry environment external platform sg call mask state : Assertion :=
  coq_prop (mutex_del_call_stage call state) &&
  mutex_del_runtime_entry environment external platform sg call mask state.

(** Admission is required only if the original ordered prefix continues.
    NULL, wrong-Type and ISR errors retain their old input domain; they do
    not need a task-stage witness merely to store the error and return. *)
Definition mutex_del_call_admission call state pe eid : Prop :=
  mutex_del_parent_prefix_ok pe state eid -> mutex_del_call_stage call state.

Definition mutex_del_source_input environment external platform sg call mask state pe eid : Assertion :=
  coq_prop (mutex_del_call_admission call state pe eid) &&
  mutex_del_runtime_entry environment external platform sg call mask state.

Lemma mutex_del_source_entry_admission : forall environment external platform sg call mask state pe eid,
  mutex_del_source_entry environment external platform sg call mask state |--
  mutex_del_source_input environment external platform sg call mask state pe eid.
Proof.
  intros; unfold mutex_del_source_entry, mutex_del_source_input, mutex_del_call_admission; entailer!.
Qed.

Lemma mutex_del_source_input_early_return : forall environment external platform sg call mask state pe eid error,
  mutex_del_before_save_error pe (event_slot_type_value state.(EventState) eid)
    state.(IntrState).(intNesting) = Some error ->
  mutex_del_runtime_entry environment external platform sg call mask state |--
  mutex_del_source_input environment external platform sg call mask state pe eid.
Proof.
  intros; unfold mutex_del_source_input, mutex_del_call_admission, mutex_del_parent_prefix_ok;
    entailer!; congruence.
Qed.

Lemma mutex_del_source_input_continue : forall environment external platform sg call mask state pe eid,
  mutex_del_parent_prefix_ok pe state eid ->
  mutex_del_source_input environment external platform sg call mask state pe eid |--
  mutex_del_source_entry environment external platform sg call mask state.
Proof.
  intros; unfold mutex_del_source_input, mutex_del_source_entry, mutex_del_call_admission;
    entailer!; auto.
Qed.

(** Boot is established at the existing concrete initializer checkpoint.
    Its startup CPU/stack bytes are supplied explicitly. This is not a
    proof of the OSInit/BSP body or of later system-task creation calls. *)
Lemma mutex_del_boot_source_entry : forall environment sg task_name flag_name memory_name names call mask,
  call.(os_sched_call_origin) = BootInvocation ->
  selected_kernel_profile sg -> init_tcb_list_profile sg -> valid_name_resources names ->
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
   sg.(osKernelConfig).(cfgMemoryNames) = true ->
   exists chars, readable_name names memory_name chars) ->
  kernel_boot_initializer_post sg task_name flag_name memory_name names ** unmap_table_rep sg **
    kernel_call_execution_owned environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) call mask |--
  mutex_del_source_entry environment environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
    sg call mask (UCOS2_boot_state sg task_name flag_name memory_name names).
Proof.
  intros environment sg task_name flag_name memory_name names call mask Horigin Hprofile Htcb Hnames Hmemory.
  set (state := UCOS2_boot_state sg task_name flag_name memory_name names).
  pose proof (mutex_del_boot_initial_call_stage sg task_name flag_name memory_name names call Horigin) as Hstage.
  fold state in Hstage.
  assert (Hprivate : event_private_pool_rep sg state.(EventState) --||-- emp).
  { apply event_private_pool_empty; intros; reflexivity. }
  assert (Htypes : mutex_del_private_types_non_mutex state.(EventState)).
  { apply mutex_del_private_types_initial. }
  sep_apply_l_atomic (mutex_program_selected_boot_resources sg task_name flag_name memory_name names
    Hprofile Htcb Hnames Hmemory).
  unfold mutex_program_resources; Intros_p Hreachable.
  eapply derivable1_trans with (y := kernel_call_execution_owned environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) call mask ** mutex_del_stack_resources sg state).
  - unfold mutex_del_stack_resources; rewrite Hprivate; entailer!.
  - sep_apply_l_atomic (kernel_stack_inv_boot _ _ _ environment.(mutex_del_call_continuations)
      mutex_del_stack_resources sg state task_name eq_refl).
    unfold mutex_del_source_entry, mutex_del_runtime_entry; Exists environment.
    unfold mutex_del_callsite_environment, kernel_stack_call_closed, task_stack_call_active_key.
    rewrite Horigin; entailer!.
Qed.

(** The already proved selector/install/restore post establishes current
    and ready at the actual return cut. Liveness is the retained original
    invocation, supplied by the intervening source trace. Del's private
    ECB pool is the CURRENT pool at this cut, not an old pool framed across
    a foreign task's execution. *)
Lemma mutex_del_selected_source_entry : forall environment sg original pc lr incoming selected node state,
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  mutex_program_selected_reachable sg state -> mutex_del_private_types_non_mutex state.(EventState) ->
  task_stack_key incoming = task_stack_key original.(os_sched_call_stack) ->
  os_sched_source_selected_post environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
    environment.(mutex_del_call_port) environment.(mutex_del_call_continuations) sg
    (armv7a_call_focus original pc lr) incoming selected node state **
    unmap_table_rep sg ** event_private_pool_rep sg state.(EventState) |--
  mutex_del_source_entry environment environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
    sg (armv7a_continuation_resumed_call selected original)
    (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) state.
Proof.
  intros environment sg original pc lr incoming selected node state Horigin Hactive Hreach Htypes Hkey.
  unfold os_sched_source_selected_post; Intros.
  assert (Hlease : selected.(armv7a_continuation_stack) = incoming) by tauto.
  assert (Hfocused : armv7a_continuation_focus_binding (armv7a_call_focus original pc lr) selected).
  { assert (Hfocus_key : task_stack_key incoming = armv7a_call_focus_key (armv7a_call_focus original pc lr))
      by exact Hkey; tauto. }
  destruct Hfocused as [Hcall [Hpc Hlr]].
  assert (Hready : sched_current_ready_at state.(TskState) state.(SchedState) incoming.(stackLeaseSlot) node)
    by tauto.
  assert (Hslot : incoming.(stackLeaseSlot) = original.(os_sched_call_stack).(stackLeaseSlot))
    by exact (f_equal fst Hkey).
  assert (Hgeneration : incoming.(stackLeaseGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration))
    by exact (f_equal snd Hkey).
  assert (Hstage : mutex_del_call_stage (armv7a_continuation_resumed_call selected original) state).
  { unfold mutex_del_call_stage; cbn [armv7a_continuation_resumed_call os_sched_call_origin]; rewrite Horigin.
    unfold mutex_del_task_call_stage, kernel_call_task_source.
    cbn [armv7a_continuation_resumed_call os_sched_call_origin os_sched_call_invocation os_sched_call_stack].
    rewrite Hlease; split.
    - split; [rewrite Hslot, Hgeneration; exact Horigin|]. split; [exact Hactive|].
      unfold task_execution_current; rewrite Horigin, <- Hslot; exact (proj1 (proj2 Hready)).
    - intros; exists node; exact (conj (proj1 Hready) (proj2 (proj2 (proj2 (proj2 Hready))))). }
  assert (Hkey_active : task_stack_call_active_key (armv7a_continuation_resumed_call selected original) =
      Some (task_stack_key incoming)).
  { unfold task_stack_call_active_key; cbn [armv7a_continuation_resumed_call os_sched_call_origin].
    rewrite Horigin; cbn [armv7a_continuation_resumed_call os_sched_call_stack].
    unfold task_stack_key; rewrite Hslot, Hgeneration; reflexivity. }
  unfold armv7a_task_restored_execution; cbn [armv7a_call_focus armv7a_focus_call] in Hcall; rewrite Hcall.
  sep_apply_l_atomic (armv7a_task_call_stacks_forget _ _ _ environment.(mutex_del_call_continuations)
    state.(TskState) (armv7a_call_focus original pc lr) state.(TskState).(parkedTaskStacks)).
  unfold mutex_del_source_entry, mutex_del_runtime_entry; Exists environment.
  unfold kernel_stack_call_closed, kernel_stack_inv, mutex_del_stack_resources, mutex_del_callsite_environment.
  rewrite kernel_program_inv_split_unmap, Hkey_active; entailer!.
Qed.

(** The None destination is first task entry. Readiness comes from the
    same selector post; the existing initial-call ABI only registers the
    initial invocation and exchanges its execution/stack authority. *)
Lemma mutex_del_selected_initial_source_entry : forall environment
  (entry : Armv7aInitialCallABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  sg focus incoming selected node state,
  armv7a_initial_frame_binding selected -> selected.(armv7a_continuation_call) = None ->
  task_stack_fragments_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords)
    0 selected.(armv7a_continuation_fragments) ->
  mutex_program_selected_reachable sg state -> mutex_del_private_types_non_mutex state.(EventState) ->
  os_sched_source_selected_post environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
    environment.(mutex_del_call_port) environment.(mutex_del_call_continuations) sg
    focus incoming selected node state ** unmap_table_rep sg ** event_private_pool_rep sg state.(EventState) |--
  let call := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments) in
  let registered := armv7a_initial_call_registered selected state in
  mutex_del_source_entry environment environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
    sg call (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) registered.
Proof.
  intros environment entry sg focus incoming selected node state Hbinding Hnone Hfragments Hreach Htypes.
  cbv zeta.
  set (call := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments)).
  set (registered := armv7a_initial_call_registered selected state).
  unfold os_sched_source_selected_post; Intros.
  assert (Hlease : selected.(armv7a_continuation_stack) = incoming) by tauto.
  assert (Hready : sched_current_ready_at state.(TskState) state.(SchedState) incoming.(stackLeaseSlot) node)
    by tauto.
  assert (Hgen : node.(taskGeneration) = incoming.(stackLeaseGeneration)) by tauto.
  assert (Hcovered : task_stack_live_coverage state.(TskState) (Some (task_stack_key incoming))) by tauto.
  assert (Hcurrent : task_current_at state selected.(armv7a_continuation_stack).(stackLeaseSlot)
    selected.(armv7a_continuation_stack).(stackLeaseGeneration)).
  { rewrite Hlease; split; [exact (proj1 (proj2 Hready))|].
    exists node; exact (conj (proj1 Hready) Hgen). }
  unfold armv7a_task_restored_execution; rewrite Hnone.
  pose proof (armv7a_initial_call_register_resources _ _ _
    environment.(mutex_del_call_continuations) entry sg state selected
    selected.(armv7a_continuation_fragments) Hbinding Hfragments Hcurrent) as Hregister.
  cbv zeta in Hregister; sep_apply_l_atomic Hregister.
  Intros.
  assert (Htask : kernel_call_task_source call registered) by assumption.
  assert (Hstage : mutex_del_call_stage call registered).
  { unfold mutex_del_call_stage, call; cbn [armv7a_initial_call os_sched_call_origin].
    split; [exact Htask|]. intros; exists node.
    cbn [armv7a_initial_call os_sched_call_stack]; rewrite Hlease.
    exact (conj (proj1 Hready) (proj2 (proj2 (proj2 (proj2 Hready))))). }
  assert (Hreachable : mutex_program_selected_reachable sg registered).
  { eapply mutex_program_source_step_reachable; [exact Hreach|].
    apply MutexOwnerSourceFrame; reflexivity. }
  sep_apply_l_atomic (armv7a_task_call_stacks_forget _ _ _ environment.(mutex_del_call_continuations)
    state.(TskState) focus state.(TskState).(parkedTaskStacks)).
  unfold mutex_del_source_entry, mutex_del_runtime_entry; Exists environment.
  unfold kernel_stack_call_closed, kernel_stack_inv, mutex_del_stack_resources, mutex_del_callsite_environment.
  rewrite kernel_program_inv_split_unmap.
  fold call registered.
  change (armv7a_task_stack_continuations environment.(mutex_del_call_continuations)
    registered.(TskState) registered.(TskState).(parkedTaskStacks)) with
    (armv7a_task_stack_continuations environment.(mutex_del_call_continuations)
      state.(TskState) state.(TskState).(parkedTaskStacks)).
  assert (Hcoverage : task_stack_live_coverage registered.(TskState) (task_stack_call_active_key call)).
  { unfold task_stack_call_active_key, call, armv7a_initial_call; cbn [os_sched_call_origin].
    rewrite Hlease; exact Hcovered. }
  entailer!.
Qed.

(** The same actual API return/next-entry boundary already used by Task
    and Sem. This producer preserves the established OS stage and registers
    a fresh invocation. No ready property is obtained from the ABI law. *)
Lemma mutex_del_sequential_source_entry : forall environment
  (boundary : KernelSequentialCallABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform))
  sg previous mask state before after (frame : Assertion),
  kernel_sequential_call_source boundary previous
    state.(TskState).(taskLifecycle).(taskNextInvocation) before after ->
  (mutex_del_source_entry environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) sg previous mask state ** frame) before ->
  let call := kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation) in
  let registered := replace_TskS
    (task_begin_invocation previous.(os_sched_call_origin) state.(TskState)) state in
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (mutex_del_source_entry environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) sg call mask registered ** frame) after.
Proof.
  intros environment boundary sg previous mask state before after frame
    Hsource Hbefore call registered.
  assert (Hopen : mutex_del_source_entry environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg previous mask state ** frame |--
      coq_prop (mutex_del_call_stage previous state) &&
      (kernel_call_execution_owned environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) previous mask **
       (kernel_stack_inv environment.(mutex_del_call_continuations) mutex_del_stack_resources sg
        (task_stack_call_active_key previous) state ** frame))).
  { unfold mutex_del_source_entry, mutex_del_runtime_entry; Intros selected.
    destruct H0 as [_ Henv]; subst selected.
    unfold kernel_stack_call_closed; entailer!. }
  destruct (Hopen before Hbefore) as [Hstage Howned].
  destruct (kernel_sequential_call_owned_entry environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) boundary previous
    state.(TskState).(taskLifecycle).(taskNextInvocation) mask before after _ Hsource Howned)
    as [Hmemory Hreturned].
  fold call in Hreturned; split; [exact Hmemory|].
  assert (Hlive : task_invocation_origin_live state.(TskState) previous.(os_sched_call_origin)).
  { unfold mutex_del_call_stage in Hstage; destruct previous.(os_sched_call_origin) eqn:Horigin;
      [exact I|].
    destruct Hstage as [[_ [Hactive _]] _]; rewrite <- Horigin; exact (proj2 (proj2 Hactive)). }
  pose proof (mutex_del_sequential_call_stage previous state Hstage) as Hregistered.
  fold call registered in Hregistered.
  match type of Hreturned with ?P after => match goal with |- ?Q after =>
    assert (Hregister : P |-- Q) end end.
  { unfold mutex_del_source_entry, mutex_del_runtime_entry; Exists environment.
    unfold kernel_stack_inv, mutex_del_stack_resources; rewrite !kernel_program_inv_split_unmap.
    Intros.
    assert (Hreachable : mutex_program_selected_reachable sg state) by tauto.
    assert (Hreachable' : mutex_program_selected_reachable sg registered).
    { eapply mutex_program_source_step_reachable; [exact Hreachable|].
      apply MutexOwnerSourceFrame; reflexivity. }
    sep_apply_l_atomic (UCOS2_inv_begin_task_invocation sg state previous.(os_sched_call_origin) Hlive).
    change (armv7a_task_stack_continuations environment.(mutex_del_call_continuations)
      registered.(TskState) registered.(TskState).(parkedTaskStacks)) with
      (armv7a_task_stack_continuations environment.(mutex_del_call_continuations)
        state.(TskState) state.(TskState).(parkedTaskStacks)).
    unfold kernel_stack_call_closed, kernel_stack_inv, mutex_del_stack_resources,
      mutex_del_callsite_environment.
    rewrite kernel_program_inv_split_unmap.
    change (task_stack_call_active_key call) with (task_stack_call_active_key previous).
    entailer!. }
  exact (Hregister after Hreturned).
Qed.

(** This is the actual ALWAYS body consumer. It joins the previously
    checked concrete wake loop, repeated PCP clear and recycle stores to
    the source-stage preservation above. Boot produces no scheduler call;
    a task's enabled selector obtains nonemptiness from its current TCB,
    including when every woken waiter remains suspended. *)
Lemma mutex_del_always_after_prepare_stage : forall sg eid entry prepared event mutex call before after
  (frame : Assertion),
  event_object_layout_prop sg eid -> mutex_del_call_stage call entry ->
  (mutex_del_parent_prepared sg eid entry prepared event mutex ** unmap_table_rep sg ** frame) before ->
  mutex_del_always_after_prepare_execution sg (event_addr sg eid) before after ->
  let checkpoint := mutex_del_always_checkpoint sg eid event prepared in
  let request := negb (Z.eqb (encode_event_wait_grp event.(waitList) entry.(TskState)) 0) in
  mutex_del_call_stage call checkpoint /\
  (request = true -> mutex_del_task_call_stage call checkpoint /\
    (os_sched_selection_enabled checkpoint = true -> checkpoint.(SchedState).(readyList) <> [])) /\
  (kernel_program_inv sg checkpoint ** frame) after.
Proof.
  intros sg eid entry prepared event mutex call before after frame Hlayout Hstage Hpre Hrun
    checkpoint request.
  destruct (mutex_del_always_after_prepare_resources sg eid entry prepared event mutex before after frame
    Hlayout Hpre Hrun) as [Hcritical Hafter].
  fold checkpoint request in Hcritical, Hafter.
  assert (Hvalid : UCOS2_state_inv sg checkpoint).
  { match type of Hafter with ?P after => assert (Hobserve : P |--
      coq_prop (UCOS2_state_inv sg checkpoint) && TT) end.
    { unfold kernel_program_inv, UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve after Hafter)). }
  split; [eapply mutex_del_critical_preserves_call_stage; eassumption|].
  split; [|exact Hafter]. intros Hrequest.
  eapply mutex_del_critical_schedule_entry; [exact Hstage|exact Hcritical|exact Hvalid|exact Hrequest].
Qed.

(** The configured counter handlers never write OSLockNesting. Their
    nesting effects can be unbalanced in the broad trace, so no equality
    of intNesting is assumed. The interrupted source is first-level; if
    selection is enabled after return, it was enabled before that IRQ. *)
Lemma mutex_del_restore_clients_lock_frame : forall clients state,
  (mutex_del_restore_clients_state clients state).(IntrState).(lockNesting) =
    state.(IntrState).(lockNesting).
Proof.
  induction clients as [|kind rest IH]; intros state; [reflexivity|].
  cbn [mutex_del_restore_clients_state]; rewrite IH.
  destruct kind; unfold mutex_del_restore_client_state, os_int_enter_state,
    os_int_exit_counter_state; cbn [replace_IntrS IntrState].
  all: unfold interrupt_enter_state, interrupt_exit_state;
    repeat match goal with |- context [if ?test then _ else _] => destruct test end; reflexivity.
Qed.

Lemma mutex_del_restore_irq_control_frame : forall sg state handler saved node publication clients kind,
  mutex_del_restore_irq_input sg state handler saved node publication kind ->
  let final := mutex_del_restore_irq_state state handler saved clients kind in
  final.(SchedState).(curTaskID) = state.(SchedState).(curTaskID) /\
  final.(IntrState).(lockNesting) = state.(IntrState).(lockNesting).
Proof.
  intros sg state handler saved node publication clients kind Hsafe final.
  destruct Hsafe as [Hrunning [Hnesting [Hcurrent [Hnode Hrest]]]].
  pose proof (proj2 (mutex_del_restore_clients_task_sched_eq clients
    (mutex_del_restore_irq_parked state handler saved))) as Hsched.
  pose proof (mutex_del_restore_clients_lock_frame clients
    (mutex_del_restore_irq_parked state handler saved)) as Hlock.
  unfold final, mutex_del_restore_irq_state, os_int_exit_wrapper_restored_state.
  cbn [replace_TskS SchedState IntrState].
  unfold mutex_del_restore_exit_state, os_int_exit_selection_state, os_int_exit_counter_state.
  destruct kind; cbn [replace_IntrS replace_SchedS SchedState IntrState]; split.
  - rewrite Hsched.
    unfold mutex_del_restore_irq_parked, armv7a_irq_live_parked_state,
      armv7a_irq_live_entry_state, armv7a_irq_entry_counter_state, os_sched_save_current_sp.
    rewrite Hrunning; cbn [replace_IntrS SchedState TskState]; rewrite Hnode; reflexivity.
  - unfold interrupt_exit_state.
    repeat match goal with |- context [if ?test then _ else _] => destruct test end;
      cbn [lockNesting]; rewrite Hlock;
      unfold mutex_del_restore_irq_parked, armv7a_irq_live_parked_state,
        armv7a_irq_live_entry_state, armv7a_irq_entry_counter_state, os_sched_save_current_sp;
      rewrite Hrunning; cbn [replace_IntrS IntrState TskState]; rewrite Hnode; reflexivity.
  - change ((mutex_del_restore_clients_state clients
      (mutex_del_restore_irq_parked state handler saved)).(SchedState).(curTaskID) =
        state.(SchedState).(curTaskID)).
    rewrite Hsched.
    unfold mutex_del_restore_irq_parked, armv7a_irq_live_parked_state,
      armv7a_irq_live_entry_state, armv7a_irq_entry_counter_state, os_sched_save_current_sp.
    rewrite Hrunning; cbn [replace_IntrS SchedState TskState]; rewrite Hnode; reflexivity.
  - unfold interrupt_exit_state.
    repeat match goal with |- context [if ?test then _ else _] => destruct test end;
      cbn [lockNesting]; rewrite Hlock;
      unfold mutex_del_restore_irq_parked, armv7a_irq_live_parked_state,
        armv7a_irq_live_entry_state, armv7a_irq_entry_counter_state, os_sched_save_current_sp;
      rewrite Hrunning; cbn [replace_IntrS IntrState TskState]; rewrite Hnode; reflexivity.
Qed.

Lemma mutex_del_restore_irq_preserves_call_stage : forall sg state handler saved node publication clients kind,
  mutex_del_restore_irq_input sg state handler saved node publication kind ->
  mutex_del_call_stage handler.(os_int_exit_interrupted_call) state ->
  mutex_del_call_stage handler.(os_int_exit_interrupted_call)
    (mutex_del_restore_irq_state state handler saved clients kind).
Proof.
  intros sg state handler saved node publication clients kind Hsafe Hstage.
  destruct (mutex_del_restore_irq_tasks_event_eq sg state handler saved node publication clients kind Hsafe)
    as [Htasks Hevents].
  destruct (mutex_del_restore_irq_control_frame sg state handler saved node publication clients kind Hsafe)
    as [Hcurrent Hlock].
  destruct Hsafe as [Hrunning [Hnesting [Hcur [Hnode Hrest]]]].
  unfold mutex_del_call_stage in *.
  destruct handler.(os_int_exit_interrupted_call).(os_sched_call_origin) eqn:Horigin.
  - destruct Hstage as [Hboot _]; congruence.
  - destruct Hstage as [[Hbinding [Hactive Hexec]] Hready]; split.
    + split; [exact Hbinding|]. split.
      * rewrite Htasks; eapply task_set_saved_sp_preserves_invocation_active; eassumption.
      * unfold task_execution_current in *; rewrite Horigin in *; rewrite Hcurrent; exact Hexec.
    + intros Henabled.
      assert (Hentry_enabled : os_sched_selection_enabled state = true).
      { unfold os_sched_selection_enabled in *; apply Bool.andb_true_iff in Henabled.
        rewrite Hnesting, Hlock in *; exact (proj2 Henabled). }
      destruct (Hready Hentry_enabled) as [old [Hold Hrun]].
      assert (old = node) by congruence; subst old.
      exists (task_set_saved_sp node saved.(armv7a_continuation_sp)); split.
      * rewrite Htasks; cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
      * exact Hrun.
Qed.

Lemma mutex_del_same_call_stage : forall original returned state,
  kernel_stack_call_same_call returned original ->
  mutex_del_call_stage original state -> mutex_del_call_stage returned state.
Proof.
  intros original returned state [Hi [Ho Hstack]].
  unfold mutex_del_call_stage; rewrite Ho.
  destruct original.(os_sched_call_origin) eqn:Horigin; [auto|].
  unfold mutex_del_task_call_stage, kernel_call_task_source; rewrite Hi, Ho, Hstack, Horigin; auto.
Qed.

(** Stage transport consumes the SAME actual finite IRQ source and strong
    resource producer already used around Save/Restore. Each ABI-derived
    returned identity is checked against that iteration's saved call.
    No equality of unrelated heap states or future return is assumed. *)
Section CounterIRQStage.
Context (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (port : OsIntExitPlatformResources) (abi : Armv7aContinuationABI external platform port)
  (sg : StableGlobVars) (Local : Type).
Variable local_step : OsIntExitCallContext ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable normal_return : OsIntExitCallContext -> StableGlobVars ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable handler_contract : forall handler,
  RestoreHandlerContract
    (fun (_ : RestoreHandlerCall) (_ : Local) => mutex_del_restore_handler_owner platform port handler)
    (local_step handler) (normal_return handler).
Variable handler_stack : TaskStackRegion.
Variable handler_fragments : TaskStackFragments.

Lemma mutex_del_counter_irqs_stage_resources : forall active mask pc lr call state before returned final after
  (frame : Assertion),
  mutex_del_restore_irqs_execution external platform port abi sg Local local_step normal_return
    handler_stack handler_fragments mask pc lr call state before returned final after ->
  mutex_del_call_stage call state ->
  (kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) before ->
  mutex_del_call_stage returned final /\ kernel_stack_call_same_call returned call /\
  (kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) after.
Proof.
  intros active mask pc lr call state before returned final after frame Hrun.
  induction Hrun; intros Hstage Hpre.
  - split; [exact Hstage|]. split; [repeat split; reflexivity|exact Hpre].
  - destruct (mutex_del_restore_irq_execution_stack_resources external platform port abi sg Local
      local_step normal_return handler_contract handler_stack handler_fragments active _ _ _ _ _ _ _ _ _ _ H Hpre)
      as [Hi [Ho [Hstack Hmiddle]]].
    assert (Hsame : kernel_stack_call_same_call middle_call call) by (repeat split; assumption).
    assert (Hstage_middle : mutex_del_call_stage middle_call middle_state).
    { eapply mutex_del_same_call_stage; [exact Hsame|].
      destruct H as [state handler saved node publication clients kind before saved_heap handler_heap handler_cursor
        returned_cursor returned_heap exit_cursor exit_heap exited_heap irq_after Hsafe Hpc Hmask Hlr Hstack'
        Hfragments Hsave Hentry Hreturn Hcursor Hreturn_pc Htrace Hwrapper Hexit Hreads Hrestore].
      eapply mutex_del_restore_irq_preserves_call_stage; eassumption. }
    destruct (IHHrun Hstage_middle Hmiddle) as [Hfinal [Hsame' Hpost]].
    split; [exact Hfinal|]. split; [|exact Hpost].
    destruct Hsame' as [Hi' [Ho' Hstack']]; repeat split; congruence.
Qed.
End CounterIRQStage.

(** Save's exact acquired-state carrier. The stage belongs to the state
    actually exposed by this Save, alongside the existing owner history
    and physical resources. It cannot be reconstructed from owner history
    alone or retained at the old [before] index across an interrupt. *)
Definition mutex_del_source_save_post environment external platform critical sg original mask saved before
  : Assertion :=
  EX acquired,
    coq_prop (mutex_del_call_stage original acquired /\
      mutex_del_runtime_save_facts sg mask saved before acquired) &&
    (critical_region_masked platform critical sg original.(os_sched_call_invocation)
       original.(os_sched_call_origin) saved acquired ** kernel_program_inv sg acquired **
     mutex_del_runtime_acquired environment external platform sg original acquired).

Lemma mutex_del_source_save_post_from_masked : forall environment critical sg original returned
  mask saved before acquired,
  mutex_del_call_stage original acquired -> mutex_owner_source_history sg before acquired ->
  kernel_stack_call_same_call returned original -> interrupt_saved_value mask saved ->
  kernel_stack_call_masked environment.(mutex_del_call_continuations)
    mutex_del_stack_resources critical sg (task_stack_call_active_key original)
    returned saved acquired acquired |--
  mutex_del_source_save_post environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical sg original mask saved before.
Proof.
  intros environment critical sg original returned mask saved before acquired Hstage Hhistory Hsame Hsaved.
  destruct Hsame as [Hi [Ho Hstack]].
  unfold kernel_stack_call_masked, kernel_stack_inv, mutex_del_stack_resources.
  unfold mutex_del_source_save_post; Exists acquired.
  unfold mutex_del_runtime_acquired, mutex_del_runtime_stack_support; Exists environment returned.
  unfold mutex_del_runtime_save_facts, kernel_stack_call_same_call,
    mutex_del_callsite_environment, kernel_program_inv; rewrite Hi, Ho; entailer!.
Qed.

Lemma mutex_del_source_save_post_forget : forall environment external platform critical sg original mask saved before,
  mutex_del_source_save_post environment external platform critical sg original mask saved before |--
  mutex_del_runtime_save_post environment external platform critical sg original mask saved before.
Proof.
  intros; unfold mutex_del_source_save_post, mutex_del_runtime_save_post; Intros acquired.
  Exists acquired; entailer!.
Qed.

Section SourceCallStage.
Context (environment : MutexDelCallEnvironment) (sg : StableGlobVars) (Local : Type).
Variable local_step : OsIntExitCallContext ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable normal_return : OsIntExitCallContext -> StableGlobVars ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable handler_contract : forall handler,
  RestoreHandlerContract
    (fun (_ : RestoreHandlerCall) (_ : Local) => mutex_del_restore_handler_owner
      environment.(mutex_del_call_platform) environment.(mutex_del_call_port) handler)
    (local_step handler) (normal_return handler).
Variable handler_stack : TaskStackRegion.
Variable handler_fragments : TaskStackFragments.

Lemma mutex_del_source_irq_save_post : forall critical arch
  (suffix : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (registers_source : Armv7aIRQRegisterSave environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  call state registers before returned_registers returned acquired resumed final_registers final_state after
  (frame : Assertion),
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  (mutex_del_source_entry environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) sg call (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) before ->
  mutex_del_irq_registers_execution environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations) registers_source sg Local local_step normal_return
    handler_stack handler_fragments (armv7a_save_entry_address suffix + 4)
    (kernel_save_read_cpsr registers) call state before returned_registers returned acquired resumed ->
  armv7a_save_suffix_transition suffix returned_registers acquired resumed final_registers final_state after ->
  final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
  final_registers.(kernel_save_return_word) = Some registers.(kernel_save_lr) /\
  (mutex_del_source_save_post environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) critical sg call
     (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) final_registers.(kernel_save_r0) state **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) after.
Proof.
  intros critical arch suffix registers_source call state registers before returned_registers returned acquired resumed
    final_registers final_state after frame Hnone Hvalid Hpre Hirqs Hsuffix.
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (mutex_del_call_stage call state) &&
    (kernel_stack_call_closed environment.(mutex_del_call_continuations) mutex_del_stack_resources sg
       (task_stack_call_active_key call) call (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state **
     (task_stack_fragments_rep handler_stack handler_fragments ** frame))) end.
  { unfold mutex_del_source_entry, mutex_del_runtime_entry; Intros selected.
    destruct H0 as [_ Hsame]; subst selected; entailer!. }
  destruct (Hopen before Hpre) as [Hstage Howned].
  destruct (mutex_del_stack_irq_save_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations) registers_source sg Local local_step normal_return
    handler_contract handler_stack handler_fragments critical arch suffix
    (task_stack_call_active_key call) call state registers before returned_registers returned acquired resumed
    final_registers final_state after frame Hnone Hvalid Howned Hirqs Hsuffix)
    as [Hmrs [Hsource [Hstate [Hr0 [Hcpsr [Hlr [Hsame [Hevents Hpost]]]]]]]].
  destruct (mutex_del_irq_registers_execution_refinement environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations) registers_source sg Local local_step normal_return
    handler_stack handler_fragments _ _ _ _ _ _ _ _ _ Hirqs) as [_ [_ [_ Hcounter]]].
  cbn [kernel_save_read_cpsr kernel_save_cpsr] in Hcounter.
  destruct (mutex_del_counter_irqs_stage_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations) sg Local local_step normal_return
    handler_contract handler_stack handler_fragments (task_stack_call_active_key call)
    _ _ _ _ _ _ _ _ _ _ Hcounter Hstage Howned) as [Hstage' [Hsame' Hresumed]].
  assert (Hacquired : mutex_del_call_stage call acquired).
  { eapply mutex_del_same_call_stage; [|exact Hstage'].
    destruct Hsame' as [Hi [Ho Hstack]]; repeat split; congruence. }
  pose proof (mutex_del_counter_irqs_owner_history environment sg Local local_step normal_return
    handler_stack handler_fragments _ _ _ _ _ _ _ _ _ Hcounter) as Hhistory.
  assert (Hsaved : interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr))
    final_registers.(kernel_save_r0)).
  { unfold interrupt_saved_value; rewrite Hr0; auto. }
  split; [exact Hr0|]. split; [exact Hlr|].
  match type of Hpost with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (mutex_del_source_save_post_from_masked environment critical sg call returned
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) final_registers.(kernel_save_r0)
      state acquired Hacquired Hhistory Hsame Hsaved); entailer!. }
  exact (Hclose after Hpost).
Qed.

(** The complete real Restore prefix/IRQ/BX family returns a stage-aware
    owner at the current state. Del's optional scheduler consumes this
    state, so readiness is never reused at the stale critical checkpoint. *)
Lemma mutex_del_source_irq_restore_post : forall critical arch
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  call saved acquired checkpoint restore_entry cursor before written released
  returned final resumed final_cursor after (frame : Assertion),
  mutex_del_call_stage call checkpoint ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (mutex_del_stack_restore_input environment.(mutex_del_call_continuations) critical sg
    (task_stack_call_active_key call) call saved acquired checkpoint **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) before ->
  armv7a_restore_prefix_transition restore cursor before written released ->
  mutex_del_restore_irqs_execution environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations) sg Local local_step normal_return
    handler_stack handler_fragments (armv7a_irq_fiq_mask saved) (restore_entry + 8)
    cursor.(kernel_restore_lr) call checkpoint released returned final resumed ->
  armv7a_restore_suffix_transition restore written resumed final_cursor after ->
  kernel_stack_call_same_call returned call /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (mutex_del_source_entry environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) sg returned (armv7a_irq_fiq_mask saved) final **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) after.
Proof.
  intros critical arch restore call saved acquired checkpoint restore_entry cursor before written released
    returned final resumed final_cursor after frame Hstage Hr0 Hmask Hpre Hprefix Hirqs Hsuffix.
  assert (Hmasked : (kernel_stack_call_masked environment.(mutex_del_call_continuations)
    mutex_del_stack_resources critical sg (task_stack_call_active_key call) call saved acquired checkpoint **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) before).
  { match type of Hpre with ?P before => match goal with |- ?Q before => assert (Hopen : P |-- Q) end end.
    { sep_apply_l_atomic (mutex_del_stack_restore_input_masked _ _ _ environment.(mutex_del_call_continuations)
        critical sg (task_stack_call_active_key call) call saved acquired checkpoint); entailer!. }
    exact (Hopen before Hpre). }
  destruct (kernel_stack_call_restore_prefix _ _ _ _ _ environment.(mutex_del_call_continuations)
    restore mutex_del_stack_resources sg (task_stack_call_active_key call) call saved acquired checkpoint
    cursor before written released _ Hr0 Hmask Hmasked Hprefix) as [Hwritten [Hmemory Hreleased]].
  destruct (mutex_del_counter_irqs_stage_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations) sg Local local_step normal_return
    handler_contract handler_stack handler_fragments (task_stack_call_active_key call)
    _ _ _ _ _ _ _ _ _ _ Hirqs Hstage Hreleased) as [Hfinal [Hsame Hresumed]].
  destruct (mutex_del_stack_repeated_restore_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations) sg Local local_step normal_return
    handler_contract handler_stack handler_fragments critical arch restore
    (task_stack_call_active_key call) call saved acquired checkpoint restore_entry cursor before written released
    returned final resumed final_cursor after frame Hr0 Hmask Hpre Hprefix Hirqs Hsuffix)
    as [Hi [Ho [Hstack [Hword Hafter]]]].
  split; [exact Hsame|]. split; [exact Hword|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold mutex_del_source_entry, mutex_del_runtime_entry; Exists environment.
    unfold mutex_del_callsite_environment, task_stack_call_active_key; rewrite Ho; entailer!. }
  exact (Hclose after Hafter).
Qed.
End SourceCallStage.
