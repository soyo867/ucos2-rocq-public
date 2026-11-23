Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Relations.Relation_Operators.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_wake_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_always_nonswitch_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_irq_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_client_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_delete_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_nontimer_source_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_client_resumption.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_inherit_call_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Completed source cuts use the actual module relation, including the
    error alternatives of critical API calls.  The transfer alternatives
    admit an arbitrary finite foreign source prefix: in particular a
    self-delete intermediate need not have a live current node.  The
    final real destination/install reconstructs current consistency.
    This is a source composition, not an additional platform guarantee. *)
Inductive sched_task_completed_current_source external port sg :
  UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| SchedTaskCompletedCurrentRefl : forall state,
    sched_task_completed_current_source external port sg state state
| SchedTaskCompletedCurrentLocal : forall before middle after,
    sched_current_source_step external sg before middle ->
    sched_task_completed_current_source external port sg middle after ->
    sched_task_completed_current_source external port sg before after
| SchedTaskCompletedCurrentProfile : forall cut before middle after,
    kernel_client_step (kernel_full_profile_cut_client cut) sg before middle ->
    sched_task_completed_current_source external port sg middle after ->
    sched_task_completed_current_source external port sg before after
| SchedTaskCompletedCurrentSuspend : forall priority code before middle after,
    task_suspend_critical sg priority before code middle ->
    sched_task_completed_current_source external port sg middle after ->
    sched_task_completed_current_source external port sg before after
| SchedTaskCompletedCurrentResume : forall priority code before middle after,
    task_resume_critical sg priority before code middle ->
    sched_task_completed_current_source external port sg middle after ->
    sched_task_completed_current_source external port sg before after
| SchedTaskCompletedCurrentFlagReady : forall pointer bits result schedule before middle after,
    flag_task_rdy sg before pointer bits result = Some (schedule, middle) ->
    sched_task_completed_current_source external port sg middle after ->
    sched_task_completed_current_source external port sg before after
| SchedTaskCompletedCurrentEventReady : forall eid kind message result priority before middle after,
    event_task_rdy sg before eid kind message result = Some (priority, middle) ->
    sched_task_completed_current_source external port sg middle after ->
    sched_task_completed_current_source external port sg before after
| SchedTaskCompletedCurrentTick : forall before after,
    sched_task_completed_current_source external port sg (time_tick_serialized_after_hook sg before) after ->
    sched_task_completed_current_source external port sg before after
| SchedTaskCompletedCurrentTaskInstall : forall origin before foreign context outgoing hooked incoming resumed after,
    task_execution_source_trace external port sg origin before foreign hooked ->
    os_sched_saved_stack_binding context outgoing hooked ->
    os_sched_destination_binding external context outgoing hooked incoming resumed ->
    sched_task_completed_current_source external port sg
      (os_sched_install_context context outgoing incoming hooked) after ->
    sched_task_completed_current_source external port sg before after
| SchedTaskCompletedCurrentIRQInstall : forall origin before foreign context entry transfer after,
    task_execution_source_trace external port sg origin before foreign entry ->
    os_int_exit_transfer_source external port sg context entry transfer ->
    sched_task_completed_current_source external port sg (os_int_exit_installed_state transfer) after ->
    sched_task_completed_current_source external port sg before after.

Lemma sched_task_completed_source_preserves_current_consistency : forall external port sg before after,
  sched_task_completed_current_source external port sg before after ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros external port sg before after Hsource; induction Hsource; intro Hconsistent.
  - exact Hconsistent.
  - apply IHHsource; eapply sched_current_source_step_preserves_consistency; eassumption.
  - apply IHHsource; eapply kernel_full_profile_cut_preserves_current_consistency; eassumption.
  - apply IHHsource; eapply task_suspend_critical_preserves_current_consistency; eassumption.
  - apply IHHsource; eapply task_resume_critical_preserves_current_consistency; eassumption.
  - apply IHHsource; eapply flag_task_rdy_preserves_current_consistency; eassumption.
  - apply IHHsource; eapply event_task_rdy_preserves_current_consistency; eassumption.
  - apply IHHsource; apply time_tick_serialized_after_hook_preserves_current_consistency; exact Hconsistent.
  - apply IHHsource; eapply os_sched_destination_installs_current_consistency; eassumption.
  - apply IHHsource; apply (os_int_exit_destination_installs_current_consistency external transfer).
    destruct H0 as [_ [_ [_ [_ [Hdestination _]]]]]; exact Hdestination.
Qed.

(** Running has a separate concrete module projection.  In particular a
    current-cache frame alone is not an OSRunning frame, and an arbitrary
    foreign task-execution trace cannot be used as this source.  The two
    frame alternatives consume the exact scheduler record returned by a
    real module: unchanged, or its ready-list update.  They do not assume
    the control relation being proved. *)
Inductive sched_task_running_source_step external sg :
  UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| SchedTaskRunningFrame : forall action before after,
    kernel_client_step action sg before after -> after.(SchedState) = before.(SchedState) ->
    sched_task_running_source_step external sg before after
| SchedTaskRunningReadyUpdate : forall action before after ready,
    kernel_client_step action sg before after ->
    after.(SchedState) = sched_set_ready before.(SchedState) ready ->
    sched_task_running_source_step external sg before after
| SchedTaskRunningProfile : forall cut before after,
    kernel_client_step (kernel_full_profile_cut_client cut) sg before after ->
    sched_task_running_source_step external sg before after
| SchedTaskRunningSuspend : forall priority code before after,
    task_suspend_critical sg priority before code after ->
    sched_task_running_source_step external sg before after
| SchedTaskRunningResume : forall priority code before after,
    task_resume_critical sg priority before code after ->
    sched_task_running_source_step external sg before after
| SchedTaskRunningChangePrio : forall requested priority code before after,
    task_change_prio_critical sg requested priority before code after ->
    sched_task_running_source_step external sg before after
| SchedTaskRunningMutexRelocate : forall state ceiling owner node priority,
    sched_task_running_source_step external sg state
      (mutex_del_relocated_state sg state ceiling owner node priority)
| SchedTaskRunningMutexInherit : forall before owner node base waiter ceiling after,
    mutex_pend_inherit_step sg before owner node base waiter ceiling after ->
    sched_task_running_source_step external sg before after
| SchedTaskRunningFlagReady : forall before pointer bits result schedule after,
    flag_task_rdy sg before pointer bits result = Some (schedule, after) ->
    sched_task_running_source_step external sg before after
| SchedTaskRunningEventReady : forall before eid kind message result priority after,
    event_task_rdy sg before eid kind message result = Some (priority, after) ->
    sched_task_running_source_step external sg before after
| SchedTaskRunningTick : forall before,
    sched_task_running_source_step external sg before (time_tick_serialized_after_hook sg before)
| SchedTaskRunningTickTask : forall before slot old,
    sched_task_running_source_step external sg before (tick_task_step sg slot old before)
| SchedTaskRunningLifecycle : forall action before after,
    kernel_client_step (task_creation_client action) sg before after ->
    sched_task_running_source_step external sg before after
| SchedTaskRunningNontimer : forall action before after,
    kernel_nontimer_source_client action -> kernel_client_step action sg before after ->
    sched_task_running_source_step external sg before after
| SchedTaskRunningDeletePrepare : forall before tid node after loan,
    task_delete_prepare_single_wait before tid node = Some (after, loan) ->
    sched_task_running_source_step external sg before after
| SchedTaskRunningDeleteEvent : forall before tid node after updated,
    task_delete_event_unlinked before tid node after updated ->
    sched_task_running_source_step external sg before after
| SchedTaskRunningDeleteFlag : forall before tid node after updated loan,
    task_delete_flag_unlinked before tid node after updated loan ->
    sched_task_running_source_step external sg before after
| SchedTaskRunningDeletePrepared : forall before tid node,
    sched_task_running_source_step external sg before (task_delete_prepare_state before tid node)
| SchedTaskRunningDeleteLocked : forall prepared,
    sched_task_running_source_step external sg prepared (task_delete_locked prepared)
| SchedTaskRunningDeleteReleased : forall prepared resumed,
    sched_task_running_source_step external sg resumed (task_delete_released prepared resumed)
| SchedTaskRunningDeleteRecycled : forall tid priority node name resumed added,
    sched_task_running_source_step external sg resumed (task_delete_recycled sg tid priority node name resumed added)
| SchedTaskRunningDeleteCut : forall prepared resumed tid priority node name,
    sched_task_running_source_step external sg resumed (task_delete_cut sg prepared resumed tid priority node name)
| SchedTaskRunningPrefix : forall before,
    sched_task_running_source_step external sg before (os_sched_prefix_state before)
| SchedTaskRunningIRQCheckpoint : forall observed before,
    sched_task_running_source_step external sg before (os_int_exit_ready_checkpoint observed before)
| SchedTaskRunningTaskInstall : forall context outgoing hooked incoming resumed,
    os_sched_destination_binding external context outgoing hooked incoming resumed ->
    sched_task_running_source_step external sg hooked
      (os_sched_install_context context outgoing incoming hooked)
| SchedTaskRunningIRQInstall : forall transfer,
    os_int_exit_destination_binding external transfer ->
    sched_task_running_source_step external sg transfer.(os_int_exit_hooked_state)
      (os_int_exit_installed_state transfer)
| SchedTaskRunningTake : forall state incoming,
    sched_task_running_source_step external sg state (os_int_exit_wrapper_restored_state state incoming)
| SchedTaskRunningSaveSP : forall state slot sp,
    sched_task_running_source_step external sg state (os_sched_save_current_sp state slot sp).

Lemma task_change_prio_critical_running_eq : forall sg requested priority before code after,
  task_change_prio_critical sg requested priority before code after ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros sg requested priority before code after Hstep.
  unfold task_change_prio_critical in Hstep; cbn beta in Hstep.
  destruct (before.(TskState).(prioTbl) priority) eqn:Hnew in Hstep.
  - destruct Hstep as [selected [Hselected Hstep]].
    unfold task_change_prio_selected_effect in Hstep; cbn beta in Hstep.
    lazymatch type of Hstep with
    | (if ?guard then _ else _) => destruct guard eqn:Hidle in Hstep
    end.
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct (before.(TskState).(prioTbl) selected) eqn:Hselected_slot in Hstep.
      * destruct Hstep as [_ ->]; reflexivity.
      * destruct Hstep as [_ ->]; reflexivity.
      * destruct Hstep as [node [Hnode [_ ->]]].
        unfold task_change_priority_state, task_change_priority_ready.
        lazymatch goal with
        | |- context [if ?ready then _ else _] => destruct ready; reflexivity
        end.
  - destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [_ ->]; reflexivity.
Qed.

Lemma sched_task_running_source_step_running_eq : forall external sg before after,
  sched_task_running_source_step external sg before after ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros external sg before after Hsource; destruct Hsource.
  - rewrite H0; reflexivity.
  - rewrite H0; reflexivity.
  - eapply kernel_full_profile_cut_running_eq; eassumption.
  - eapply task_suspend_critical_running_eq; eassumption.
  - eapply task_resume_critical_running_eq; eassumption.
  - eapply task_change_prio_critical_running_eq; eassumption.
  - reflexivity.
  - exact (proj2 (proj2 (proj2 (mutex_pend_inherit_call_fields_eq _ _ _ _ _ _ _ _ H)))).
  - eapply flag_task_rdy_running_eq; eassumption.
  - eapply event_task_rdy_running_eq; eassumption.
  - apply time_tick_serialized_after_hook_running_eq.
  - apply tick_task_step_running_eq.
  - eapply task_creation_client_running_eq; eassumption.
  - eapply kernel_nontimer_source_client_running_eq; eassumption.
  - eapply task_delete_prepare_single_wait_running_eq; eassumption.
  - rewrite (task_delete_event_unlinked_sched_eq _ _ _ _ _ H); reflexivity.
  - rewrite (task_delete_flag_unlinked_sched_eq _ _ _ _ _ _ H); reflexivity.
  - rewrite task_delete_prepare_state_sched_eq; reflexivity.
  - rewrite task_delete_locked_sched_eq; reflexivity.
  - rewrite task_delete_released_sched_eq; reflexivity.
  - rewrite task_delete_recycled_sched_eq; reflexivity.
  - rewrite task_delete_cut_sched_eq; reflexivity.
  - exact (proj2 (proj2 (proj2 (os_sched_ready_checkpoint_frame before)))).
  - exact (proj2 (proj2 (os_int_exit_checkpoint_current_frame observed before))).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold os_sched_save_current_sp; destruct (state.(TskState).(inUsedTaskStates) slot); reflexivity.
Qed.

Inductive sched_task_running_source external sg : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| SchedTaskRunningRefl : forall state, sched_task_running_source external sg state state
| SchedTaskRunningNext : forall before current after,
    sched_task_running_source_step external sg before current ->
    sched_task_running_source external sg current after ->
    sched_task_running_source external sg before after.

Lemma sched_task_running_source_running_eq : forall external sg before after,
  sched_task_running_source external sg before after ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros external sg before after Hsource; induction Hsource; [reflexivity|].
  rewrite IHHsource; eapply sched_task_running_source_step_running_eq; exact H.
Qed.

(** These actions name the critical effects used by the checked C
    modules.  In particular the priority action uses the actual API's
    conditional current-cache update, not the older semaphore-local
    priority transformer.  Return codes remain existential observations
    of the same module effect. *)
Definition task_change_prio_critical_client (actor : option nat) requested priority : KernelClientAction :=
  {| kernel_client_actor := actor; kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       exists code, task_change_prio_critical sg requested priority before code after |}.

Definition flag_task_rdy_source_client (actor : option nat) pointer bits result : KernelClientAction :=
  {| kernel_client_actor := actor; kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       exists schedule, flag_task_rdy sg before pointer bits result = Some (schedule, after) |}.

Definition event_task_rdy_source_client (actor : option nat) eid kind message result : KernelClientAction :=
  {| kernel_client_actor := actor; kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       exists priority, event_task_rdy sg before eid kind message result = Some (priority, after) |}.

Definition time_tick_task_source_client slot old : KernelClientAction :=
  {| kernel_client_actor := None; kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       before.(TskState).(inUsedTaskStates) slot = Some old /\ after = tick_task_step sg slot old before |}.

(** Registration identifies named real module effects.  No constructor
    admits an arbitrary action merely because its endpoint happens to
    satisfy current consistency or a control rely.  Phase-local Delete
    and Mutex cuts remain in their finite stage sources above; they are
    not required to pretend that every intermediate state is a closed
    UCOS2 invariant. *)
Inductive sched_task_source_client external : KernelClientAction -> Prop :=
| SchedTaskSourceNontimer : forall action,
    kernel_nontimer_source_client action -> sched_task_source_client external action
| SchedTaskSourceProfile : forall cut,
    sched_task_source_client external (kernel_full_profile_cut_client cut)
| SchedTaskSourceChangePrio : forall actor requested priority,
    sched_task_source_client external (task_change_prio_critical_client actor requested priority)
| SchedTaskSourceFlagReady : forall actor pointer bits result,
    sched_task_source_client external (flag_task_rdy_source_client actor pointer bits result)
| SchedTaskSourceEventReady : forall actor eid kind message result,
    sched_task_source_client external (event_task_rdy_source_client actor eid kind message result)
| SchedTaskSourceTickTask : forall slot old,
    sched_task_source_client external (time_tick_task_source_client slot old)
| SchedTaskSourceTaskInstall : forall context outgoing incoming resumed,
    sched_task_source_client external (os_sched_install_client external context outgoing incoming resumed).

Lemma sched_task_source_client_running_step : forall external action sg before after,
  sched_task_source_client external action -> kernel_client_step action sg before after ->
  sched_task_running_source_step external sg before after.
Proof.
  intros external action sg before after Hsource; destruct Hsource; intro Hstep.
  - eapply SchedTaskRunningNontimer; eassumption.
  - eapply SchedTaskRunningProfile; exact Hstep.
  - destruct Hstep as [code Hstep]; eapply SchedTaskRunningChangePrio; exact Hstep.
  - destruct Hstep as [schedule Hstep]; eapply SchedTaskRunningFlagReady; exact Hstep.
  - destruct Hstep as [priority Hstep]; eapply SchedTaskRunningEventReady; exact Hstep.
  - destruct Hstep as [Hnode ->]; apply SchedTaskRunningTickTask.
  - destruct Hstep as [Hsaved [Hdestination [Hhigh ->]]]; eapply SchedTaskRunningTaskInstall; exact Hdestination.
Qed.

(** Resource and name obligations are the existing module certification
    boundary.  They do not assert any new current/control property: that
    consequence is proved above from the named source operation. *)
Definition sched_task_registered_client external (action : KernelClientAction) : Prop :=
  sched_task_source_client external action /\ KernelClientCertificate action /\
  (forall sg before after, kernel_client_step action sg before after ->
    before.(NameState) = after.(NameState)) /\
  kernel_client_preserves_resources kernel_sched_ready_inv action.

(** A fresh static family over the existing physical region handles.
    It is not a filtering/transport of an arbitrary earlier registration
    or of an earlier trace.  Actual module dispatch must produce membership
    in this family on each closed source edge. *)
Definition sched_task_source_region (external : OsSchedExternalResources)
  (resources : CriticalRegionResources) : CriticalRegionResources.
Proof.
  refine {| critical_region_outside_without_running := resources.(critical_region_outside_without_running);
            critical_region_outside_without_running_rep := resources.(critical_region_outside_without_running_rep);
            critical_region_inside := resources.(critical_region_inside);
            critical_region_clients := sched_task_registered_client external |}.
  - intros action [_ [Hcertificate _]]; exact Hcertificate.
  - intros action [_ [_ [Hname _]]]; exact Hname.
Defined.

Lemma sched_task_source_region_ready_clients : forall external resources,
  kernel_sched_ready_clients (sched_task_source_region external resources).
Proof. intros external resources action [_ [_ [_ Hready]]]; exact Hready. Qed.

Lemma sched_task_source_region_trace_running_source : forall external resources sg observer before stopped after,
  kernel_client_trace (sched_task_source_region external resources).(critical_region_clients)
    sg observer before stopped after ->
  sched_task_running_source external sg before after.
Proof.
  intros external resources sg observer before stopped after Htrace.
  induction Htrace as [state|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH].
  - constructor.
  - eapply SchedTaskRunningNext; [|exact IH].
    eapply sched_task_source_client_running_step; [exact (proj1 Hin)|exact Hstep].
Qed.

Lemma task_change_prio_critical_client_step : forall actor sg requested priority before code after,
  task_change_prio_critical sg requested priority before code after ->
  kernel_client_step (task_change_prio_critical_client actor requested priority) sg before after.
Proof. intros; exists code; exact H. Qed.

Lemma flag_task_rdy_client_step : forall actor sg before pointer bits result schedule after,
  flag_task_rdy sg before pointer bits result = Some (schedule, after) ->
  kernel_client_step (flag_task_rdy_source_client actor pointer bits result) sg before after.
Proof. intros; exists schedule; exact H. Qed.

Lemma event_task_rdy_client_step : forall actor sg before eid kind message result priority after,
  event_task_rdy sg before eid kind message result = Some (priority, after) ->
  kernel_client_step (event_task_rdy_source_client actor eid kind message result) sg before after.
Proof. intros; exists priority; exact H. Qed.


(** Named source steps, unlike an arbitrary region membership, provide
    current-cache preservation.  The existing invariant premise is needed
    only for publication's private/live disjointness. *)
Lemma sched_task_source_client_preserves_current_consistency :
  forall external action sg before after,
  UCOS2_state_inv sg before ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_task_source_client external action -> kernel_client_step action sg before after ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros external action sg before after Hvalid Hcurrent Hsource; destruct Hsource; intro Hstep.
  - eapply kernel_nontimer_source_client_preserves_current_consistency; eassumption.
  - eapply kernel_full_profile_cut_preserves_current_consistency; eassumption.
  - destruct Hstep as [code Hstep]; eapply task_change_prio_critical_preserves_current_consistency; eassumption.
  - destruct Hstep as [schedule Hstep]; eapply flag_task_rdy_preserves_current_consistency; eassumption.
  - destruct Hstep as [priority Hstep]; eapply event_task_rdy_preserves_current_consistency; eassumption.
  - destruct Hstep as [Hnode ->]; eapply tick_task_step_preserves_current_consistency; eassumption.
  - destruct Hstep as [Hsaved [Hdestination [Hhigh ->]]].
    eapply os_sched_destination_installs_current_consistency; eassumption.
Qed.

Lemma sched_task_source_region_trace_preserves_current_consistency :
  forall external resources sg observer before stopped after,
  kernel_client_trace (sched_task_source_region external resources).(critical_region_clients)
    sg observer before stopped after ->
  UCOS2_state_inv sg before ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros external resources sg observer before stopped after Htrace.
  induction Htrace as [state|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intros Hvalid Hcurrent.
  - exact Hcurrent.
  - apply IH.
    + eapply kernel_client_preserves_validity; [exact (proj1 (proj2 Hin))|exact Hvalid|exact Hstep].
    + eapply sched_task_source_client_preserves_current_consistency;
        [exact Hvalid|exact Hcurrent|exact (proj1 Hin)|exact Hstep].
Qed.

(** This is a proof combinator for the existing four registration
    obligations.  It adds no source guard: each use below names a real
    module and discharges its certificate, name frame and ready effect. *)
Lemma sched_task_register_named_source : forall external action,
  sched_task_source_client external action -> KernelClientCertificate action ->
  (forall sg before after, kernel_client_step action sg before after ->
    before.(NameState) = after.(NameState)) ->
  (forall sg before after, UCOS2_state_inv sg before ->
    kernel_client_step action sg before after ->
    before.(SchedState).(readyList) <> [] -> after.(SchedState).(readyList) <> []) ->
  sched_task_registered_client external action.
Proof.
  intros external action Hsource Hcert Hname Hready.
  split; [exact Hsource|]. split; [exact Hcert|]. split; [exact Hname|].
  intros sg before after [Hvalid Hnonempty] Hstep.
  destruct (kernel_client_certificate_preserves_selected_resources action Hcert
    sg before after Hvalid Hstep) as [Hafter Hresources].
  split.
  - split; [exact Hafter|exact (Hready sg before after Hvalid Hstep Hnonempty)].
  - exact Hresources.
Qed.

Lemma sched_task_install_client_registered : forall external context outgoing incoming resumed,
  sched_task_registered_client external
    (os_sched_install_client external context outgoing incoming resumed).
Proof.
  intros; apply sched_task_register_named_source.
  - apply SchedTaskSourceTaskInstall.
  - apply os_sched_install_client_certificate.
  - intros sg before after [_ [_ [_ ->]]]; reflexivity.
  - intros sg before after Hvalid [_ [_ [_ ->]]] Hready; exact Hready.
Qed.

Lemma sched_task_stack_publication_registered : forall external publication,
  sched_task_registered_client external (task_create_stack_publication_client publication).
Proof.
  intros external publication; split; [apply SchedTaskSourceNontimer; constructor|].
  split; [apply task_create_stack_publication_certificate|].
  split.
  - intros sg before after Hstep; exact (task_create_stack_publication_name_frame sg publication before after Hstep).
  - apply task_create_stack_publication_preserves_sched_ready.
Qed.

Lemma sched_task_begin_client_registered : forall external origin,
  sched_task_registered_client external (task_create_begin_client origin).
Proof.
  intros; apply sched_task_register_named_source.
  - apply SchedTaskSourceNontimer; constructor.
  - apply task_create_begin_client_certificate.
  - intros sg before after [_ ->]; reflexivity.
  - intros sg before after Hvalid [_ ->] Hready; exact Hready.
Qed.

Lemma sched_task_reserve_client_registered : forall external priority invocation origin,
  sched_task_registered_client external (task_create_reserve_client priority invocation origin).
Proof.
  intros; apply sched_task_register_named_source.
  - apply SchedTaskSourceNontimer; constructor.
  - apply task_create_reserve_client_certificate.
  - intros sg before after [_ ->]; reflexivity.
  - intros sg before after Hvalid [_ ->] Hready; exact Hready.
Qed.

Lemma sched_task_rollback_client_registered : forall external priority invocation,
  sched_task_registered_client external (task_create_rollback_client priority invocation).
Proof.
  intros; apply sched_task_register_named_source.
  - apply SchedTaskSourceNontimer; constructor.
  - apply task_create_rollback_client_certificate.
  - intros sg before after [_ ->]; reflexivity.
  - intros sg before after Hvalid [_ ->] Hready; exact Hready.
Qed.

Lemma sched_task_event_allocate_registered : forall external actor invocation,
  sched_task_registered_client external (event_create_allocate_client actor invocation).
Proof.
  intros; apply sched_task_register_named_source.
  - apply SchedTaskSourceNontimer; constructor.
  - apply event_create_allocate_client_certificate.
  - intros sg before after [_ [result Hstep]]; unfold event_create_allocate_critical in Hstep.
    destruct before.(EventState).(unUsedEventStates);
      [destruct Hstep as [_ ->]|destruct Hstep as [image [_ [_ ->]]]]; reflexivity.
  - intros sg before after Hvalid [_ [result Hstep]] Hready; unfold event_create_allocate_critical in Hstep.
    destruct before.(EventState).(unUsedEventStates);
      [destruct Hstep as [_ ->]|destruct Hstep as [image [_ [_ ->]]]]; exact Hready.
Qed.

Lemma sched_task_event_private_store_registered : forall external actor eid allocation field value,
  sched_task_registered_client external (event_create_private_store_client actor eid allocation field value).
Proof.
  intros; apply sched_task_register_named_source.
  - apply SchedTaskSourceNontimer; constructor.
  - apply event_create_private_store_client_certificate.
  - intros sg before after [_ ->]; reflexivity.
  - intros sg before after Hvalid [_ ->] Hready; exact Hready.
Qed.

Lemma sched_task_event_publication_registered : forall external actor eid allocation node,
  node.(eventGeneration) = allocation.(eventPrivateGeneration) ->
  node.(eventType) <> OS_EVENT_TYPE_MUTEX -> node.(queueFields) = None -> node.(waitList) = [] ->
  event_fields_consistency node -> (forall sg, event_payload_consistency sg node) ->
  allocation.(eventPrivateMutexPCP) = None ->
  sched_task_registered_client external (event_create_publication_client actor eid allocation node).
Proof.
  intros; apply sched_task_register_named_source.
  - apply SchedTaskSourceNontimer; constructor.
  - apply event_create_publication_client_certificate; assumption.
  - intros sg before after [_ [_ ->]]; reflexivity.
  - intros sg before after Hvalid [_ [_ ->]] Hready; exact Hready.
Qed.

Lemma sched_task_queue_reserve_registered : forall external actor eid allocation free,
  allocation.(eventPrivateMutexPCP) = None ->
  sched_task_registered_client external (q_create_reserve_client actor eid allocation free).
Proof.
  intros; apply sched_task_register_named_source.
  - apply SchedTaskSourceNontimer; constructor.
  - apply q_create_reserve_client_certificate; assumption.
  - intros sg before after [_ [_ [_ [_ [result [a [Ha Hstep]]]]]]].
    destruct free; destruct Hstep as [_ ->]; reflexivity.
  - intros sg before after Hvalid [_ [_ [_ [_ [result [a [Ha Hstep]]]]]]] Hready.
    destruct free; destruct Hstep as [_ ->]; exact Hready.
Qed.

Lemma sched_task_queue_publication_registered : forall external actor eid allocation qid start size slots name,
  0 < start -> 0 <= size <= 65535 ->
  sched_task_registered_client external
    (q_create_publication_client actor eid allocation qid start size slots name).
Proof.
  intros; apply sched_task_register_named_source.
  - apply SchedTaskSourceNontimer; constructor.
  - apply q_create_publication_client_certificate; assumption.
  - intros sg before after [_ [_ [_ [_ ->]]]]; reflexivity.
  - intros sg before after Hvalid [_ [_ [_ [_ ->]]]] Hready; exact Hready.
Qed.

Lemma sched_task_sem_accept_registered : forall external invocation eid count,
  sched_task_registered_client external (sem_accept_critical_client invocation eid count).
Proof.
  intros; apply sched_task_register_named_source.
  - apply SchedTaskSourceNontimer; constructor.
  - apply sem_accept_critical_client_certificate.
  - intros sg before after [e [_ [_ [node [fields [_ [_ [_ ->]]]]]]]].
    lazymatch goal with |- context [if ?positive then _ else _] => destruct positive end;
      reflexivity.
  - intros sg before after Hvalid [e [_ [_ [node [fields [_ [_ [_ ->]]]]]]]] Hready.
    lazymatch goal with |- context [if ?positive then _ else _] => destruct positive end;
      exact Hready.
Qed.

Lemma sched_task_int_enter_registered : forall external,
  sched_task_registered_client external (kernel_full_profile_cut_client KernelFullIntEnter).
Proof.
  intros; split; [apply SchedTaskSourceProfile|]. split.
  - constructor; intros; destruct H0 as [_ ->]; try reflexivity; assumption.
  - split; [intros sg before after [_ ->]; reflexivity|apply kernel_int_enter_preserves_sched_ready].
Qed.

Lemma sched_task_int_exit_counter_registered : forall external running,
  sched_task_registered_client external (kernel_full_profile_cut_client (KernelFullIntExitCounter running)).
Proof.
  intros; split; [apply SchedTaskSourceProfile|]. split.
  - constructor; intros; destruct H0 as [_ ->]; try reflexivity; assumption.
  - split; [intros sg before after [_ ->]; reflexivity|apply kernel_int_exit_counter_preserves_sched_ready].
Qed.

(** Phase effects are the actual source operations.  In particular neither
    Delete's prepared window nor Mutex's released-ceiling window requires
    the closed UCOS2 invariant.  This source syntax itself supplies no heap:
    the paired C-stage resource producers below must supply that ownership. *)
Inductive sched_task_phase_step external sg :
  UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| SchedTaskPhaseClosed : forall action before after,
    sched_task_registered_client external action ->
    kernel_client_step action sg before after ->
    sched_task_phase_step external sg before after
| SchedTaskPhaseDeletePrepare : forall before tid node prepared loan,
    task_delete_prepare_single_wait before tid node = Some (prepared, loan) ->
    sched_task_phase_step external sg before prepared
| SchedTaskPhaseDeleteLock : forall prepared,
    sched_task_phase_step external sg prepared (task_delete_locked prepared)
| SchedTaskPhaseDeleteWindow : forall before after,
    task_delete_window_kernel_step sg before after ->
    sched_task_phase_step external sg before after
| SchedTaskPhaseDeleteCut : forall prepared resumed tid priority node name,
    sched_task_phase_step external sg resumed
      (task_delete_cut sg prepared resumed tid priority node name)
| SchedTaskPhaseMutexPrepare : forall mutex before after,
    mutex_del_prepare sg mutex before after ->
    sched_task_phase_step external sg before after
| SchedTaskPhaseMutexWake : forall before eid priority after,
    event_task_rdy sg before eid PendMutex 0 PendAbort = Some (priority, after) ->
    sched_task_phase_step external sg before after
| SchedTaskPhaseMutexRecycle : forall eid state event,
    sched_task_phase_step external sg state (mutex_del_recycle_state sg eid event state)
| SchedTaskPhaseMutexInherit : forall before owner node base waiter ceiling after,
    mutex_pend_inherit_step sg before owner node base waiter ceiling after ->
    sched_task_phase_step external sg before after.

Inductive sched_task_phase_source external sg :
  UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| SchedTaskPhaseSourceRefl : forall state,
    sched_task_phase_source external sg state state
| SchedTaskPhaseSourceNext : forall before middle after,
    sched_task_phase_step external sg before middle ->
    sched_task_phase_source external sg middle after ->
    sched_task_phase_source external sg before after.

Lemma sched_task_phase_source_trans : forall external sg before middle after,
  sched_task_phase_source external sg before middle ->
  sched_task_phase_source external sg middle after ->
  sched_task_phase_source external sg before after.
Proof.
  intros external sg before middle after Hprefix Hsuffix; induction Hprefix.
  - exact Hsuffix.
  - eapply SchedTaskPhaseSourceNext; [exact H|apply IHHprefix; exact Hsuffix].
Qed.

Lemma sched_task_mutex_wake_prefix_phase_source : forall external sg eid before priorities after,
  mutex_del_wake_prefix sg eid before priorities after ->
  sched_task_phase_source external sg before after.
Proof.
  intros external sg eid before priorities after Hprefix; induction Hprefix.
  - constructor.
  - eapply SchedTaskPhaseSourceNext;
      [eapply SchedTaskPhaseMutexWake; exact H1|exact IHHprefix].
Qed.

Lemma sched_task_mutex_broadcast_phase_source : forall external sg eid before priorities after,
  event_broadcast sg eid PendMutex 0 PendAbort before priorities after ->
  sched_task_phase_source external sg before after.
Proof.
  intros external sg eid before priorities after Hbroadcast; induction Hbroadcast.
  - constructor.
  - eapply SchedTaskPhaseSourceNext;
      [eapply SchedTaskPhaseMutexWake; exact H1|exact IHHbroadcast].
Qed.

(** The actual critical API relation retains no-wait, waiting-error,
    forced-broadcast and invalid-option outcomes.  Its existing source
    decomposition constructs the phase chain; no closed invariant is
    presumed at the prepared or drained state. *)
Lemma sched_task_mutex_del_critical_phase_source : forall external sg eid option before result after,
  mutex_del_critical sg eid option before result after ->
  sched_task_phase_source external sg before after.
Proof.
  intros external sg eid option before result after
    [event [mutex [Hlookup [Htype [Hfields Hcritical]]]]].
  lazymatch type of Hcritical with
  | (if ?zero then _ else _) => destruct zero in Hcritical
  end.
  - lazymatch type of Hcritical with
    | (if ?empty then _ else _) => destruct empty in Hcritical
    end.
    + destruct Hcritical as [prepared [Hprepare [-> Hresult]]].
      eapply SchedTaskPhaseSourceNext; [eapply SchedTaskPhaseMutexPrepare; exact Hprepare|].
      eapply SchedTaskPhaseSourceNext; [apply SchedTaskPhaseMutexRecycle|constructor].
    + destruct Hcritical as [-> Hresult]; constructor.
  - lazymatch type of Hcritical with
    | (if ?force then _ else _) => destruct force in Hcritical
    end.
    + destruct Hcritical as [prepared [priorities [drained [Hprepare [Hbroadcast [-> Hresult]]]]]].
      eapply SchedTaskPhaseSourceNext; [eapply SchedTaskPhaseMutexPrepare; exact Hprepare|].
      eapply sched_task_phase_source_trans;
        [eapply sched_task_mutex_broadcast_phase_source; exact Hbroadcast|].
      eapply SchedTaskPhaseSourceNext; [apply SchedTaskPhaseMutexRecycle|constructor].
    + destruct Hcritical as [-> Hresult]; constructor.
Qed.

Lemma task_delete_window_kernel_step_running_eq : forall sg before after,
  task_delete_window_kernel_step sg before after ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros sg before after Hstep; destruct Hstep.
  - apply tick_task_step_running_eq.
  - apply sched_wake_by_status_running_eq.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma mutex_del_prepare_running_eq : forall sg mutex before after,
  mutex_del_prepare sg mutex before after ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros sg mutex before after Hprepare; unfold mutex_del_prepare in Hprepare.
  lazymatch type of Hprepare with
  | (if ?disabled then _ else _) => destruct disabled in Hprepare
  end.
  - subst after; reflexivity.
  - destruct mutex.(mfOwner) as [owner|].
    + destruct Hprepare as [node [priority [_ [_ ->]]]].
      unfold mutex_del_owner_priority_state.
      lazymatch goal with |- context [if ?same then _ else _] => destruct same end; reflexivity.
    + subst after; reflexivity.
Qed.

Lemma sched_task_phase_step_running_eq : forall external sg before after,
  sched_task_phase_step external sg before after ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros external sg before after Hstep; destruct Hstep.
  - eapply sched_task_running_source_step_running_eq.
    eapply sched_task_source_client_running_step; [exact (proj1 H)|exact H0].
  - eapply task_delete_prepare_single_wait_running_eq; exact H.
  - rewrite task_delete_locked_sched_eq; reflexivity.
  - eapply task_delete_window_kernel_step_running_eq; exact H.
  - rewrite task_delete_cut_sched_eq; reflexivity.
  - eapply mutex_del_prepare_running_eq; exact H.
  - eapply event_task_rdy_running_eq; exact H.
  - reflexivity.
  - exact (proj2 (proj2 (proj2 (mutex_pend_inherit_call_fields_eq _ _ _ _ _ _ _ _ H)))).
Qed.

Lemma sched_task_phase_source_running_eq : forall external sg before after,
  sched_task_phase_source external sg before after ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros external sg before after Hsource; induction Hsource; [reflexivity|].
  rewrite IHHsource; eapply sched_task_phase_step_running_eq; exact H.
Qed.

Lemma sched_task_delete_window_phase_source : forall external sg before after,
  clos_refl_trans_1n _ (task_delete_window_kernel_step sg) before after ->
  sched_task_phase_source external sg before after.
Proof.
  intros external sg before after Hwindow; induction Hwindow.
  - constructor.
  - eapply SchedTaskPhaseSourceNext; [apply SchedTaskPhaseDeleteWindow; exact H|exact IHHwindow].
Qed.

Lemma sched_task_delete_prepare_window_cut_phase_source : forall external sg
  acquired tid node prepared loan resumed priority name,
  task_delete_prepare_single_wait acquired tid node = Some (prepared, loan) ->
  clos_refl_trans_1n _ (task_delete_window_kernel_step sg) (task_delete_locked prepared) resumed ->
  sched_task_phase_source external sg acquired (task_delete_cut sg prepared resumed tid priority node name).
Proof.
  intros external sg acquired tid node prepared loan resumed priority name Hprepare Hwindow.
  eapply SchedTaskPhaseSourceNext; [eapply SchedTaskPhaseDeletePrepare; exact Hprepare|].
  eapply SchedTaskPhaseSourceNext; [apply SchedTaskPhaseDeleteLock|].
  eapply sched_task_phase_source_trans; [apply sched_task_delete_window_phase_source; exact Hwindow|].
  eapply SchedTaskPhaseSourceNext; [apply SchedTaskPhaseDeleteCut|constructor].
Qed.
Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual completed interval keeps its own returned call, state and
    two heaps. Preparation history is an observation of the earlier C cut;
    it does not manufacture the interval or the earlier own-store execution. *)
Lemma task_delete_actual_prepared_environment_window :
  forall environment critical saved_local requested sg completed
    original initial first acquired priority tid node prepared loan
    returned resumed mask initial_heap final_heap frame,
  task_delete_c_environment environment critical saved_local requested sg completed ->
  task_delete_preparation_history sg requested original initial first acquired
    priority tid node prepared loan ->
  completed.(task_delete_environment_execution)
    (TaskDeletePrepared tid node.(taskGeneration))
    first (task_delete_locked prepared) returned resumed initial_heap final_heap ->
  (task_delete_call_closed environment saved_local
    (TaskDeletePrepared tid node.(taskGeneration)) loan
    sg first mask (task_delete_locked prepared) ** frame) initial_heap ->
  task_delete_restore_history environment critical requested
    (TaskDeletePrepared tid node.(taskGeneration)) sg
    first (task_delete_locked prepared) returned resumed /\
  task_delete_window_history sg requested original initial first acquired
    priority tid node prepared loan returned resumed /\
  (task_delete_call_closed environment saved_local
    (TaskDeletePrepared tid node.(taskGeneration)) loan
    sg returned mask resumed ** frame) final_heap.
Proof.
  intros environment critical saved_local requested sg completed
    original initial first acquired priority tid node prepared loan
    returned resumed mask initial_heap final_heap frame Henv Hprep Hactual Hpre.
  destruct (task_delete_actual_environment_return environment critical saved_local
    requested sg completed (TaskDeletePrepared tid node.(taskGeneration)) loan
    first (task_delete_locked prepared) returned resumed mask initial_heap final_heap
    frame Henv Hactual Hpre) as [Htrace [Hnormal [Hrely [Htransport Hclosed]]]].
  split.
  - unfold task_delete_restore_history; tauto.
  - split; [|exact Hclosed].
    unfold task_delete_window_history; split; [exact Hprep|].
    pose proof Hprep as [Hlive [Hprepare Hrunning]].
    destruct Hlive as [Hlookup _].
    destruct Hlookup as [_ [_ [Hfirst _]]].
    split.
    + destruct (proj1 Hnormal) as [Hi [Ho Hs]], Hfirst as [Hi' [Ho' Hs']].
      unfold task_tcb_init_stack_same_call; repeat split; congruence.
    + split; [exact Hrely|exact (proj1 Htransport Hrunning)].
Qed.

(** The existing restore boundary's resource derivation, retaining the
    explicitly supplied returned/current indices instead of folding them
    immediately into the existential restore_post. *)
Lemma task_delete_restore_completed_call_resources :
  forall environment critical saved_local requested sg completed arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    phase loan original saved acquired released cursor initial_heap written prefix_heap
    returned current environment_heap final_cursor final_heap frame,
  task_delete_c_environment environment critical saved_local requested sg completed ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (task_delete_call_masked environment critical saved_local phase loan
    sg original saved acquired released ** frame) initial_heap ->
  armv7a_restore_prefix_transition restore cursor initial_heap written prefix_heap ->
  completed.(task_delete_environment_execution)
    phase original released returned current prefix_heap environment_heap ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor final_heap ->
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  task_delete_restore_history environment critical requested phase sg
    original released returned current /\
  (task_delete_call_closed environment saved_local phase loan
    sg returned (armv7a_irq_fiq_mask saved) current ** frame) final_heap.
Proof.
  intros environment critical saved_local requested sg completed arch restore phase loan
    original saved acquired released cursor initial_heap written prefix_heap returned current
    environment_heap final_cursor final_heap frame Henv Hr0 Hmask Hpre Hprefix Hactual Hsuffix.
  unfold task_delete_call_masked, kernel_continuation_call_masked in Hpre.
  assert (Hopen :
    critical_region_masked environment.(task_stack_call_platform) critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) original **
    kernel_continuation_inv environment.(task_stack_call_continuations)
      (task_delete_phase_resources phase loan) (task_create_continuation_local saved_local)
      sg (task_stack_call_active_key original) released ** frame |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) original **
    (kernel_continuation_inv environment.(task_stack_call_continuations)
      (task_delete_phase_resources phase loan) (task_create_continuation_local saved_local)
      sg (task_stack_call_active_key original) released ** frame)) by entailer!.
  destruct (armv7a_restore_prefix_releases_critical_region
    environment.(task_stack_call_external) environment.(task_stack_call_platform) critical arch
    restore sg original saved acquired cursor initial_heap written prefix_heap _ Hr0 Hmask
    (Hopen initial_heap Hpre) Hprefix) as [Hwritten [Hmemory Howned]].
  assert (Hclosed : (task_delete_call_closed environment saved_local phase loan sg original
    (armv7a_irq_fiq_mask saved) released ** frame) prefix_heap).
  { match type of Howned with ?P prefix_heap => match goal with |- ?Q prefix_heap =>
      assert (Hclose : P |-- Q) end end.
    { unfold task_delete_call_closed, kernel_continuation_call_closed; entailer!. }
    exact (Hclose prefix_heap Howned). }
  destruct (task_delete_actual_environment_return environment critical saved_local requested sg
    completed phase loan original released returned current (armv7a_irq_fiq_mask saved)
    prefix_heap environment_heap frame Henv Hactual Hclosed)
    as [Htrace [Hnormal [Hrely [Htransport Hreturned]]]].
  assert (Hword : written.(kernel_restore_msr_word) = Some
    (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0))).
  { rewrite Hwritten; reflexivity. }
  unfold task_delete_call_closed, kernel_continuation_call_closed in Hreturned.
  assert (Horder : kernel_call_execution_owned environment.(task_stack_call_external)
    environment.(task_stack_call_platform) returned (armv7a_irq_fiq_mask saved) **
    kernel_continuation_inv environment.(task_stack_call_continuations)
      (task_delete_phase_resources phase loan) (task_create_continuation_local saved_local)
      sg (task_stack_call_active_key returned) current ** frame |--
    kernel_call_execution_owned environment.(task_stack_call_external)
    environment.(task_stack_call_platform) returned (armv7a_irq_fiq_mask saved) **
    (kernel_continuation_inv environment.(task_stack_call_continuations)
      (task_delete_phase_resources phase loan) (task_create_continuation_local saved_local)
      sg (task_stack_call_active_key returned) current ** frame)) by entailer!.
  pose proof (Horder environment_heap Hreturned) as Hsuffix_pre.
  rewrite <- Hr0, <- (armv7a_cpsr_restore_mask_eq cursor.(kernel_restore_current_cpsr)
    cursor.(kernel_restore_r0)) in Hsuffix_pre.
  destruct (armv7a_restore_suffix_transports_owned_execution
    environment.(task_stack_call_external) environment.(task_stack_call_platform) critical arch
    restore returned _ written environment_heap final_cursor final_heap _ Hword Hsuffix_pre Hsuffix)
    as [Hfinal [Hmemory' Hafter]].
  split; [rewrite Hfinal, Hwritten; reflexivity|].
  split; [unfold task_delete_restore_history; tauto|].
  rewrite armv7a_cpsr_restore_mask_eq, Hr0 in Hafter.
  match type of Hafter with ?P final_heap => match goal with |- ?Q final_heap =>
    assert (Hclose : P |-- Q) end end.
  { unfold task_delete_call_closed, kernel_continuation_call_closed; entailer!. }
  exact (Hclose final_heap Hafter).
Qed.

(** The save interval supplies the same returned/current world consumed
    by the real suffix. The history describes that environment interval;
    it does not assert a restore instruction at the save site. *)
Lemma task_delete_save_completed_call_resources :
  forall environment critical saved_local requested sg completed arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    phase loan original before returned current mask registers initial_heap
    environment_heap final_registers acquired final_heap frame,
  task_delete_c_environment environment critical saved_local requested sg completed ->
  completed.(task_delete_environment_execution)
    phase original before returned current initial_heap environment_heap ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (task_delete_call_closed environment saved_local phase loan
    sg original mask before ** frame) initial_heap ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current environment_heap
    final_registers acquired final_heap ->
  acquired = current /\
  interrupt_saved_value mask final_registers.(kernel_save_r0) /\
  task_delete_restore_history environment critical requested phase sg
    original before returned current /\
  kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original returned mask
    final_registers.(kernel_save_r0) before current /\
  (task_delete_call_masked environment critical saved_local phase loan
    sg returned final_registers.(kernel_save_r0) current current ** frame) final_heap.
Proof.
  intros environment critical saved_local requested sg completed arch save phase loan
    original before returned current mask registers initial_heap environment_heap
    final_registers acquired final_heap frame Henv Hactual Hreturn Hvalid Hmask Hpre Hsuffix.
  destruct (task_delete_actual_environment_return environment critical saved_local requested sg
    completed phase loan original before returned current mask initial_heap environment_heap
    frame Henv Hactual Hpre) as [Htrace [Hnormal [Hrely [Htransport Hclosed]]]].
  destruct (kernel_continuation_call_uninterrupted_save
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    environment.(task_stack_call_port) critical arch environment.(task_stack_call_continuations)
    save (task_delete_phase_resources phase loan) (task_create_continuation_local saved_local)
    sg (task_stack_call_active_key returned) returned current mask registers environment_heap
    final_registers acquired final_heap frame Hreturn Hvalid Hmask Hclosed Hsuffix)
    as [Hstate [Hr0 [Hsource Hmasked]]].
  assert (Hsaved : interrupt_saved_value mask final_registers.(kernel_save_r0)).
  { rewrite Hr0; split; [exact Hvalid|exact Hmask]. }
  assert (Hhistory : task_delete_restore_history environment critical requested phase sg
    original before returned current) by (unfold task_delete_restore_history; tauto).
  assert (Hcall : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original returned mask
    final_registers.(kernel_save_r0) before current).
  { unfold kernel_call_save_source; destruct Hnormal as [[Hi [Ho Hs]] Havailable]; auto. }
  split; [exact Hstate|]. split; [exact Hsaved|].
  split; [exact Hhistory|]. split; [exact Hcall|exact Hmasked].
Qed.

(** Two separate actual intervals meet on one closed heap. In the C body
    OS_Dummy frames that cut. No composition law for environment_execution
    is assumed, and neither actual interval is replaced by a flat trace. *)
Lemma task_delete_prepared_restore_save_window :
  forall environment critical saved_local requested sg completed arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    original initial first acquired priority tid node prepared loan saved
    cursor initial_heap written prefix_heap middle between restore_environment_heap
    final_cursor middle_heap registers returned resumed save_environment_heap
    final_registers reacquired final_heap frame,
  task_delete_c_environment environment critical saved_local requested sg completed ->
  task_delete_preparation_history sg requested original initial first acquired
    priority tid node prepared loan ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (task_delete_call_masked environment critical saved_local
    (TaskDeletePrepared tid node.(taskGeneration)) loan
    sg first saved acquired (task_delete_locked prepared) ** frame) initial_heap ->
  armv7a_restore_prefix_transition restore cursor initial_heap written prefix_heap ->
  completed.(task_delete_environment_execution)
    (TaskDeletePrepared tid node.(taskGeneration)) first (task_delete_locked prepared)
    middle between prefix_heap restore_environment_heap ->
  armv7a_restore_suffix_transition restore written restore_environment_heap
    final_cursor middle_heap ->
  completed.(task_delete_environment_execution)
    (TaskDeletePrepared tid node.(taskGeneration)) middle between
    returned resumed middle_heap save_environment_heap ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) resumed
    save_environment_heap final_registers reacquired final_heap ->
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  reacquired = resumed /\
  task_delete_restore_history environment critical requested
    (TaskDeletePrepared tid node.(taskGeneration)) sg
    first (task_delete_locked prepared) middle between /\
  task_delete_restore_history environment critical requested
    (TaskDeletePrepared tid node.(taskGeneration)) sg middle between returned resumed /\
  kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg middle returned
    (armv7a_irq_fiq_mask saved) final_registers.(kernel_save_r0) between resumed /\
  task_delete_window_history sg requested original initial first acquired
    priority tid node prepared loan returned resumed /\
  interrupt_saved_value (armv7a_irq_fiq_mask saved) final_registers.(kernel_save_r0) /\
  (task_delete_call_masked environment critical saved_local
    (TaskDeletePrepared tid node.(taskGeneration)) loan
    sg returned final_registers.(kernel_save_r0) resumed resumed ** frame) final_heap.
Proof.
  intros environment critical saved_local requested sg completed arch restore save
    original initial first acquired priority tid node prepared loan saved
    cursor initial_heap written prefix_heap middle between restore_environment_heap
    final_cursor middle_heap registers returned resumed save_environment_heap
    final_registers reacquired final_heap frame Henv Hprep Hr0 Hmask Hpre Hprefix
    Hactual_restore Hsuffix_restore Hactual_save Hreturn Hvalid Hsave_mask Hsuffix_save.
  destruct (task_delete_restore_completed_call_resources environment critical saved_local
    requested sg completed arch restore (TaskDeletePrepared tid node.(taskGeneration)) loan
    first saved acquired (task_delete_locked prepared) cursor initial_heap written prefix_heap
    middle between restore_environment_heap final_cursor middle_heap frame
    Henv Hr0 Hmask Hpre Hprefix Hactual_restore Hsuffix_restore)
    as [Hreturn_word [Hrestore_history Hmiddle]].
  destruct (task_delete_save_completed_call_resources environment critical saved_local
    requested sg completed arch save (TaskDeletePrepared tid node.(taskGeneration)) loan
    middle between returned resumed (armv7a_irq_fiq_mask saved) registers middle_heap
    save_environment_heap final_registers reacquired final_heap frame
    Henv Hactual_save Hreturn Hvalid Hsave_mask Hmiddle Hsuffix_save)
    as [Hstate [Hsaved [Hsave_history [Hsave_source Hmasked]]]].
  assert (Hwindow : task_delete_window_history sg requested original initial first acquired
    priority tid node prepared loan returned resumed).
  { pose proof Hrestore_history as [Htrace1 [Hnormal1 [Hrely1 Htransport1]]].
    pose proof Hsave_history as [Htrace2 [Hnormal2 [Hrely2 Htransport2]]].
    pose proof Hprep as [Hlive [Hprepare Hrunning]].
    destruct Hlive as [Hlookup _].
    destruct Hlookup as [_ [_ [Hfirst _]]].
    unfold task_delete_window_history; split; [exact Hprep|].
    split.
    - pose proof (task_delete_same_return_trans first (task_delete_locked prepared)
        middle between returned resumed Hnormal1 Hnormal2) as Hnormal.
      destruct (proj1 Hnormal) as [Hi [Ho Hs]], Hfirst as [Hi' [Ho' Hs']].
      unfold task_tcb_init_stack_same_call; repeat split; congruence.
    - split.
      + eapply task_delete_phase_rely_trans; eassumption.
      + exact (proj1 Htransport2 (proj1 Htransport1 Hrunning)). }
  split; [exact Hreturn_word|]. split; [exact Hstate|].
  split; [exact Hrestore_history|]. split; [exact Hsave_history|].
  split; [exact Hsave_source|]. split; [exact Hwindow|].
  split; [exact Hsaved|exact Hmasked].
Qed.

(** One source edge for the actual Restore/OS_Dummy/Save window.  The two
    environment executions remain separate, with their original calls,
    states and heaps.  The restore suffix's middle_heap is exactly the
    second interval's input.  This constructor records no desired endpoint
    invariant or current-task condition. *)
Inductive sched_task_delete_window_execution (environment : TaskStackCallEnvironment)
  (critical : CriticalRegionResources) sg :
  UCOS2_Verify_State -> model -> UCOS2_Verify_State -> model -> Prop :=
| SchedTaskDeleteWindowExecution :
  forall saved_local requested completed arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    original initial first acquired priority tid node prepared loan saved
    cursor initial_heap written prefix_heap middle between restore_environment_heap
    final_cursor middle_heap registers returned resumed save_environment_heap
    final_registers reacquired final_heap frame,
  task_delete_c_environment environment critical saved_local requested sg completed ->
  task_delete_preparation_history sg requested original initial first acquired
    priority tid node prepared loan ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (task_delete_call_masked environment critical saved_local
    (TaskDeletePrepared tid node.(taskGeneration)) loan
    sg first saved acquired (task_delete_locked prepared) ** frame) initial_heap ->
  armv7a_restore_prefix_transition restore cursor initial_heap written prefix_heap ->
  completed.(task_delete_environment_execution)
    (TaskDeletePrepared tid node.(taskGeneration)) first (task_delete_locked prepared)
    middle between prefix_heap restore_environment_heap ->
  armv7a_restore_suffix_transition restore written restore_environment_heap
    final_cursor middle_heap ->
  completed.(task_delete_environment_execution)
    (TaskDeletePrepared tid node.(taskGeneration)) middle between
    returned resumed middle_heap save_environment_heap ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) resumed
    save_environment_heap final_registers reacquired final_heap ->
  sched_task_delete_window_execution environment critical sg
    (task_delete_locked prepared) initial_heap resumed final_heap.

Lemma sched_task_delete_window_source_resources : forall environment critical sg
  before initial_heap after final_heap,
  sched_task_delete_window_execution environment critical sg before initial_heap after final_heap ->
  exists saved_local requested original initial first acquired priority tid node
    prepared loan returned saved frame,
    before = task_delete_locked prepared /\
    task_delete_window_history sg requested original initial first acquired
      priority tid node prepared loan returned after /\
    (task_delete_call_masked environment critical saved_local
      (TaskDeletePrepared tid node.(taskGeneration)) loan
      sg returned saved after after ** frame) final_heap.
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
    as [Hreturn_word [Hstate [Hrestore_history [Hsave_history [Hsave_source
      [Hwindow [Hsaved Hmasked]]]]]]].
  exists saved_local, requested, original, initial, first, acquired, priority, tid, node,
    prepared, loan, returned, final_registers.(kernel_save_r0), frame.
  split; [reflexivity|]. split; [exact Hwindow|exact Hmasked].
Qed.

Lemma sched_task_delete_window_execution_running_eq : forall environment critical sg
  before initial_heap after final_heap,
  sched_task_delete_window_execution environment critical sg before initial_heap after final_heap ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros environment critical sg before initial_heap after final_heap Hsource.
  destruct (sched_task_delete_window_source_resources environment critical sg before
    initial_heap after final_heap Hsource) as
    (saved_local & requested & original & initial & first & acquired & priority & tid & node &
      prepared & loan & returned & saved & frame & Ebefore & Hwindow & Hmasked).
  subst before.
  destruct Hwindow as [_ [_ [Hrely _]]]; exact (proj1 (proj2 Hrely)).
Qed.

(** These are the literal prepare, loop and recycle executions, with one
    shared preparation heap.  The existing producer covers every prepare
    branch; its enclosing file name does not restrict these declarations to
    a nonswitching Scheduler return. *)
Definition sched_task_mutex_del_always_execution sg eid entry prepared
  (before after : model) : Prop :=
  exists preparation_heap,
    mutex_del_prepare_source_execution sg (event_addr sg eid) eid
      entry prepared before preparation_heap /\
    mutex_del_always_after_prepare_execution sg (event_addr sg eid)
      preparation_heap after.

Lemma sched_task_mutex_del_always_source_resources : forall external sg eid
  entry prepared event mutex before after (frame : Assertion),
  mutex_del_parent_layout sg -> event_object_layout_prop sg eid ->
  mutex_del_parent_entry sg eid entry event mutex ->
  (kernel_program_inv sg entry ** frame) before ->
  sched_task_mutex_del_always_execution sg eid entry prepared before after ->
  let checkpoint := mutex_del_always_checkpoint sg eid event prepared in
  sched_task_phase_source external sg entry checkpoint /\
  mutex_del_critical sg eid 1 entry
    (0, (OS_ERR_NONE, negb (Z.eqb (encode_event_wait_grp event.(waitList) entry.(TskState)) 0)))
    checkpoint /\
  (kernel_program_inv sg checkpoint ** frame) after.
Proof.
  intros external sg eid entry prepared event mutex before after frame Hlayout Hobject
    Hentry Hpre [preparation_heap [Hprepare Hsuffix]] checkpoint.
  pose proof (mutex_del_prepare_source_resources sg eid entry prepared event mutex
    before preparation_heap frame Hlayout Hentry Hpre Hprepare) as Hprepared.
  destruct (mutex_del_always_after_prepare_resources sg eid entry prepared event mutex
    preparation_heap after frame Hobject Hprepared Hsuffix) as [Hcritical Hafter].
  split.
  - eapply sched_task_mutex_del_critical_phase_source; exact Hcritical.
  - split; [exact Hcritical|exact Hafter].
Qed.

(** A completed window is not identified with a flat client trace.  Its
    source relation keeps both heaps and all six endpoint indices of the
    existing TaskDel environment.  The original public R/G protocol is
    consumed here, without requiring a closed invariant at Prepared. *)
Definition sched_task_delete_environment_execution environment critical
  saved_local requested sg completed phase loan original before returned after
  mask (initial_heap final_heap : model) (frame : Assertion) : Prop :=
  task_delete_c_environment environment critical saved_local requested sg completed /\
  completed.(task_delete_environment_execution)
    phase original before returned after initial_heap final_heap /\
  (task_delete_call_closed environment saved_local phase loan
    sg original mask before ** frame) initial_heap.

Lemma sched_task_delete_environment_source_resources : forall environment critical
  saved_local requested sg completed phase loan original before returned after
  mask initial_heap final_heap frame,
  sched_task_delete_environment_execution environment critical saved_local requested
    sg completed phase loan original before returned after mask initial_heap final_heap frame ->
  kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    before false returned.(os_sched_call_origin) after /\
  task_delete_same_return original before returned after /\
  task_delete_phase_rely requested phase sg before after /\
  task_delete_protocol_transport sg requested original before returned after /\
  (task_delete_call_closed environment saved_local phase loan
    sg returned mask after ** frame) final_heap.
Proof.
  intros environment critical saved_local requested sg completed phase loan original
    before returned after mask initial_heap final_heap frame [Henv [Hactual Hpre]].
  eapply task_delete_actual_environment_return; eassumption.
Qed.
(** Heap-indexed source edges keep the actual intermediate heap at each
    composition point.  The Mutex constructor retains its literal source
    execution, not only the abstract critical result.  The TaskDel edge
    retains the original callee's conditional environment and its actual
    interval, rather than assuming an arbitrary completed endpoint.

    This is an extensible source syntax for the proved edges below.  It is
    not a theorem classifying every kernel call, and in particular does not
    silently convert the old arbitrary client registry into this family. *)
Inductive sched_task_phase_heap_step (environment : TaskStackCallEnvironment)
  (critical : CriticalRegionResources) sg :
  UCOS2_Verify_State -> model -> UCOS2_Verify_State -> model -> Prop :=
| SchedTaskPhaseHeapMutexDeleteAlways : forall eid entry prepared event mutex
    before_heap after_heap (frame : Assertion),
    mutex_del_parent_layout sg -> event_object_layout_prop sg eid ->
    mutex_del_parent_entry sg eid entry event mutex ->
    (kernel_program_inv sg entry ** frame) before_heap ->
    sched_task_mutex_del_always_execution sg eid entry prepared before_heap after_heap ->
    sched_task_phase_heap_step environment critical sg entry before_heap
      (mutex_del_always_checkpoint sg eid event prepared) after_heap
| SchedTaskPhaseHeapDeleteEnvironment : forall saved_local requested completed
    phase loan original before returned after mask before_heap after_heap frame,
    sched_task_delete_environment_execution environment critical saved_local requested
      sg completed phase loan original before returned after mask before_heap after_heap frame ->
    sched_task_phase_heap_step environment critical sg before before_heap after after_heap
| SchedTaskPhaseHeapDeleteWindow : forall before before_heap after after_heap,
    sched_task_delete_window_execution environment critical sg before before_heap after after_heap ->
    sched_task_phase_heap_step environment critical sg before before_heap after after_heap.

Inductive sched_task_phase_heap_source environment critical sg :
  UCOS2_Verify_State -> model -> UCOS2_Verify_State -> model -> Prop :=
| SchedTaskPhaseHeapSourceRefl : forall state heap,
    sched_task_phase_heap_source environment critical sg state heap state heap
| SchedTaskPhaseHeapSourceNext : forall before before_heap middle middle_heap after after_heap,
    sched_task_phase_heap_step environment critical sg before before_heap middle middle_heap ->
    sched_task_phase_heap_source environment critical sg middle middle_heap after after_heap ->
    sched_task_phase_heap_source environment critical sg before before_heap after after_heap.

Lemma sched_task_phase_heap_source_trans : forall environment critical sg
  before before_heap middle middle_heap after after_heap,
  sched_task_phase_heap_source environment critical sg before before_heap middle middle_heap ->
  sched_task_phase_heap_source environment critical sg middle middle_heap after after_heap ->
  sched_task_phase_heap_source environment critical sg before before_heap after after_heap.
Proof.
  intros environment critical sg before before_heap middle middle_heap after after_heap
    Hprefix Hsuffix; induction Hprefix.
  - exact Hsuffix.
  - eapply SchedTaskPhaseHeapSourceNext; [exact H|apply IHHprefix; exact Hsuffix].
Qed.

Lemma sched_task_phase_heap_step_running_eq : forall environment critical sg
  before before_heap after after_heap,
  sched_task_phase_heap_step environment critical sg before before_heap after after_heap ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros environment critical sg before before_heap after after_heap Hsource; destruct Hsource.
  - destruct (sched_task_mutex_del_always_source_resources environment.(task_stack_call_external)
      sg eid entry prepared event mutex before_heap after_heap frame H H0 H1 H2 H3)
      as [Hphase Hresources].
    eapply sched_task_phase_source_running_eq; exact Hphase.
  - destruct (sched_task_delete_environment_source_resources environment critical saved_local
      requested sg completed phase loan original before returned after mask before_heap
      after_heap frame H) as [_ [_ [Hrely _]]].
    exact (proj1 (proj2 Hrely)).
  - eapply sched_task_delete_window_execution_running_eq; exact H.
Qed.

Lemma sched_task_phase_heap_source_running_eq : forall environment critical sg
  before before_heap after after_heap,
  sched_task_phase_heap_source environment critical sg before before_heap after after_heap ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros environment critical sg before before_heap after after_heap Hsource; induction Hsource.
  - reflexivity.
  - rewrite IHHsource; eapply sched_task_phase_heap_step_running_eq; exact H.
Qed.

