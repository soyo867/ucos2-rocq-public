Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_inherit_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_idle_protocol_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_sched_call_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.mutex.
Import TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.

(** The source modules below supply these field observations from their real
    postconditions.  This lemma permits status, delay, wait, ready-list,
    saved-stack and unrelated-module changes.  It does not freeze priority
    across an operation which actually changes it. *)
Lemma sched_current_consistency_fields_frame :
  forall before_tasks after_tasks before after,
  after.(curTaskID) = before.(curTaskID) ->
  after.(curSchedPrio) = before.(curSchedPrio) ->
  (forall slot node,
    before.(curTaskID) = Some slot -> before_tasks.(inUsedTaskStates) slot = Some node ->
    exists returned, after_tasks.(inUsedTaskStates) slot = Some returned /\
      returned.(curPrio) = node.(curPrio)) ->
  sched_current_consistency before_tasks before ->
  sched_current_consistency after_tasks after.
Proof.
  intros before_tasks after_tasks before after Hcurrent Hcache Htasks Hconsistent.
  unfold sched_current_consistency in *; rewrite Hcurrent.
  destruct before.(curTaskID) as [slot|] eqn:Hslot.
  - destruct Hconsistent as [node [Hnode Hpriority]].
    destruct (Htasks slot node eq_refl Hnode) as [returned [Hreturned Hprio]].
    exists returned; split; [exact Hreturned|rewrite Hcache, Hprio; exact Hpriority].
  - rewrite Hcache; exact Hconsistent.
Qed.

Lemma os_sched_prefix_preserves_current_consistency : forall state,
  sched_current_consistency state.(TskState) state.(SchedState) ->
  sched_current_consistency (os_sched_prefix_state state).(TskState)
    (os_sched_prefix_state state).(SchedState).
Proof.
  intros state Hconsistent.
  destruct (os_sched_ready_checkpoint_frame state) as [Hready [Hcurrent [Hcache Hrunning]]].
  apply sched_current_consistency_fields_frame with
    (before_tasks := state.(TskState)) (before := state.(SchedState)).
  - exact Hcurrent.
  - exact Hcache.
  - intros slot node Hslot Hnode; exists node; auto.
  - exact Hconsistent.
Qed.

Lemma os_sched_save_sp_preserves_current_consistency : forall state slot sp,
  sched_current_consistency state.(TskState) state.(SchedState) ->
  sched_current_consistency (os_sched_save_current_sp state slot sp).(TskState)
    (os_sched_save_current_sp state slot sp).(SchedState).
Proof.
  intros state slot sp Hconsistent.
  unfold os_sched_save_current_sp.
  destruct (state.(TskState).(inUsedTaskStates) slot) as [changed|] eqn:Hchanged.
  - apply sched_current_consistency_fields_frame with
      (before_tasks := state.(TskState)) (before := state.(SchedState)); try reflexivity.
    + intros current node Hcurrent Hnode.
      destruct (Z.eq_dec current slot) as [->|Hother].
      * rewrite Hchanged in Hnode; inversion Hnode; subst node.
        exists (task_set_saved_sp changed sp); split; [|reflexivity].
        cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
      * exists node; split; [|reflexivity].
        cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
        rewrite (proj2 (Z.eqb_neq current slot) Hother); exact Hnode.
    + exact Hconsistent.
  - exact Hconsistent.
Qed.

(** Destination binding, not a ready premise, is sufficient for cache
    consistency.  Ready-at-return uses the stronger actual selector source
    in sched_task_return_source_spec. *)
Lemma os_sched_destination_installs_current_consistency :
  forall external context outgoing hooked incoming resumed,
  os_sched_destination_binding external context outgoing hooked incoming resumed ->
  sched_current_consistency
    (os_sched_install_context context outgoing incoming hooked).(TskState)
    (os_sched_install_context context outgoing incoming hooked).(SchedState).
Proof.
  intros external context outgoing hooked incoming resumed
    [Hselected [[node [Hnode [Hgeneration [Hpriority Hrestore]]]] Hrest]].
  change (match hooked.(SchedState).(highRdyTid) with
    | None => hooked.(SchedState).(highRdyPrio) = None
    | Some slot => exists node,
        hooked.(TskState).(inUsedTaskStates) slot = Some node /\
        hooked.(SchedState).(highRdyPrio) = Some node.(curPrio)
    end).
  rewrite Hselected; exists node; auto.
Qed.

(** The raw RdyAtPrio contract is consumed by Mutex Del/Post through this
    exact transformer, including its target=current conditional cache store.
    Nested ownership is allowed; no assumption makes every owner current. *)
Lemma mutex_del_relocated_preserves_current_consistency :
  forall sg entry ceiling owner node priority,
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  sched_current_consistency
    (mutex_del_relocated_state sg entry ceiling owner node priority).(TskState)
    (mutex_del_relocated_state sg entry ceiling owner node priority).(SchedState).
Proof.
  intros sg entry ceiling owner node priority Hconsistent.
  unfold sched_current_consistency in *.
  change (match entry.(SchedState).(curTaskID) with
    | None => mutex_del_current_priority entry owner priority = None
    | Some current => exists returned,
        (mutex_del_relocated_tasks entry ceiling owner node priority).(inUsedTaskStates) current = Some returned /\
        mutex_del_current_priority entry owner priority = Some returned.(curPrio)
    end).
  unfold mutex_del_current_priority.
  destruct entry.(SchedState).(curTaskID) as [current|] eqn:Hcurrent.
  - destruct (Z.eq_dec owner current) as [->|Hother].
    + exists (mutex_priority_task node priority); split; [|reflexivity].
      cbn [mutex_del_relocated_tasks glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
    + destruct Hconsistent as [old [Hold Hcache]].
      exists old; split; [|exact Hcache].
      cbn [mutex_del_relocated_tasks glob_task_set_usedtask inUsedTaskStates].
      rewrite (proj2 (Z.eqb_neq current owner) ltac:(congruence)); exact Hold.
  - exact Hconsistent.
Qed.

(** This is the critical relation actually exported by the corrected
    OSTaskChangePrio C contract, including its real error branches.  The
    older Sem-local illustrative family is not used as API registration. *)
Lemma task_change_prio_critical_preserves_current_consistency :
  forall sg requested priority before code after,
  task_change_prio_critical sg requested priority before code after ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros sg requested priority before code after Hstep Hcurrent.
  unfold task_change_prio_critical in Hstep.
  destruct (before.(TskState).(prioTbl) priority).
  - destruct Hstep as [selected [Hselected Hstep]].
    unfold task_change_prio_selected_effect in Hstep.
    destruct (Z.eqb selected sg.(osLowestPrio)).
    + destruct Hstep as [_ ->]; exact Hcurrent.
    + destruct (before.(TskState).(prioTbl) selected).
      * destruct Hstep as [_ ->]; exact Hcurrent.
      * destruct Hstep as [_ ->]; exact Hcurrent.
      * destruct Hstep as [node [Hnode [_ ->]]].
        apply task_change_priority_state_preserves_current_consistency; exact Hcurrent.
  - destruct Hstep as [_ ->]; exact Hcurrent.
  - destruct Hstep as [_ ->]; exact Hcurrent.
Qed.

(** This family names mathematical consequences of existing source effects.
    It is not the registry of all enabled C programs and does not grant a
    new external guarantee.  A heap-bound module producer supplies one
    constructor for its actual edge.  In particular the Frame constructor
    must prove the three field observations of that real client step. *)
Inductive sched_current_source_step (external : OsSchedExternalResources)
  (sg : StableGlobVars) : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| SchedCurrentSourceFrame : forall action before after,
    kernel_client_step action sg before after ->
    after.(SchedState).(curTaskID) = before.(SchedState).(curTaskID) ->
    after.(SchedState).(curSchedPrio) = before.(SchedState).(curSchedPrio) ->
    (forall slot node, before.(SchedState).(curTaskID) = Some slot ->
      before.(TskState).(inUsedTaskStates) slot = Some node ->
      exists returned, after.(TskState).(inUsedTaskStates) slot = Some returned /\
        returned.(curPrio) = node.(curPrio)) ->
    sched_current_source_step external sg before after
| SchedCurrentSourceChangePriority : forall state slot node oldprio priority,
    sched_current_source_step external sg state
      (task_change_priority_state sg state slot node oldprio priority)
| SchedCurrentSourceChangePrioCall : forall requested priority before code after,
    task_change_prio_critical sg requested priority before code after ->
    sched_current_source_step external sg before after
| SchedCurrentSourceMutexRelocate : forall state ceiling owner node priority,
    sched_current_source_step external sg state
      (mutex_del_relocated_state sg state ceiling owner node priority)
| SchedCurrentSourceMutexInherit : forall call before idle eid event mutex owner node base waiter after,
    UCOS2_state_inv sg before ->
    mutex_idle_slot before.(TskState) idle -> mutex_idle_excluded idle before.(EventState) ->
    mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
    before.(EventState).(inUsedEventStates) eid = Some event ->
    event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
    mutex.(mfOwner) = Some owner -> before.(TskState).(inUsedTaskStates) owner = Some node ->
    before.(SchedState).(isRunning) = true -> call.(os_sched_call_stack).(stackLeaseSlot) <> owner ->
    kernel_call_task_source call before -> sem_pend_blocking_call_stage sg call before ->
    mutex_pend_inherit_step sg before owner node base waiter mutex.(mfPCP) after ->
    sched_current_source_step external sg before after
| SchedCurrentSourcePrefix : forall state,
    sched_current_source_step external sg state (os_sched_prefix_state state)
| SchedCurrentSourceSaveSP : forall state slot sp,
    sched_current_source_step external sg state (os_sched_save_current_sp state slot sp)
| SchedCurrentSourceTake : forall state incoming,
    sched_current_source_step external sg state (os_int_exit_wrapper_restored_state state incoming)
| SchedCurrentSourceInstall : forall context outgoing hooked incoming resumed,
    os_sched_destination_binding external context outgoing hooked incoming resumed ->
    sched_current_source_step external sg hooked
      (os_sched_install_context context outgoing incoming hooked).

Lemma sched_current_source_step_preserves_consistency : forall external sg before after,
  sched_current_source_step external sg before after ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros external sg before after Hstep Hconsistent; destruct Hstep.
  - eapply sched_current_consistency_fields_frame; eassumption.
  - apply task_change_priority_state_preserves_current_consistency; exact Hconsistent.
  - eapply task_change_prio_critical_preserves_current_consistency; eassumption.
  - apply mutex_del_relocated_preserves_current_consistency; exact Hconsistent.
  - exact (proj1 (proj2 (mutex_pend_inherit_preserves_call_stage sg call before idle eid event mutex owner node
      base waiter after H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hconsistent H11 H12))).
  - apply os_sched_prefix_preserves_current_consistency; exact Hconsistent.
  - apply os_sched_save_sp_preserves_current_consistency; exact Hconsistent.
  - exact Hconsistent.
  - eapply os_sched_destination_installs_current_consistency; eassumption.
Qed.

Inductive sched_current_source_trace external sg :
  UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| SchedCurrentSourceRefl : forall state, sched_current_source_trace external sg state state
| SchedCurrentSourceNext : forall before current after,
    sched_current_source_step external sg before current ->
    sched_current_source_trace external sg current after ->
    sched_current_source_trace external sg before after
| SchedCurrentSourceSelectedReturn : forall port origin before returning hooked context outgoing incoming resumed,
    task_execution_source_trace external port sg origin before returning hooked ->
    os_sched_destination_binding external context outgoing hooked incoming resumed ->
    sched_current_source_trace external sg before
      (os_sched_install_context context outgoing incoming hooked).

Lemma sched_current_source_trace_preserves_consistency : forall external sg before after,
  sched_current_source_trace external sg before after ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros external sg before after Htrace; induction Htrace; intros Hconsistent.
  - exact Hconsistent.
  - apply IHHtrace; eapply sched_current_source_step_preserves_consistency; eassumption.
  - eapply os_sched_destination_installs_current_consistency; eassumption.
Qed.
