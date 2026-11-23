Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_pend_abort_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSTaskChangePrio, pinned V2.93.01 Source/os_task.c:60--188.
    This is its actual single-Event critical mutation, not a new public
    guard or a whole-function theorem. SELF reads the current TCB priority;
    the new slot is checked first. The reviewed current-target repair writes
    OSPrioCur after the five TCB stores, before Restore, using actual task
    identity. The post-Restore OSRunning read and OS_Sched call remain separate boundaries.
    Full global preservation/client registration is NOT asserted here. *)
Definition task_change_priority_argument_error (sg : StableGlobVars)
  (oldprio newprio : Priority) : option OSErrCode :=
  if sg.(osKernelConfig).(cfgArgumentChecks) then
    if (Z.leb sg.(osLowestPrio) oldprio && negb (Z.eqb oldprio sg.(osPrioSelf)))%bool
    then Some OS_ERR_PRIO_INVALID else
    if Z.leb sg.(osLowestPrio) newprio then Some OS_ERR_PRIO_INVALID else None
  else None.

Definition task_change_priority_tasks (tasks : Glob_TaskAbstractState)
  (tid : TaskID) (old : TaskAbstractState) (oldprio newprio : Priority) : Glob_TaskAbstractState :=
  {| inUsedTaskStates := (glob_task_set_usedtask tasks tid (mutex_priority_task old newprio)).(inUsedTaskStates);
     unUsedTaskStates := tasks.(unUsedTaskStates); tcbListHead := tasks.(tcbListHead);
     prioTbl := fun p => if Z.eqb p newprio then PTTask tid else
       if Z.eqb p oldprio then PTFree else tasks.(prioTbl) p;
     taskCount := tasks.(taskCount); taskLifecycle := tasks.(taskLifecycle);
     taskRegNextID := tasks.(taskRegNextID); parkedTaskStacks := tasks.(parkedTaskStacks) |}.

Definition task_change_priority_ready (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (scheduler : SchedAbstractState) (tid : TaskID) (old : TaskAbstractState)
  (new_tasks : Glob_TaskAbstractState) : SchedAbstractState :=
  if Z.eqb (Z.land (encode_ready_tbl_at_or scheduler.(readyList) tasks (old.(curPrio) / 8))
       (tcb_bit_x_of_prio old.(curPrio))) 0 then scheduler else
  sched_set_ready scheduler (insert_sorted_by (wait_prio_key sg new_tasks) tid
    (remove_Z_eqb tid scheduler.(readyList))).

Definition task_change_priority_events (sg : StableGlobVars) (events : Glob_EventAbstractState)
  (new_tasks : Glob_TaskAbstractState) (tid : TaskID) (old : TaskAbstractState) : Glob_EventAbstractState :=
  match old.(eventPtr) with
  | None => events
  | Some eid => match events.(inUsedEventStates) eid with
    | None => events
    | Some event => update_event_field_raw events eid (event_insert_waiter sg new_tasks event tid)
    end
  end.

(** The repaired tail compares the protected target with OSTCBCur.
    The condition is independent of SELF spelling, ready membership, the
    old priority byte and the task/handler execution view. *)
Definition task_change_priority_cached_priority (scheduler : SchedAbstractState)
  (tid : TaskID) (newprio : Priority) : option Priority :=
  match scheduler.(curTaskID) with
  | None => scheduler.(curSchedPrio)
  | Some current => if Z.eqb tid current then Some newprio else scheduler.(curSchedPrio)
  end.

Definition task_change_priority_current_cache (scheduler : SchedAbstractState)
  (tid : TaskID) (newprio : Priority) : SchedAbstractState :=
  {| readyList := scheduler.(readyList); curTaskID := scheduler.(curTaskID);
     curSchedPrio := task_change_priority_cached_priority scheduler tid newprio;
     highRdyTid := scheduler.(highRdyTid); highRdyPrio := scheduler.(highRdyPrio);
     ctxSwCtr := scheduler.(ctxSwCtr); isRunning := scheduler.(isRunning) |}.

Lemma task_change_priority_current_cache_preserves_in_range :
  forall sg tasks scheduler tid newprio,
  task_priority_in_range sg newprio -> sched_in_range sg tasks scheduler ->
  sched_in_range sg tasks (task_change_priority_current_cache scheduler tid newprio).
Proof.
  intros sg tasks scheduler tid newprio Hnew [Hready [Hhigh [Hcounter [Hcurrent Hpriority]]]].
  split; [exact Hready|]. split; [exact Hhigh|]. split; [exact Hcounter|].
  split; [exact Hcurrent|].
  change (match task_change_priority_cached_priority scheduler tid newprio with
          | None => True | Some p => task_priority_in_range sg p end).
  unfold task_change_priority_cached_priority.
  destruct scheduler.(curTaskID) as [current|];
    [destruct (Z.eqb tid current)|]; assumption.
Qed.

Definition task_change_priority_state (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (tid : TaskID) (old : TaskAbstractState) (oldprio newprio : Priority) : UCOS2_Verify_State :=
  let tasks := task_change_priority_tasks entry.(TskState) tid old oldprio newprio in
  replace_SchedS (task_change_priority_current_cache
    (task_change_priority_ready sg entry.(TskState) entry.(SchedState) tid old tasks) tid newprio)
    (replace_EventS (task_change_priority_events sg entry.(EventState) tasks tid old)
      (replace_TskS tasks entry)).

(** These are exactly the two branches of the SELF resolution. No current
    task fact is demanded on the non-SELF path. Actual table/ECB read-domain
    facts are explicit and are not turned into extra C error branches. *)
Definition task_change_priority_selection (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (requested selected : Priority) : Prop :=
  (requested = sg.(osPrioSelf) /\ exists tid current,
    entry.(SchedState).(curTaskID) = Some tid /\
    entry.(TskState).(inUsedTaskStates) tid = Some current /\ selected = current.(curPrio)) \/
  (requested <> sg.(osPrioSelf) /\ selected = requested).

Definition task_change_priority_critical (sg : StableGlobVars) (oldprio newprio : Priority)
  : program UCOS2_Verify_State OSErrCode :=
  fun entry result after => task_priority_in_range sg newprio /\
    match entry.(TskState).(prioTbl) newprio with
    | PTReserved | PTTask _ => result = OS_ERR_PRIO_EXIST /\ after = entry
    | PTFree => exists selected,
      task_change_priority_selection sg entry oldprio selected /\ task_priority_in_range sg selected /\
      match entry.(TskState).(prioTbl) selected with
      | PTFree => result = OS_ERR_PRIO /\ after = entry
      | PTReserved => result = OS_ERR_TASK_NOT_EXIST /\ after = entry
      | PTTask tid => exists old,
        entry.(TskState).(inUsedTaskStates) tid = Some old /\
        sg.(osKernelConfig).(cfgEventMultiEnabled) = false /\
        (forall eid, old.(eventPtr) = Some eid -> exists e, entry.(EventState).(inUsedEventStates) eid = Some e) /\
        result = OS_ERR_NONE /\ after = task_change_priority_state sg entry tid old selected newprio
      end
    end.

Lemma task_change_priority_tasks_lookup : forall tasks tid old oldprio newprio,
  (task_change_priority_tasks tasks tid old oldprio newprio).(inUsedTaskStates) tid =
    Some (mutex_priority_task old newprio).
Proof. intros; cbn [task_change_priority_tasks glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity. Qed.

Lemma task_change_priority_state_current_cache : forall sg entry tid old oldprio newprio,
  (task_change_priority_state sg entry tid old oldprio newprio).(SchedState).(curTaskID) = entry.(SchedState).(curTaskID) /\
  (task_change_priority_state sg entry tid old oldprio newprio).(SchedState).(curSchedPrio) =
    task_change_priority_cached_priority entry.(SchedState) tid newprio.
Proof.
  intros; unfold task_change_priority_state, task_change_priority_ready,
    task_change_priority_current_cache, task_change_priority_cached_priority.
  destruct (Z.eqb _ 0); split; reflexivity.
Qed.

Lemma task_change_priority_state_current_target_consistency :
  forall sg entry tid old oldprio newprio,
  entry.(SchedState).(curTaskID) = Some tid ->
  sched_current_consistency
    (task_change_priority_state sg entry tid old oldprio newprio).(TskState)
    (task_change_priority_state sg entry tid old oldprio newprio).(SchedState).
Proof.
  intros sg entry tid old oldprio newprio Htarget.
  destruct (task_change_priority_state_current_cache sg entry tid old oldprio newprio)
    as [Hcurrent Hpriority].
  unfold sched_current_consistency; rewrite Hcurrent, Htarget.
  exists (mutex_priority_task old newprio); split.
  - apply task_change_priority_tasks_lookup.
  - unfold task_change_priority_cached_priority in Hpriority.
    rewrite Htarget, Z.eqb_refl in Hpriority; exact Hpriority.
Qed.

Lemma task_change_priority_state_preserves_current_consistency :
  forall sg entry tid old oldprio newprio,
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  sched_current_consistency
    (task_change_priority_state sg entry tid old oldprio newprio).(TskState)
    (task_change_priority_state sg entry tid old oldprio newprio).(SchedState).
Proof.
  intros sg entry tid old oldprio newprio Hbefore.
  destruct entry.(SchedState).(curTaskID) as [current|] eqn:Hcurrent.
  - destruct (Z.eq_dec tid current) as [->|Hother].
    + apply task_change_priority_state_current_target_consistency; exact Hcurrent.
    + destruct (task_change_priority_state_current_cache sg entry tid old oldprio newprio)
        as [Hpointer Hpriority].
      unfold sched_current_consistency in *; rewrite ?Hcurrent in Hbefore.
      rewrite Hpointer, Hcurrent.
      destruct Hbefore as [node [Hnode Hcache]].
      exists node; split.
      * change ((task_change_priority_tasks entry.(TskState) tid old oldprio newprio).(inUsedTaskStates)
          current = Some node).
        cbn [task_change_priority_tasks glob_task_set_usedtask inUsedTaskStates].
        rewrite (proj2 (Z.eqb_neq current tid) ltac:(congruence)); exact Hnode.
      * unfold task_change_priority_cached_priority in Hpriority.
        rewrite Hcurrent, (proj2 (Z.eqb_neq tid current) Hother) in Hpriority.
        rewrite Hpriority; exact Hcache.
  - destruct (task_change_priority_state_current_cache sg entry tid old oldprio newprio)
      as [Hpointer Hpriority].
    unfold sched_current_consistency in *; rewrite ?Hcurrent in Hbefore.
    rewrite Hpointer, Hcurrent.
    unfold task_change_priority_cached_priority in Hpriority.
    rewrite Hcurrent in Hpriority; rewrite Hpriority; exact Hbefore.
Qed.

Lemma task_change_priority_table_writes : forall tasks tid old oldprio newprio,
  (task_change_priority_tasks tasks tid old oldprio newprio).(prioTbl) newprio = PTTask tid /\
  (oldprio <> newprio -> (task_change_priority_tasks tasks tid old oldprio newprio).(prioTbl) oldprio = PTFree) /\
  (forall p, p <> oldprio -> p <> newprio ->
    (task_change_priority_tasks tasks tid old oldprio newprio).(prioTbl) p = tasks.(prioTbl) p).
Proof.
  intros; cbn [task_change_priority_tasks prioTbl]; rewrite Z.eqb_refl.
  split; [reflexivity|]. split.
  - intro H; rewrite (proj2 (Z.eqb_neq _ _) H), Z.eqb_refl; reflexivity.
  - intros p Hold Hnew; rewrite (proj2 (Z.eqb_neq _ _) Hnew), (proj2 (Z.eqb_neq _ _) Hold); reflexivity.
Qed.

Lemma task_change_priority_preserves_wait_fields : forall old priority,
  sem_pend_wait_fields_equal old (mutex_priority_task old priority).
Proof. intros; repeat split; reflexivity. Qed.

Lemma task_change_priority_wait_effect : forall old priority,
  sem_pend_wait_effect old (mutex_priority_task old priority).
Proof. intros; apply SemPendWaitOtherFields, task_change_priority_preserves_wait_fields. Qed.

(** The five source stores are the same physical priority/Y/X/BitY/BitX
    image used by the repaired Mutex helper. That identity changes the
    real priority instead of merely relabelling the old TCB. *)
Lemma task_change_priority_image_consumer : forall sg old priority,
  mutex_priority_image (task_tcb64_image sg old) priority =
    task_tcb64_image sg (mutex_priority_task old priority) /\
  (mutex_priority_task old priority).(curPrio) = priority /\
  sem_pend_wait_effect old (mutex_priority_task old priority).
Proof. intros; split; [apply mutex_priority_image_task_eq|]. split; [reflexivity|apply task_change_priority_wait_effect]. Qed.

(** Literal five-store order of OSTaskChangePrio in the <=63 profile.
    Range is the already accessed priority domain, not an invented C
    branch. In this range the two INT8U coordinates and OS_PRIO shifts do
    not wrap; no hand-written smaller TCB layout is introduced. *)
Definition task_change_priority_source_image (image : TCBCommonImage) (priority : Z)
  : TCBCommonImage :=
  let y := unsigned_last_nbits (Z.shiftr priority 3) 8 in
  let x := unsigned_last_nbits (Z.land priority 7) 8 in
  tcb_write (tcb_write (tcb_write (tcb_write (tcb_write image
    TCBPrio (Some priority)) TCBY (Some y)) TCBX (Some x))
    TCBBitY (Some (unsigned_last_nbits (Z.shiftl 1 y) 8)))
    TCBBitX (Some (unsigned_last_nbits (Z.shiftl 1 x) 8)).

Lemma task_change_priority_source_image_eq : forall image priority,
  0 <= priority < 64 ->
  task_change_priority_source_image image priority = mutex_priority_image image priority.
Proof.
  intros image priority Hp.
  destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding priority Hp)
    as [Hx [Hy [Hand _]]].
  assert (Hshift : Z.shiftr priority 3 = tcb_y_of_prio priority).
  { rewrite Z.shiftr_div_pow2 by lia; reflexivity. }
  unfold task_change_priority_source_image; rewrite Hand, Hshift.
  rewrite (unsigned_last_nbits_eq (tcb_y_of_prio priority) 8) by (cbn; lia).
  rewrite (unsigned_last_nbits_eq (tcb_x_of_prio priority) 8) by (cbn; lia).
  rewrite !shift_one_unsigned_byte_eq__priority_encoding by assumption.
  reflexivity.
Qed.

Lemma task_change_priority_source_image_wait_consumer : forall sg old priority,
  0 <= priority < 64 ->
  task_change_priority_source_image (task_tcb64_image sg old) priority =
    task_tcb64_image sg (mutex_priority_task old priority) /\
  sem_pend_wait_effect old (mutex_priority_task old priority) /\
  (priority <> old.(curPrio) -> (mutex_priority_task old priority).(curPrio) <> old.(curPrio)).
Proof.
  intros; rewrite task_change_priority_source_image_eq by assumption; split.
  - apply mutex_priority_image_task_eq.
  - split; [apply task_change_priority_wait_effect|trivial].
Qed.

Definition sem_pend_task_projection (before after : Glob_TaskAbstractState)
  (tid : TaskID) (old : TaskAbstractState) : Prop :=
  exists current, after.(inUsedTaskStates) tid = Some current /\
    clos_refl_trans TaskAbstractState sem_pend_wait_effect old current.

Lemma sem_pend_task_projection_refl : forall tasks tid old,
  tasks.(inUsedTaskStates) tid = Some old -> sem_pend_task_projection tasks tasks tid old.
Proof. intros; exists old; split; [assumption|apply rt_refl]. Qed.

Lemma sem_pend_updated_task_projection : forall tasks selected previous next tid old,
  tasks.(inUsedTaskStates) selected = Some previous ->
  tasks.(inUsedTaskStates) tid = Some old -> sem_pend_wait_effect previous next ->
  sem_pend_task_projection tasks (glob_task_set_usedtask tasks selected next) tid old.
Proof.
  intros tasks selected previous next tid old Hselected Hold Heffect.
  unfold sem_pend_task_projection; cbn [glob_task_set_usedtask inUsedTaskStates].
  destruct (Z.eqb tid selected) eqn:E.
  - apply Z.eqb_eq in E; subst selected; assert (previous = old) by congruence; subst previous.
    exists next; split; [reflexivity|apply rt_step; exact Heffect].
  - exists old; split; [exact Hold|apply rt_refl].
Qed.

Lemma task_change_priority_state_wait_projection : forall sg entry selected previous oldprio newprio tid old,
  entry.(TskState).(inUsedTaskStates) selected = Some previous ->
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection entry.(TskState)
    (task_change_priority_state sg entry selected previous oldprio newprio).(TskState) tid old.
Proof.
  intros; change (sem_pend_task_projection entry.(TskState)
    (glob_task_set_usedtask entry.(TskState) selected (mutex_priority_task previous newprio)) tid old).
  eapply sem_pend_updated_task_projection; [eassumption|eassumption|apply task_change_priority_wait_effect].
Qed.

Lemma task_change_priority_critical_wait_projection : forall sg oldprio newprio entry code after tid old,
  task_change_priority_critical sg oldprio newprio entry code after ->
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection entry.(TskState) after.(TskState) tid old.
Proof.
  intros sg oldprio newprio entry code after tid old [_ Hstep] Hold.
  destruct (entry.(TskState).(prioTbl) newprio).
  - destruct Hstep as [selected [_ [_ Hstep]]].
    destruct (entry.(TskState).(prioTbl) selected).
    + destruct Hstep as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
    + destruct Hstep as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
    + destruct Hstep as [previous [Hprevious [_ [_ [_ ->]]]]].
      eapply task_change_priority_state_wait_projection; eassumption.
  - destruct Hstep as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
  - destruct Hstep as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
Qed.

Lemma task_change_priority_critical_preserves_pend_continuation :
  forall sg oldprio newprio entry code after tid old eid generation,
  task_change_priority_critical sg oldprio newprio entry code after ->
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  exists current, after.(TskState).(inUsedTaskStates) tid = Some current /\
    sem_pend_wait_continuation eid generation current.
Proof.
  intros * Hstep Hold Hcont.
  destruct (task_change_priority_critical_wait_projection sg oldprio newprio entry code after tid old Hstep Hold)
    as [current [Hcurrent Heffect]].
  exists current; split; [exact Hcurrent|].
  eapply sem_pend_wait_trace_preserves_continuation; eassumption.
Qed.

(** Existing registered clients: their projections are derived from their
    actual source transformers, not assumed by an extra client certificate. *)
Lemma sem_pend_suspend_client_projection : forall actor priority sg entry after tid old,
  kernel_client_step (task_suspend_critical_client actor priority) sg entry after ->
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection entry.(TskState) after.(TskState) tid old.
Proof.
  intros actor priority sg entry after tid old [_ [result [cid [current [_ [_ [_ Hstep]]]]]]] Hold.
  destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg priority current))).
  - destruct Hstep as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
  - destruct Hstep as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
  - destruct Hstep as [previous [Hprevious [_ ->]]].
    eapply sem_pend_updated_task_projection; [exact Hprevious|exact Hold|apply SemPendWaitSuspend].
Qed.

Lemma sem_pend_resume_client_projection : forall actor priority sg entry after tid old,
  kernel_client_step (task_resume_critical_client actor priority) sg entry after ->
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection entry.(TskState) after.(TskState) tid old.
Proof.
  intros actor priority sg entry after tid old [_ [result [_ Hstep]]] Hold.
  destruct (entry.(TskState).(prioTbl) priority).
  - destruct Hstep as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
  - destruct Hstep as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
  - destruct Hstep as [previous [Hprevious Hstep]].
    destruct (task_is_suspended previous.(stat)); destruct Hstep as [_ ->].
    + eapply sem_pend_updated_task_projection; [exact Hprevious|exact Hold|apply SemPendWaitResume].
    + apply sem_pend_task_projection_refl; exact Hold.
Qed.

Lemma sem_pend_tick_task_projection : forall sg entry selected previous tid old,
  entry.(TskState).(inUsedTaskStates) selected = Some previous ->
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection entry.(TskState) (tick_task_step sg selected previous entry).(TskState) tid old.
Proof.
  intros * Hprevious Hold; rewrite tick_task_step_task_state_eq by exact Hprevious.
  eapply sem_pend_updated_task_projection; [exact Hprevious|exact Hold|apply SemPendWaitTick].
Qed.

Lemma sem_pend_wake_task_projection : forall sg entry eid event selected previous result tid old,
  entry.(TskState).(inUsedTaskStates) selected = Some previous -> result <> PendTimeout ->
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection entry.(TskState)
    (event_wake_state sg entry eid event selected previous PendSem 0 result).(TskState) tid old.
Proof.
  intros * Hprevious Hresult Hold.
  eapply sem_pend_updated_task_projection; [exact Hprevious|exact Hold|apply SemPendWaitWake; exact Hresult].
Qed.

Lemma sem_pend_saved_sp_projection : forall entry selected previous sp tid old,
  entry.(TskState).(inUsedTaskStates) selected = Some previous ->
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection entry.(TskState)
    (glob_task_set_usedtask entry.(TskState) selected (task_set_saved_sp previous sp)) tid old.
Proof.
  intros; eapply sem_pend_updated_task_projection; [eassumption|eassumption|apply SemPendWaitSaveStack].
Qed.

Lemma sem_pend_task_projection_trans : forall before middle after tid old current,
  sem_pend_task_projection before middle tid old ->
  middle.(inUsedTaskStates) tid = Some current ->
  sem_pend_task_projection middle after tid current ->
  sem_pend_task_projection before after tid old.
Proof.
  intros * [found [Hfound Hfirst]] Hcurrent [last [Hlast Hsecond]].
  assert (found = current) by congruence; subst found.
  exists last; split; [exact Hlast|eapply rt_trans; eassumption].
Qed.

(** The actual scheduler SP store can target a retiring/free outgoing
    slot. It still frames every used waiting TCB on that branch; no
    used-only restriction is introduced for the scheduler. *)
Lemma sem_pend_sched_save_sp_projection : forall entry selected sp tid old,
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection entry.(TskState)
    (os_sched_save_current_sp entry selected sp).(TskState) tid old.
Proof.
  intros * Hold; unfold os_sched_save_current_sp.
  destruct (entry.(TskState).(inUsedTaskStates) selected) as [previous|] eqn:Hselected.
  - eapply sem_pend_saved_sp_projection; eassumption.
  - exists old; split; [exact Hold|apply rt_refl].
Qed.

Lemma sem_pend_time_tick_visit_projection : forall sg entry selected tid old,
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection entry.(TskState) (time_tick_visit sg entry selected).(TskState) tid old.
Proof.
  intros * Hold; unfold time_tick_visit.
  destruct (entry.(TskState).(inUsedTaskStates) selected) as [previous|] eqn:Hselected.
  - eapply sem_pend_tick_task_projection; eassumption.
  - apply sem_pend_task_projection_refl; exact Hold.
Qed.

Lemma sem_pend_time_tick_scan_projection : forall sg visited entry tid old,
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection entry.(TskState) (time_tick_scan sg entry visited).(TskState) tid old.
Proof.
  intros sg visited; induction visited as [|selected rest IH]; intros entry tid old Hold.
  - apply sem_pend_task_projection_refl; exact Hold.
  - change (sem_pend_task_projection entry.(TskState)
      (time_tick_scan sg (time_tick_visit sg entry selected) rest).(TskState) tid old).
    destruct (sem_pend_time_tick_visit_projection sg entry selected tid old Hold)
      as [current [Hcurrent Hfirst]].
    destruct (IH _ tid current Hcurrent) as [last [Hlast Hsecond]].
    exists last; split; [exact Hlast|eapply rt_trans; eassumption].
Qed.

Lemma sem_pend_time_tick_after_hook_projection : forall sg entry tid old,
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection entry.(TskState)
    (time_tick_serialized_after_hook sg entry).(TskState) tid old.
Proof.
  intros * Hold; unfold time_tick_serialized_after_hook; destruct (time_tick_process_tasks entry).
  - apply sem_pend_time_tick_scan_projection; exact Hold.
  - apply sem_pend_task_projection_refl; exact Hold.
Qed.

Lemma sem_pend_links_wait_effect : forall old next previous,
  sem_pend_wait_effect old (task_set_links old next previous).
Proof. intros; apply SemPendWaitOtherFields; repeat split; reflexivity. Qed.

Lemma sem_pend_profile_wait_effect : forall old switches cycles start stack_base used,
  sem_pend_wait_effect old (task_set_profile old switches cycles start stack_base used).
Proof. intros; apply SemPendWaitOtherFields; repeat split; reflexivity. Qed.

Lemma sem_pend_mutex_priority_task_projection : forall tasks selected previous priority tid old,
  tasks.(inUsedTaskStates) selected = Some previous ->
  tasks.(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection tasks
    (glob_task_set_usedtask tasks selected (mutex_priority_task previous priority)) tid old.
Proof.
  intros; eapply sem_pend_updated_task_projection;
    [eassumption|eassumption|apply task_change_priority_wait_effect].
Qed.

(** Lookup and selection are those of OS_EventTaskRdy, including a
    changed priority table after ChangePrio. Nothing assumes the old
    wait-list head or the pre-block priority remains selected. *)
Lemma sem_pend_event_task_rdy_projection : forall sg entry eid result priority after tid old,
  event_task_rdy sg entry eid PendSem 0 result = Some (priority, after) ->
  result <> PendTimeout -> entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection entry.(TskState) after.(TskState) tid old.
Proof.
  intros * Hstep Hresult Hold; unfold event_task_rdy in Hstep.
  destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
  destruct (entry.(TskState).(prioTbl) (event_wait_priority entry.(TskState) event))
    as [| |selected]; try discriminate.
  destruct (entry.(TskState).(inUsedTaskStates) selected) as [previous|] eqn:Hselected;
    [|discriminate].
  injection Hstep as Hpriority Hafter; subst after.
  eapply sem_pend_wake_task_projection; eassumption.
Qed.

Lemma sem_pend_event_broadcast_projection : forall sg eid result entry priorities after,
  event_broadcast sg eid PendSem 0 result entry priorities after -> result <> PendTimeout ->
  forall tid old, entry.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_task_projection entry.(TskState) after.(TskState) tid old.
Proof.
  intros sg eid result entry priorities after Hloop Hresult.
  induction Hloop as [entry event He Hempty|
    entry event priority middle priorities after He Hnonempty Hstep Htail IH]; intros tid old Hold.
  - apply sem_pend_task_projection_refl; exact Hold.
  - destruct (sem_pend_event_task_rdy_projection sg entry eid result priority middle tid old
      Hstep Hresult Hold) as [current [Hcurrent Hfirst]].
    destruct (IH tid current Hcurrent) as [last [Hlast Hsecond]].
    exists last; split; [exact Hlast|eapply rt_trans; eassumption].
Qed.

Lemma sem_pend_post_critical_projection : forall sg eid entry result after tid old,
  sem_post_critical sg eid entry result after ->
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection entry.(TskState) after.(TskState) tid old.
Proof.
  intros * [event [He Hstep]] Hold.
  destruct (Z.eqb (encode_event_wait_grp event.(waitList) entry.(TskState)) 0).
  - destruct Hstep as [fields [_ Hstep]].
    destruct (Z.ltb fields.(semCount) 65535); destruct Hstep as [_ ->];
      apply sem_pend_task_projection_refl; exact Hold.
  - destruct Hstep as [_ [priority Hstep]].
    eapply sem_pend_event_task_rdy_projection; [exact Hstep|discriminate|exact Hold].
Qed.

Lemma sem_pend_abort_critical_projection : forall sg eid opt entry result after tid old,
  event_pend_abort_critical sg eid PendSem opt entry result after ->
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection entry.(TskState) after.(TskState) tid old.
Proof.
  intros * [event [He Hstep]] Hold.
  destruct (Z.eqb (encode_event_wait_grp event.(waitList) entry.(TskState)) 0).
  - destruct Hstep as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
  - destruct (Z.eqb opt 1).
    + destruct Hstep as [priorities [Hloop _]].
      eapply sem_pend_event_broadcast_projection; [exact Hloop|discriminate|exact Hold].
    + destruct Hstep as [priority [Hstep _]].
      eapply sem_pend_event_task_rdy_projection; [exact Hstep|discriminate|exact Hold].
Qed.

(** OSTimeDlyResume, pinned Source/os_time.c:175--223. The argument guard
    is unconditional (unlike ChangePrio); there is no ISR/lock guard.
    This is the critical endpoint only. The bool is the source request
    for OS_Sched after Restore, not a context switch or return guarantee. *)
Definition time_delay_resume_argument_error (sg : StableGlobVars) (priority : Priority)
  : option OSErrCode :=
  if Z.leb sg.(osLowestPrio) priority then Some OS_ERR_PRIO_INVALID else None.

Definition time_delay_resume_state (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (selected : TaskID) (previous : TaskAbstractState) : UCOS2_Verify_State :=
  let next := sem_pend_delay_resume_task previous in
  replace_TskS (glob_task_set_usedtask entry.(TskState) selected next)
    (replace_SchedS (sched_wake_by_status sg entry.(TskState) entry.(SchedState)
      selected (encode_task_status next.(stat))) entry).

Definition time_delay_resume_critical (sg : StableGlobVars) (priority : Priority)
  : program UCOS2_Verify_State (OSErrCode * bool) :=
  fun entry result after => task_priority_in_range sg priority /\
    match entry.(TskState).(prioTbl) priority with
    | PTFree | PTReserved => result = (OS_ERR_TASK_NOT_EXIST, false) /\ after = entry
    | PTTask selected => exists previous,
      entry.(TskState).(inUsedTaskStates) selected = Some previous /\
      if Z.eqb previous.(dly) 0 then result = (OS_ERR_TIME_NOT_DLY, false) /\ after = entry
      else result = (OS_ERR_NONE, negb (task_is_suspended previous.(stat))) /\
        after = time_delay_resume_state sg entry selected previous
    end.

Lemma time_delay_resume_task_observations : forall previous,
  (sem_pend_delay_resume_task previous).(dly) = 0 /\
  (sem_pend_delay_resume_task previous).(statPend) =
    snd (task_status_timeout (encode_task_status previous.(stat))) /\
  (sem_pend_delay_resume_task previous).(eventPtr) = previous.(eventPtr) /\
  (sem_pend_delay_resume_task previous).(taskGeneration) = previous.(taskGeneration) /\
  task_is_suspended (sem_pend_delay_resume_task previous).(stat) = task_is_suspended previous.(stat).
Proof.
  intros; repeat split; try reflexivity; apply task_status_after_timeout_preserves_suspension.
Qed.

Lemma time_delay_resume_state_clock_frame : forall sg entry selected previous,
  (time_delay_resume_state sg entry selected previous).(TickState) = entry.(TickState) /\
  (time_delay_resume_state sg entry selected previous).(EventState) = entry.(EventState).
Proof. intros; split; reflexivity. Qed.

Lemma time_delay_resume_critical_wait_projection : forall sg priority entry result after tid old,
  time_delay_resume_critical sg priority entry result after ->
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection entry.(TskState) after.(TskState) tid old.
Proof.
  intros * [_ Hstep] Hold; destruct (entry.(TskState).(prioTbl) priority).
  - destruct Hstep as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
  - destruct Hstep as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
  - destruct Hstep as [previous [Hprevious Hstep]].
    destruct (Z.eqb previous.(dly) 0) eqn:Hdelay; destruct Hstep as [_ ->].
    + apply sem_pend_task_projection_refl; exact Hold.
    + eapply sem_pend_updated_task_projection; [exact Hprevious|exact Hold|].
      apply SemPendWaitDelayResume; apply Z.eqb_neq; exact Hdelay.
Qed.

Lemma time_delay_resume_task_image_eq : forall sg previous,
  task_tcb64_image sg (sem_pend_delay_resume_task previous) =
    tcb_write (tcb_write (tcb_write (task_tcb64_image sg previous) TCBDly (Some 0))
      TCBStat (Some (fst (task_status_timeout (encode_task_status previous.(stat))))))
      TCBStatPend (Some (encode_pend_status (snd (task_status_timeout (encode_task_status previous.(stat)))))).
Proof.
  intros sg previous; apply functional_extensionality; intros []; try reflexivity.
  change (Some (encode_task_status (task_status_after_timeout previous.(stat))) =
    Some (fst (task_status_timeout (encode_task_status previous.(stat))))).
  rewrite task_status_after_timeout_encoding; reflexivity.
Qed.

(** Source order, including the branch that does NOT write OSTCBStat. *)
Definition time_delay_resume_source_image (image : TCBCommonImage) (bits : Z) : TCBCommonImage :=
  let cleared := tcb_write image TCBDly (Some 0) in
  if task_status_has_pending bits then
    tcb_write (tcb_write cleared TCBStat (Some (task_status_clear_wait bits task_pend_any_mask)))
      TCBStatPend (Some (encode_pend_status PendTimeout))
  else tcb_write cleared TCBStatPend (Some (encode_pend_status PendOK)).

Lemma time_delay_resume_source_image_eq : forall sg previous,
  time_delay_resume_source_image (task_tcb64_image sg previous) (encode_task_status previous.(stat)) =
    task_tcb64_image sg (sem_pend_delay_resume_task previous).
Proof.
  intros; rewrite time_delay_resume_task_image_eq.
  unfold time_delay_resume_source_image, task_status_timeout.
  destruct (task_status_has_pending (encode_task_status previous.(stat))); [reflexivity|].
  apply functional_extensionality; intros []; reflexivity.
Qed.

(** Source-action wrappers for composing the concrete projections. These
    are not declarations of global registration or validity certificates.
    Suspend/Resume already have such certificates; ChangePrio still needs
    its bitmap/global invariant and whole-source binding. No wrapper
    assumes wait effects, endpoint validity, or a fresh current task. *)
Definition task_change_priority_source_client (actor : nat) (oldprio newprio : Priority)
  : KernelClientAction :=
  {| kernel_client_actor := Some actor; kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       task_change_priority_argument_error sg oldprio newprio = None /\
       exists code, task_change_priority_critical sg oldprio newprio before code after |}.

Definition sem_pend_tick_source_client (selected : TaskID) : KernelClientAction :=
  {| kernel_client_actor := None; kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after => exists previous,
       before.(TskState).(inUsedTaskStates) selected = Some previous /\
       after = tick_task_step sg selected previous before |}.

Definition sem_pend_post_source_client (actor : nat) (eid : EventID) : KernelClientAction :=
  {| kernel_client_actor := Some actor; kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after => exists result,
       sem_post_critical sg eid before result after |}.

Definition sem_pend_abort_source_client (actor : nat) (eid : EventID) (opt : Z) : KernelClientAction :=
  {| kernel_client_actor := Some actor; kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after => exists result,
       event_pend_abort_critical sg eid PendSem opt before result after |}.

Definition sem_pend_saved_sp_source_client (actor : nat) (selected : TaskID) (sp : Z)
  : KernelClientAction :=
  {| kernel_client_actor := Some actor; kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun _ before after => after = os_sched_save_current_sp before selected sp |}.

Definition sem_pend_delay_resume_source_client (actor : nat) (priority : Priority) : KernelClientAction :=
  {| kernel_client_actor := Some actor; kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       time_delay_resume_argument_error sg priority = None /\
       exists result, time_delay_resume_critical sg priority before result after |}.

(** A source family with proved wait projection, NOT the public allowed
    kernel environment. Full Pend must embed every enabled real client;
    this theorem does not exclude other clients by strengthening its API. *)
Inductive sem_pend_projected_source_client : KernelClientAction -> Prop :=
| SemPendSourceChangePriority : forall actor oldprio newprio,
    sem_pend_projected_source_client (task_change_priority_source_client actor oldprio newprio)
| SemPendSourceSuspend : forall actor priority,
    sem_pend_projected_source_client (task_suspend_critical_client actor priority)
| SemPendSourceResume : forall actor priority,
    sem_pend_projected_source_client (task_resume_critical_client actor priority)
| SemPendSourceTick : forall selected,
    sem_pend_projected_source_client (sem_pend_tick_source_client selected)
| SemPendSourcePost : forall actor eid,
    sem_pend_projected_source_client (sem_pend_post_source_client actor eid)
| SemPendSourceAbort : forall actor eid opt,
    sem_pend_projected_source_client (sem_pend_abort_source_client actor eid opt)
| SemPendSourceSavedSP : forall actor selected sp,
    sem_pend_projected_source_client (sem_pend_saved_sp_source_client actor selected sp)
| SemPendSourceDelayResume : forall actor priority,
    sem_pend_projected_source_client (sem_pend_delay_resume_source_client actor priority)
| SemPendSourceTaskEventRunningFrame : forall action,
    (forall sg before after, kernel_client_step action sg before after ->
      after.(TskState) = before.(TskState) /\
      after.(EventState) = before.(EventState) /\
      after.(SchedState).(isRunning) = before.(SchedState).(isRunning)) ->
    sem_pend_projected_source_client action
| SemPendSourceSchedulerInstall : forall external context outgoing incoming resumed,
    sem_pend_projected_source_client
      (os_sched_install_client external context outgoing incoming resumed).

(** These two registered C cuts really write only interrupt counters.
    The frame constructor consumes a proved property of the actual action;
    it grants no blanket preservation law to application/Extra clients.
    In particular publication is not a task-state frame operation. *)
Lemma sem_pend_int_enter_projected_source_client :
  sem_pend_projected_source_client
    (kernel_full_profile_cut_client KernelFullIntEnter).
Proof.
  apply SemPendSourceTaskEventRunningFrame.
  intros sg before after [_ ->]; repeat split; reflexivity.
Qed.

Lemma sem_pend_int_exit_counter_projected_source_client : forall observed_running,
  sem_pend_projected_source_client
    (kernel_full_profile_cut_client (KernelFullIntExitCounter observed_running)).
Proof.
  intros observed_running; apply SemPendSourceTaskEventRunningFrame.
  intros sg before after [_ ->]; repeat split; reflexivity.
Qed.

Lemma sem_pend_source_client_projection : forall action sg before after tid old,
  sem_pend_projected_source_client action -> kernel_client_step action sg before after ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros action sg before after tid old Hsource Hstep Hold.
  destruct Hsource as
    [actor oldprio newprio | actor priority | actor priority | selected |
     actor eid | actor eid opt | actor selected sp | actor priority | client Hframe |
     external context outgoing incoming resumed].
  - destruct Hstep as [_ [code Hstep]]; eapply task_change_priority_critical_wait_projection; eassumption.
  - eapply sem_pend_suspend_client_projection; eassumption.
  - eapply sem_pend_resume_client_projection; eassumption.
  - destruct Hstep as [previous [Hprevious ->]]; eapply sem_pend_tick_task_projection; eassumption.
  - destruct Hstep as [result Hstep]; eapply sem_pend_post_critical_projection; eassumption.
  - destruct Hstep as [result Hstep]; eapply sem_pend_abort_critical_projection; eassumption.
  - change (after = os_sched_save_current_sp before selected sp) in Hstep; subst after.
    apply sem_pend_sched_save_sp_projection; exact Hold.
  - destruct Hstep as [_ [result Hstep]]; eapply time_delay_resume_critical_wait_projection; eassumption.
  - destruct (Hframe sg before after Hstep) as [Htasks [Hevents Hrunning]].
    exists old; split; [rewrite Htasks; exact Hold|apply rt_refl].
  - pose proof (os_sched_install_client_state_frame external context outgoing incoming resumed
      sg before after Hstep) as [Htasks _].
    exists old; split; [rewrite Htasks; exact Hold|apply rt_refl].
Qed.

Lemma sem_pend_source_trace_projection : forall clients sg observer event_observer before stopped after,
  (forall action, clients action -> sem_pend_projected_source_client action) ->
  kernel_client_resource_trace clients sg observer event_observer before stopped after ->
  forall tid old, before.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros clients sg observer event_observer before stopped after Hclients Htrace.
  induction Htrace as [entry|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intros tid old Hold.
  - apply sem_pend_task_projection_refl; exact Hold.
  - destruct (sem_pend_source_client_projection action sg before middle tid old
      (Hclients action Hin) Hstep Hold) as [current [Hcurrent Hfirst]].
    destruct (IH tid current Hcurrent) as [last [Hlast Hsecond]].
    exists last; split; [exact Hlast|eapply rt_trans; eassumption].
Qed.

Lemma sem_pend_resumption_trace_projection : forall clients sg observer event_observer before stopped after,
  (forall action, clients action -> sem_pend_projected_source_client action) ->
  kernel_resumption_resource_trace clients sg observer event_observer before stopped after ->
  forall tid old, before.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros; eapply sem_pend_source_trace_projection; [eassumption| |eassumption].
  apply kernel_resumption_resource_trace_erases; eassumption.
Qed.

Lemma sem_pend_resumption_trace_preserves_continuation :
  forall clients sg observer event_observer before stopped after tid old eid generation,
  (forall action, clients action -> sem_pend_projected_source_client action) ->
  kernel_resumption_resource_trace clients sg observer event_observer before stopped after ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  exists current, after.(TskState).(inUsedTaskStates) tid = Some current /\
    sem_pend_wait_continuation eid generation current.
Proof.
  intros * Hclients Htrace Hold Hcont.
  destruct (sem_pend_resumption_trace_projection clients sg observer event_observer before stopped after
    Hclients Htrace tid old Hold) as [current [Hcurrent Heffects]].
  exists current; split; [exact Hcurrent|].
  eapply sem_pend_wait_trace_preserves_continuation; eassumption.
Qed.

(** Before the first Pend publication, suspension and resumption may
    change readiness, but these actual source effects do not introduce a
    new Event/Flag registration.  This is a one-task observation law,
    not a strengthening of KernelClientCertificate or an all-client rely. *)
Definition sem_pend_task_unregistered (node : TaskAbstractState) : Prop :=
  node.(eventPtr) = None /\ node.(eventMultiWaitEvents) = [] /\
  node.(tcbFlagNode) = 0.

Lemma sem_pend_event_task_rdy_call_frame : forall sg entry eid result priority after,
  event_task_rdy sg entry eid PendSem 0 result = Some (priority, after) ->
  after.(TskState).(taskLifecycle).(taskActiveOrder) = entry.(TskState).(taskLifecycle).(taskActiveOrder) /\
  after.(SchedState).(isRunning) = entry.(SchedState).(isRunning).
Proof.
  intros * Hstep; unfold event_task_rdy in Hstep.
  destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
  destruct (entry.(TskState).(prioTbl) (event_wait_priority entry.(TskState) event))
    as [| |selected]; try discriminate.
  destruct (entry.(TskState).(inUsedTaskStates) selected) as [previous|]; [|discriminate].
  injection Hstep as Hpriority Hafter; subst after; split; [reflexivity|].
  unfold event_wake_state, sched_wake_by_status;
    destruct (task_status_is_suspended _); reflexivity.
Qed.

Lemma sem_pend_event_broadcast_call_frame : forall sg eid result entry priorities after,
  event_broadcast sg eid PendSem 0 result entry priorities after ->
  after.(TskState).(taskLifecycle).(taskActiveOrder) = entry.(TskState).(taskLifecycle).(taskActiveOrder) /\
  after.(SchedState).(isRunning) = entry.(SchedState).(isRunning).
Proof.
  intros * Hloop; induction Hloop as [entry event He Hempty|
    entry event priority middle priorities after He Hnonempty Hstep Htail [Horder Hrunning]].
  - split; reflexivity.
  - destruct (sem_pend_event_task_rdy_call_frame sg entry eid result priority middle Hstep)
      as [HfirstOrder HfirstRunning].
    split; congruence.
Qed.

(** These fields really are framed by the already projected source
    family. Readiness and current-priority caches are intentionally not
    framed: Suspend/Resume/ChangePrio may change them. *)
Lemma sem_pend_source_client_call_frame : forall action sg before after,
  sem_pend_projected_source_client action -> kernel_client_step action sg before after ->
  after.(TskState).(taskLifecycle).(taskActiveOrder) = before.(TskState).(taskLifecycle).(taskActiveOrder) /\
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros action sg before after Hsource Hstep.
  destruct Hsource as
    [actor oldprio newprio | actor priority | actor priority | selected |
     actor eid | actor eid opt | actor selected sp | actor priority | client Hframe |
     external context outgoing incoming resumed].
  - destruct Hstep as [_ [code [_ Hstep]]].
    destruct (before.(TskState).(prioTbl) newprio).
    + destruct Hstep as [selected [_ [_ Hstep]]].
      destruct (before.(TskState).(prioTbl) selected).
      * destruct Hstep as [_ ->]; split; reflexivity.
      * destruct Hstep as [_ ->]; split; reflexivity.
      * destruct Hstep as [previous [_ [_ [_ [_ ->]]]]].
        unfold task_change_priority_state, task_change_priority_ready;
          destruct (Z.eqb _ 0); split; reflexivity.
    + destruct Hstep as [_ ->]; split; reflexivity.
    + destruct Hstep as [_ ->]; split; reflexivity.
  - destruct Hstep as [_ [result [cid [current [_ [_ [_ Hstep]]]]]]].
    destruct (before.(TskState).(prioTbl) (fst (task_suspend_selection sg priority current))).
    + destruct Hstep as [_ ->]; split; reflexivity.
    + destruct Hstep as [_ ->]; split; reflexivity.
    + destruct Hstep as [previous [_ [_ ->]]]; split; reflexivity.
  - destruct Hstep as [_ [result [_ Hstep]]].
    destruct (before.(TskState).(prioTbl) priority).
    + destruct Hstep as [_ ->]; split; reflexivity.
    + destruct Hstep as [_ ->]; split; reflexivity.
    + destruct Hstep as [previous [_ Hstep]].
      destruct (task_is_suspended previous.(stat)); destruct Hstep as [_ ->];
        split; try reflexivity.
      apply sched_resume_task_running_eq.
  - destruct Hstep as [previous [Hprevious ->]].
    split.
    + rewrite tick_task_step_task_state_eq by exact Hprevious; reflexivity.
    + unfold tick_task_step; destruct (Z.eqb previous.(dly) 0); [reflexivity|].
      destruct (Z.eqb (tick_task_update previous).(dly) 0); [|reflexivity].
      unfold sched_wake_by_status; destruct (task_status_is_suspended _); reflexivity.
  - destruct Hstep as [result [event [He Hstep]]].
    destruct (Z.eqb (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
    + destruct Hstep as [fields [_ Hstep]].
      destruct (Z.ltb fields.(semCount) 65535); destruct Hstep as [_ ->]; split; reflexivity.
    + destruct Hstep as [_ [priority Hstep]]; eapply sem_pend_event_task_rdy_call_frame; exact Hstep.
  - destruct Hstep as [result [event [He Hstep]]].
    destruct (Z.eqb (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
    + destruct Hstep as [_ ->]; split; reflexivity.
    + destruct (Z.eqb opt 1).
      * destruct Hstep as [priorities [Hloop _]]; eapply sem_pend_event_broadcast_call_frame; exact Hloop.
      * destruct Hstep as [priority [Hstep _]]; eapply sem_pend_event_task_rdy_call_frame; exact Hstep.
  - change (after = os_sched_save_current_sp before selected sp) in Hstep; subst after.
    unfold os_sched_save_current_sp; destruct (before.(TskState).(inUsedTaskStates) selected);
      split; reflexivity.
  - destruct Hstep as [_ [result [_ Hstep]]].
    destruct (before.(TskState).(prioTbl) priority).
    + destruct Hstep as [_ ->]; split; reflexivity.
    + destruct Hstep as [_ ->]; split; reflexivity.
    + destruct Hstep as [previous [_ Hstep]].
      destruct (Z.eqb previous.(dly) 0); destruct Hstep as [_ ->]; split; try reflexivity.
      unfold time_delay_resume_state, sched_wake_by_status;
        destruct (task_status_is_suspended _); reflexivity.
  - destruct (Hframe sg before after Hstep) as [Htasks [Hevents Hrunning]].
    split; [rewrite Htasks; reflexivity|exact Hrunning].
  - destruct (os_sched_install_client_state_frame external context outgoing incoming resumed
      sg before after Hstep) as [Htasks [Hlife [_ [Hrunning _]]]].
    split; [rewrite Hlife; reflexivity|exact Hrunning].
Qed.

Lemma sem_pend_resumption_trace_call_frame :
  forall clients sg observer event_observer before stopped after,
  (forall action, clients action -> sem_pend_projected_source_client action) ->
  kernel_resumption_resource_trace clients sg observer event_observer before stopped after ->
  after.(TskState).(taskLifecycle).(taskActiveOrder) = before.(TskState).(taskLifecycle).(taskActiveOrder) /\
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros * Hclients Htrace; apply kernel_resumption_resource_trace_erases in Htrace.
  induction Htrace as [state|action before middle after stopped Hin Hforeign Hevent Hstep Htail [Ho Hr]].
  - split; reflexivity.
  - destruct (sem_pend_source_client_call_frame action sg before middle
      (Hclients action Hin) Hstep) as [HfirstOrder HfirstRunning]; split; congruence.
Qed.

(** Running validity identifies Idle as the last active-list node.  The
    actual source family frames that order, so a live preceding task cannot
    turn into Idle merely because its priority changes. *)
Lemma sem_pend_call_frame_preserves_nonidle : forall sg before after tid old current,
  UCOS2_state_inv sg before -> UCOS2_state_inv sg after ->
  before.(SchedState).(isRunning) = true -> after.(SchedState).(isRunning) = true ->
  after.(TskState).(taskLifecycle).(taskActiveOrder) = before.(TskState).(taskLifecycle).(taskActiveOrder) ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  after.(TskState).(inUsedTaskStates) tid = Some current ->
  old.(curPrio) <> sg.(osLowestPrio) -> current.(curPrio) <> sg.(osLowestPrio).
Proof.
  intros sg before after tid old current Hbefore Hafter Hr0 Hr1 Horder Hold Hcurrent Hnonidle.
  pose proof Hbefore as [_ [[_ [Hactive _]] [_ [_ [_ [Hidle0 _]]]]]].
  pose proof Hafter as [_ [_ [_ [_ [_ [Hidle1 _]]]]]].
  destruct (Hidle0 Hr0) as [prefix [idle [node [Hlist [Hnode [Hprio Hprefix]]]]]].
  destruct (Hidle1 Hr1) as [prefix' [idle' [node' [Hlist' [Hnode' [Hprio' Hprefix']]]]]].
  assert (Hlists : prefix ++ [idle] = prefix' ++ [idle']) by congruence.
  apply app_inj_tail in Hlists; destruct Hlists as [Hp Hi]; subst prefix' idle'.
  destruct (task_live_has_one_occurrence before.(TskState) tid old Hactive Hold) as [Hin _].
  rewrite Hlist in Hin; apply in_app_or in Hin; destruct Hin as [Hin|[Heq|Hnil]].
  - exact (Hprefix' tid current Hin Hcurrent).
  - subst tid; assert (old = node) by congruence; subst old; contradiction.
  - contradiction.
Qed.

Lemma sem_pend_wait_effect_preserves_unregistered : forall before after,
  sem_pend_wait_effect before after ->
  sem_pend_task_unregistered before -> sem_pend_task_unregistered after.
Proof.
  intros before after Hstep [He [Hm Hf]]; destruct Hstep;
    unfold sem_pend_task_unregistered.
  - unfold tick_task_update; destruct (dly t =? 0);
      [repeat split; assumption|].
    destruct (dly t - 1 =? 0); repeat split; assumption.
  - repeat split; assumption || reflexivity.
  - repeat split; assumption.
  - repeat split; assumption.
  - repeat split; assumption.
  - destruct H as [_ [_ [_ [_ [_ [Hptr [Hmulti Hflag]]]]]]].
    rewrite Hptr, Hmulti, Hflag; repeat split; assumption.
  - repeat split; assumption.
Qed.

Lemma sem_pend_wait_trace_preserves_unregistered : forall before after,
  clos_refl_trans TaskAbstractState sem_pend_wait_effect before after ->
  sem_pend_task_unregistered before -> sem_pend_task_unregistered after.
Proof.
  intros before after Htrace; induction Htrace; intro Hbefore.
  - eapply sem_pend_wait_effect_preserves_unregistered; eassumption.
  - exact Hbefore.
  - apply IHHtrace2, IHHtrace1; exact Hbefore.
Qed.

Lemma sem_pend_resumption_trace_preserves_unregistered :
  forall clients sg observer event_observer before stopped after tid old,
  (forall action, clients action -> sem_pend_projected_source_client action) ->
  kernel_resumption_resource_trace clients sg observer event_observer before stopped after ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_unregistered old ->
  exists current, after.(TskState).(inUsedTaskStates) tid = Some current /\
    sem_pend_task_unregistered current.
Proof.
  intros * Hclients Htrace Hold Hnone.
  destruct (sem_pend_resumption_trace_projection clients sg observer event_observer
    before stopped after Hclients Htrace tid old Hold) as [current [Hcurrent Heffects]].
  exists current; split; [exact Hcurrent|].
  eapply sem_pend_wait_trace_preserves_unregistered; eassumption.
Qed.

Lemma sem_pend_resumption_trace_preserves_call_fields :
  forall clients sg observer event_observer before stopped after tid old,
  (forall action, clients action -> sem_pend_projected_source_client action) ->
  kernel_resumption_resource_trace clients sg observer event_observer before stopped after ->
  UCOS2_state_inv sg before -> UCOS2_state_inv sg after ->
  before.(SchedState).(isRunning) = true ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  old.(curPrio) <> sg.(osLowestPrio) -> sem_pend_task_unregistered old ->
  after.(SchedState).(isRunning) = true /\
  exists current, after.(TskState).(inUsedTaskStates) tid = Some current /\
    current.(curPrio) <> sg.(osLowestPrio) /\ sem_pend_task_unregistered current.
Proof.
  intros * Hclients Htrace Hbefore Hafter Hrunning Hold Hnonidle Hnone.
  destruct (sem_pend_resumption_trace_call_frame clients sg observer event_observer
    before stopped after Hclients Htrace) as [Horder Hr].
  assert (HrunningAfter : after.(SchedState).(isRunning) = true) by congruence.
  split; [exact HrunningAfter|].
  destruct (sem_pend_resumption_trace_preserves_unregistered clients sg observer event_observer
    before stopped after tid old Hclients Htrace Hold Hnone) as [current [Hcurrent Hfields]].
  exists current; split; [exact Hcurrent|]. split; [|exact Hfields].
  exact (sem_pend_call_frame_preserves_nonidle sg before after tid old current
    Hbefore Hafter Hrunning HrunningAfter Horder Hold Hcurrent Hnonidle).
Qed.

(** Actual OS_Sched stages: prefix scheduler bytes, outgoing SP, a
    concrete classified hook, parked-stack installation, foreign steps,
    and original-return outcome. This establishes only the TCB projection;
    it does not establish the separate CPU/stack/source binding or fresh
    current/ready facts needed to prove that a source call is safe. *)
Lemma sem_pend_sched_switch_source_projection :
  forall external sg entry context installed tid old,
  sem_pend_projected_source_client external.(os_sched_hook_action) ->
  os_sched_switch_source external sg entry context installed ->
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection entry.(TskState) installed.(TskState) tid old.
Proof.
  intros * Hhook [_ [sp [saved [hooked [incoming [resumed [Hsave [Hstep [_ ->]]]]]]]]] Hold.
  destruct (sem_pend_sched_save_sp_projection (os_sched_prefix_state entry)
    context.(os_sched_call_stack).(stackLeaseSlot) sp tid old Hold)
    as [current [Hcurrent Hfirst]].
  destruct (sem_pend_source_client_projection external.(os_sched_hook_action) sg _ hooked
    tid current Hhook Hstep Hcurrent) as [last [Hlast Hsecond]].
  exists last; split; [exact Hlast|eapply rt_trans; eassumption].
Qed.

Lemma sem_pend_sched_return_projection : forall external critical sg entry context returned final tid old,
  (forall action, critical.(critical_region_clients) action -> sem_pend_projected_source_client action) ->
  sem_pend_projected_source_client external.(os_sched_hook_action) ->
  os_sched_c_return external critical sg entry context returned final ->
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection entry.(TskState) final.(TskState) tid old.
Proof.
  intros * Hclients Hhook Hreturn Hold; unfold os_sched_c_return in Hreturn.
  destruct (os_sched_requests_switch entry).
  - destruct Hreturn as [installed [Hsource [[stopped [Htrace Hnormal]] Hreturned]]].
    destruct (sem_pend_sched_switch_source_projection external sg entry context installed tid old
      Hhook Hsource Hold) as [current [Hcurrent Hfirst]].
    destruct (sem_pend_source_trace_projection _ sg context.(os_sched_call_invocation) None
      installed stopped final Hclients Htrace tid current Hcurrent) as [last [Hlast Hsecond]].
    exists last; split; [exact Hlast|eapply rt_trans; eassumption].
  - destruct Hreturn as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
Qed.
