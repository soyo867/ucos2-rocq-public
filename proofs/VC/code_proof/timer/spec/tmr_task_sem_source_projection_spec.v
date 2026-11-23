Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_idle_guard_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.lib.sem.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Import TaskStateDef ListNotations.
Local Open Scope Z_scope.

(** Observations of the same live Sem waiter under the actual Task source
    actions.  The original registry and trace remain unchanged.  Creation
    transports an existing TCB; TaskLifecycle here is not task deletion.
    Post, Abort, Tick and Resume retain their real effects. *)
Lemma tmr_task_sem_projection_map_eq : forall before after tid old,
  after.(inUsedTaskStates) = before.(inUsedTaskStates) ->
  before.(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection before after tid old.
Proof.
  intros before after tid old Hmap Hold; exists old; split.
  - rewrite Hmap; exact Hold.
  - apply rt_refl.
Qed.

Lemma tmr_task_sem_projection_trans : forall before middle after tid old,
  sem_pend_task_projection before middle tid old ->
  (forall current, middle.(inUsedTaskStates) tid = Some current ->
    sem_pend_task_projection middle after tid current) ->
  sem_pend_task_projection before after tid old.
Proof.
  intros before middle after tid old [current [Hcurrent Hfirst]] Hnext.
  destruct (Hnext current Hcurrent) as [last [Hlast Hsecond]].
  exists last; split; [exact Hlast|eapply rt_trans; eassumption].
Qed.

Lemma tmr_task_sem_links_equal_wait_effect : forall before after,
  task_set_links after None None = task_set_links before None None ->
  sem_pend_wait_effect before after.
Proof.
  intros before after Hfields; apply SemPendWaitOtherFields.
  unfold sem_pend_wait_fields_equal; repeat split;
    first [exact (f_equal taskID Hfields) | exact (f_equal taskGeneration Hfields) |
      exact (f_equal stat Hfields) | exact (f_equal statPend Hfields) |
      exact (f_equal dly Hfields) | exact (f_equal eventPtr Hfields) |
      exact (f_equal eventMultiWaitEvents Hfields) | exact (f_equal tcbFlagNode Hfields)].
Qed.

Lemma tmr_task_sem_creation_projection : forall action sg before after tid old,
  UCOS2_state_inv sg before ->
  kernel_client_step (task_creation_client action) sg before after ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros action sg before after tid old Hvalid [Hguard [_ ->]] Hold.
  destruct action as [priority entry slot rest image|priority entry allocation image|
    priority invocation node|invocation].
  - eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - pose proof (task_commit_identity_private before.(TskState) priority invocation node
      (proj1 Hguard)) as Hprivate.
    pose proof (proj1 (task_private_excludes_public sg before.(TskState) node.(taskID)
      (proj1 (proj1 (proj2 Hvalid))) Hprivate)) as Hfresh.
    destruct (task_commit_transports_old_fields before.(TskState) priority invocation node
      tid old Hfresh Hold) as [current [Hcurrent Hfields]].
    exists current; split; [exact Hcurrent|].
    apply rt_step, tmr_task_sem_links_equal_wait_effect; exact Hfields.
  - eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
Qed.

Lemma tmr_task_sem_nontimer_projection : forall action sg before after tid old,
  tmr_task_nontimer_source_client action -> UCOS2_state_inv sg before ->
  kernel_client_step action sg before after ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros action sg before after tid old Hsource Hvalid; destruct Hsource; intros Hstep Hold.
  - eapply tmr_task_sem_creation_projection; eassumption.
  - destruct (task_create_stack_publication_raw_projection sg publication before after Hstep)
      as [Hraw ->].
    change (sem_pend_task_projection before.(TskState)
      (task_create_stack_publication_raw_state sg publication before).(TskState) tid old).
    eapply tmr_task_sem_creation_projection; eassumption.
  - destruct Hstep as [_ ->]; eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - destruct Hstep as [_ ->]; eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - destruct Hstep as [_ ->]; eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - destruct Hstep as [_ [result Hstep]]. unfold event_create_allocate_critical in Hstep.
    destruct before.(EventState).(unUsedEventStates).
    + destruct Hstep as [_ ->]; eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
    + destruct Hstep as [image [_ [_ ->]]];
        eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - destruct Hstep as [_ ->]; eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - destruct Hstep as [_ [_ ->]]; eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - destruct Hstep as [_ [_ [_ [_ [result [a [Ha Hstep]]]]]]].
    destruct free; destruct Hstep as [_ ->];
      (eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold]).
  - destruct Hstep as [_ [_ [_ [_ ->]]]];
      eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - eapply sem_pend_resume_client_projection; eassumption.
  - destruct Hstep as [event [_ [_ [node [fields [_ [_ [_ ->]]]]]]]].
    unfold sem_pend_task_projection.
    exists old; split.
    + change ((if Z.ltb 0 fields.(semCount)
          then sem_count_update_state before eid node (fields.(semCount) - 1)
          else before).(TskState).(inUsedTaskStates) tid = Some old).
      destruct (Z.ltb 0 fields.(semCount)); exact Hold.
    + apply rt_refl.
Qed.

Lemma tmr_task_sem_change_prio_projection : forall sg requested priority before code after tid old,
  task_change_prio_critical sg requested priority before code after ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros sg requested priority before code after tid old Hsource Hold.
  unfold task_change_prio_critical in Hsource.
  destruct (before.(TskState).(prioTbl) priority).
  - destruct Hsource as [selected [Hselection Hsource]].
    unfold task_change_prio_selected_effect in Hsource.
    lazymatch type of Hsource with
    | (if ?condition then _ else _) => destruct condition in Hsource
    end.
    + destruct Hsource as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
    + destruct (before.(TskState).(prioTbl) selected) as [| |slot].
      * destruct Hsource as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
      * destruct Hsource as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
      * destruct Hsource as [node [Hnode [_ ->]]].
        eapply task_change_priority_state_wait_projection; eassumption.
  - destruct Hsource as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
  - destruct Hsource as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
Qed.

Lemma tmr_task_sem_profile_projection : forall cut sg before after tid old,
  kernel_client_step (kernel_full_profile_cut_client cut) sg before after ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros cut sg before after tid old [Hinput ->] Hold; destruct cut as [|running|slot node].
  - eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - destruct Hinput as [_ Hnode].
    eapply sem_pend_updated_task_projection; [exact Hnode|exact Hold|].
    apply SemPendWaitOtherFields; repeat split; reflexivity.
Qed.

(** FlagTaskRdy cannot select this Sem waiter.  This follows from the
    actual linked Flag node and the existing cross-module invariant, not
    from a blanket promise that Flag operations preserve every TCB. *)
Lemma tmr_task_sem_flag_ready_projection : forall sg before pointer bits result schedule after
  tid old eid generation,
  UCOS2_state_inv sg before ->
  flag_task_rdy sg before pointer bits result = Some (schedule, after) ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros sg before pointer bits result schedule after tid old eid generation
    Hvalid Hstep Hold [_ [_ [Hnull _]]].
  destruct (flag_task_rdy_result sg before pointer bits result schedule after Hstep)
    as [waiter [flags [node [Hunlink [Hnode [-> Hschedule]]]]]].
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hunlink)) as Hwaiter.
  pose proof Hvalid as [_ [_ [_ [_ [Hcross _]]]]].
  assert (Hflags : task_flag_waiter_consistency sg before.(TskState) before.(FlagState)).
  { unfold cross_module_consistency in Hcross; tauto. }
  assert (Hother : tid <> waiter.(flagTask)).
  { intro Heq; apply (task_flag_null_pointer_has_no_waiter sg before.(TskState)
      before.(FlagState) tid old Hflags Hold Hnull).
    exists pointer, waiter; split; [exact Hwaiter|symmetry; exact Heq]. }
  exists old; split; [|apply rt_refl].
  change ((if Z.eqb tid waiter.(flagTask) then Some (task_flag_wake node bits result)
    else before.(TskState).(inUsedTaskStates) tid) = Some old).
  lazymatch goal with
  | |- context [if ?condition then _ else _] => destruct condition eqn:Hsame
  end.
  - apply Z.eqb_eq in Hsame; contradiction.
  - exact Hold.
Qed.

Lemma tmr_task_sem_tick_projection : forall sg cut before after tid old,
  tmr_task_tick_cut_source sg cut before after ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros sg cut before after tid old; destruct cut; cbn [tmr_task_tick_cut_source]; intros Hstep Hold.
  - subst after; unfold time_tick_clock_step_state; destruct (tick_step_advance _ _);
      eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - subst after; apply sem_pend_time_tick_after_hook_projection; exact Hold.
  - destruct Hstep as [state error Herror|state event node error Hargument Hpointer Hlookup Htype|
      state event node actual current Hargument Hpointer Hlookup Htype Hcritical];
      try (apply sem_pend_task_projection_refl; exact Hold).
    eapply sem_pend_post_critical_projection; eassumption.
Qed.

Lemma tmr_task_sem_suspend_projection : forall actor source_sg priority result entry returned
  sg before after tid old,
  kernel_client_step (tmr_task_suspend_call_client actor source_sg priority result entry returned)
    sg before after ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros actor source_sg priority result entry returned sg before after tid old
    [_ [_ [_ [Hargument Hcritical]]]] Hold.
  destruct (task_suspend_idle_guard_original_or_unchanged _ _ _ _ _ Hcritical) as [->|Horiginal].
  - apply sem_pend_task_projection_refl; exact Hold.
  - eapply (sem_pend_suspend_client_projection actor priority sg before after tid old).
    + split; [exact Hargument|exists result; exact Horiginal].
    + exact Hold.
Qed.

(** Actual EventTaskRdy callers supply a nonempty canonical wait list,
    its kind and a Post/Abort result.  The raw source constructor currently
    drops those arguments' provenance; the theorem below keeps it explicit
    at this single call, not as a future-endpoint assumption. *)
Lemma tmr_task_sem_linked_clear_status_eq : forall old kind,
  task_linked_wait_phase old PendSem -> task_linked_wait_phase old kind ->
  task_clear_pending_status old.(stat) kind = task_clear_pending_status old.(stat) PendSem.
Proof.
  intros old kind Hsem Hkind.
  destruct Hsem as [Hsem|[Hzero _]].
  - destruct Hkind as [Hkind|[Hzero _]].
    + assert (Hmask : task_pend_mask kind = task_pend_mask PendSem) by congruence.
      destruct kind; cbn [task_pend_mask] in Hmask; try discriminate; reflexivity.
    + rewrite Hzero in Hsem; discriminate.
  - rewrite !task_clear_pending_status_none by exact Hzero; reflexivity.
Qed.

Lemma tmr_task_sem_wake_projection : forall old kind message result eid generation,
  sem_pend_wait_continuation eid generation old ->
  task_linked_wait_phase old kind -> old.(eventPtr) <> None -> result <> PendTimeout ->
  clos_refl_trans TaskAbstractState sem_pend_wait_effect old
    (task_event_wake_single old kind message result).
Proof.
  intros old kind message result eid generation [_ [_ [_ [Hlinked|Hreleased]]]]
    Hkind Hpointer Hresult; [|exfalso; apply Hpointer; exact (proj1 Hreleased)].
  destruct Hlinked as [_ Hsem].
  eapply rt_trans with (y := task_event_wake_single old PendSem 0 result).
  - apply rt_step, SemPendWaitWake; exact Hresult.
  - apply rt_step, SemPendWaitOtherFields.
    unfold sem_pend_wait_fields_equal; repeat split; try reflexivity.
    apply tmr_task_sem_linked_clear_status_eq; assumption.
Qed.

Lemma tmr_task_sem_event_ready_projection : forall sg before event node head tail
  kind message result priority after tid old eid generation,
  valid_stable_glob_vars sg -> task_in_range sg before.(TskState) ->
  event_wait_entry_consistency sg before.(TskState) event node ->
  before.(EventState).(inUsedEventStates) event = Some node ->
  node.(waitList) = head :: tail -> event_type_to_pend_type node.(eventType) = Some kind ->
  result <> PendTimeout ->
  event_task_rdy sg before event kind message result = Some (priority, after) ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros sg before event node head tail kind message result priority after tid old eid generation
    Hsg Htasks Hentry Hnode Hlist Hkind Hresult Hstep Hold Hcont.
  assert (Hin : In head node.(waitList)) by (rewrite Hlist; left; reflexivity).
  destruct (event_waiter_task_fields sg before.(TskState) event node head Hentry Hin)
    as [selected [actual [Hselected [Hactual [Hpointer [Hmulti Hphase]]]]]].
  assert (actual = kind) by congruence; subst actual.
  rewrite (event_task_rdy_selects_waiter sg before event node head tail selected kind message result
    Hsg Htasks Hentry Hnode Hlist Hselected) in Hstep.
  injection Hstep as Hpriority Hafter; subst after.
  destruct (Z.eq_dec tid head) as [->|Hother].
  - assert (selected = old) by congruence; subst selected.
    exists (task_event_wake_single old kind message result); split.
    + cbn [event_wake_state replace_SchedS replace_EventS replace_TskS TskState
        glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
    + eapply tmr_task_sem_wake_projection; [exact Hcont|exact Hphase|congruence|exact Hresult].
  - exists old; split; [|apply rt_refl].
    cbn [event_wake_state replace_SchedS replace_EventS replace_TskS TskState
      glob_task_set_usedtask inUsedTaskStates].
    rewrite (proj2 (Z.eqb_neq _ _) Hother); exact Hold.
Qed.

Lemma tmr_task_sem_mutex_prepare_projection : forall sg mutex before after tid old,
  mutex_del_prepare sg mutex before after ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros sg mutex before after tid old Hprepare Hold; unfold mutex_del_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis));
    [subst; apply sem_pend_task_projection_refl; exact Hold|].
  destruct mutex.(mfOwner) as [owner|].
  - destruct Hprepare as [node [priority [Hnode [_ ->]]]].
    unfold mutex_del_owner_priority_state; destruct Z.eq_dec.
    + eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
    + eapply sem_pend_updated_task_projection; [exact Hnode|exact Hold|].
      apply task_change_priority_wait_effect.
  - subst; eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
Qed.

(** Mutex deletion has an existing phase owner after releasing its PCP.
    Its proved ranges and actual wake decomposition are used here; no
    closed global invariant is imposed on that intermediate state. *)
Lemma tmr_task_sem_mutex_broadcast_projection : forall sg event mutex before priorities after,
  event_broadcast sg event PendMutex 0 PendAbort before priorities after ->
  mutex_del_wake_state_inv sg event mutex before ->
  forall tid old eid generation,
    before.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros sg event mutex before priorities after Hloop.
  induction Hloop as [before node Hnode Hzero|
    before node priority middle priorities after Hnode Hnonzero Hstep Hloop IH];
    intros Hphase tid old eid generation Hold Hcont.
  - apply sem_pend_task_projection_refl; exact Hold.
  - pose proof (mutex_del_wake_state_ranges sg event mutex before Hphase)
      as [Hprofile [Htasks [_ Hevents]]].
    pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
    assert (Hkind : event_type_to_pend_type node.(eventType) = Some PendMutex).
    { destruct Hphase as [actual [Hactual [Htype _]]].
      assert (actual = node) by congruence; subst actual; rewrite Htype; reflexivity. }
    destruct node.(waitList) as [|head tail] eqn:Hlist;
      [exfalso; apply Hnonzero; reflexivity|].
    destruct (tmr_task_sem_event_ready_projection sg before event node head tail
      PendMutex 0 PendAbort priority middle tid old eid generation
      (proj1 Hprofile) Htasks (Hentries event node Hnode) Hnode Hlist Hkind
      ltac:(discriminate) Hstep Hold Hcont) as [current [Hcurrent Hfirst]].
    destruct (mutex_del_wake_decompose sg event mutex before node priority middle
      Hphase Hnode ltac:(rewrite Hlist; exact Hnonzero) Hstep)
      as [selected [previous [_ [_ [_ [_ Hmiddle]]]]]].
    assert (Hcontinue : sem_pend_wait_continuation eid generation current).
    { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
    destruct (IH Hmiddle tid current eid generation Hcurrent Hcontinue) as [last [Hlast Hsecond]].
    exists last; split; [exact Hlast|eapply rt_trans; eassumption].
Qed.

Lemma tmr_task_sem_mutex_delete_projection : forall sg event option before result after tid old eid generation,
  UCOS2_state_inv sg before ->
  CriticalComponent.mutex_del_no_pend_critical_call_guard sg event before ->
  mutex_del_critical sg event option before result after ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros sg event option before result after tid old eid generation Hvalid Hguard
    [node [mutex [Hnode [Htype [Hfields Hsource]]]]] Hold Hcont.
  assert (Hprepare_phase : forall prepared, mutex_del_prepare sg mutex before prepared ->
    mutex_del_wake_state_inv sg event mutex prepared).
  { intros prepared Hprepare.
    destruct Hguard as [actual [actual_mutex [[Hentry [Hlookup [Hactual_type [Hactual_fields Huse]]]] Hpointer]]].
    unfold mutex_query_lookup in Hlookup.
    assert (actual = node) by congruence; subst actual.
    assert (actual_mutex = mutex) by congruence; subst actual_mutex.
    eapply mutex_del_prepare_under_owner_use; eassumption. }
  destruct (Z.eq_dec option 0).
  - destruct (Z.eq_dec (encode_event_wait_grp node.(waitList) before.(TskState)) 0).
    + destruct Hsource as [prepared [Hprepare [-> Hresult]]].
      change (sem_pend_task_projection before.(TskState) prepared.(TskState) tid old).
      eapply tmr_task_sem_mutex_prepare_projection; eassumption.
    + destruct Hsource as [-> Hresult]; apply sem_pend_task_projection_refl; exact Hold.
  - destruct (Z.eq_dec option 1).
    + destruct Hsource as [prepared [priorities [drained [Hprepare [Hbroadcast [-> Hresult]]]]]].
      change (sem_pend_task_projection before.(TskState) drained.(TskState) tid old).
      destruct (tmr_task_sem_mutex_prepare_projection sg mutex before prepared tid old Hprepare Hold)
        as [current [Hcurrent Hfirst]].
      assert (Hcontinue : sem_pend_wait_continuation eid generation current).
      { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
      destruct (tmr_task_sem_mutex_broadcast_projection sg event mutex prepared priorities drained
        Hbroadcast (Hprepare_phase prepared Hprepare) tid current eid generation Hcurrent Hcontinue)
        as [last [Hlast Hsecond]].
      exists last; split; [exact Hlast|eapply rt_trans; eassumption].
    + destruct Hsource as [-> Hresult]; apply sem_pend_task_projection_refl; exact Hold.
Qed.

Lemma tmr_task_sem_critical_projection : forall action sg before after tid old eid generation,
  tmr_task_critical_source_client action -> UCOS2_state_inv sg before ->
  kernel_client_step action sg before after ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros action sg before after tid old eid generation Hsource Hvalid;
    destruct Hsource; intros Hstep Hold Hcont.
  - destruct Hstep as [Hguard [result [code [request [error [scheduled [Hcritical Hencoding]]]]]]].
    eapply tmr_task_sem_mutex_delete_projection; eassumption.
  - destruct Hstep as [result [code [request Hsource]]].
    destruct Hsource as [result code request checkpoint Hguard Hobservation|kind Htype Hnotmutex].
    + destruct Hobservation as [error [scheduled [Hcritical Hencoding]]].
      eapply tmr_task_sem_mutex_delete_projection; eassumption.
    + apply sem_pend_task_projection_refl; exact Hold.
  - destruct Hstep as [_ [error Hsource]].
    eapply tmr_task_sem_change_prio_projection; eassumption.
Qed.

(** The only information missing from the raw EventReady source wrapper
    is local to that actual call: the nonempty queue whose bitmap is read,
    its typed wake operation, and the Post/Abort result.  The internal C
    helper itself accepts a wider byte domain; its real callers must supply
    these facts.  This is not implied by source coverage alone. *)
Definition tmr_task_sem_event_ready_call_input (sg : StableGlobVars) before event kind result : Prop :=
  exists node head tail,
    before.(EventState).(inUsedEventStates) event = Some node /\
    node.(waitList) = head :: tail /\
    event_type_to_pend_type node.(eventType) = Some kind /\ result <> PendTimeout.

Lemma tmr_task_sem_event_ready_call_input_from_c_entry :
  forall sg before event node selected previous kind result,
  event_task_rdy_entry sg before.(TskState) event node selected previous ->
  before.(EventState).(inUsedEventStates) event = Some node ->
  event_type_to_pend_type node.(eventType) = Some kind -> result <> PendTimeout ->
  tmr_task_sem_event_ready_call_input sg before event kind result.
Proof.
  intros sg before event node selected previous kind result
    [_ [_ [_ [_ [_ [Hhead _]]]]]] Hnode Hkind Hresult.
  destruct node.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
  exists node, head, tail; repeat split; assumption.
Qed.

Lemma tmr_task_sem_event_ready_call_input_from_group :
  forall sg before event node kind result,
  before.(EventState).(inUsedEventStates) event = Some node ->
  encode_event_wait_grp node.(waitList) before.(TskState) <> 0 ->
  event_type_to_pend_type node.(eventType) = Some kind -> result <> PendTimeout ->
  tmr_task_sem_event_ready_call_input sg before event kind result.
Proof.
  intros sg before event node kind result Hnode Hgroup Hkind Hresult.
  destruct node.(waitList) as [|head tail] eqn:Hlist;
    [exfalso; apply Hgroup; reflexivity|].
  exists node, head, tail; repeat split; assumption.
Qed.

Lemma tmr_task_sem_event_ready_call_projection : forall sg before after actor event kind message result
  tid old eid generation,
  UCOS2_state_inv sg before ->
  tmr_task_sem_event_ready_call_input sg before event kind result ->
  kernel_client_step (event_task_rdy_source_client actor event kind message result) sg before after ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros sg before after actor event kind message result tid old eid generation
    [Hprofile [Htasks [_ [Hevents _]]]]
    [node [head [tail [Hnode [Hlist [Hkind Hresult]]]]]] [priority Hstep] Hold Hcont.
  pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  eapply tmr_task_sem_event_ready_projection;
    [exact (proj1 Hprofile)|exact Htasks|exact (Hentries event node Hnode)|
     exact Hnode|exact Hlist|exact Hkind|exact Hresult|exact Hstep|exact Hold|exact Hcont].
Qed.

Definition tmr_task_sem_event_ready_call action sg before after : Prop :=
  exists actor event kind message result,
    action = event_task_rdy_source_client actor event kind message result /\
    kernel_client_step (event_task_rdy_source_client actor event kind message result) sg before after.

Lemma tmr_task_sem_scheduler_projection_or_event_call :
  forall external action sg before after tid old eid generation,
  tmr_task_scheduler_source_client external action -> UCOS2_state_inv sg before ->
  kernel_client_step action sg before after ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old \/
    tmr_task_sem_event_ready_call action sg before after.
Proof.
  intros external action sg before after tid old eid generation Hsource Hvalid.
  destruct Hsource as [action Hnontimer|cut|actor requested priority|actor pointer bits result|
    actor event kind message result|slot previous|context outgoing incoming resumed];
    intros Hstep Hold Hcont.
  - left; eapply tmr_task_sem_nontimer_projection; eassumption.
  - left; eapply tmr_task_sem_profile_projection; eassumption.
  - left; destruct Hstep as [code Hstep]; eapply tmr_task_sem_change_prio_projection; eassumption.
  - left; destruct Hstep as [schedule Hstep]; eapply tmr_task_sem_flag_ready_projection; eassumption.
  - right; exists actor, event, kind, message, result; split; [reflexivity|exact Hstep].
  - left; destruct Hstep as [Hprevious ->]; eapply sem_pend_tick_task_projection; eassumption.
  - left; eapply sem_pend_source_client_projection;
      [apply SemPendSourceSchedulerInstall|exact Hstep|exact Hold].
Qed.

(** Exhaustive source split.  No constructor is removed, and no new
    wait-preservation field is inserted into KernelClientCertificate.
    The disjunction identifies the one raw wrapper requiring its actual
    caller producer; all other constructors yield the effects directly. *)
Lemma tmr_task_sem_source_projection_or_event_call :
  forall external action sg before after tid old eid generation,
  tmr_task_source_client external action -> UCOS2_state_inv sg before ->
  kernel_client_step action sg before after ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old \/
    tmr_task_sem_event_ready_call action sg before after.
Proof.
  intros external action sg before after tid old eid generation Hsource Hvalid.
  destruct Hsource as [action Hscheduler|action Hsem|action Hcritical|actor cut|actor cut|
    actor source_sg cut entry timers|actor event option result|
    actor source_sg priority result entry returned]; intros Hstep Hold Hcont.
  - eapply tmr_task_sem_scheduler_projection_or_event_call; eassumption.
  - left; eapply sem_pend_source_client_projection;
      [apply tmr_task_sem_source_client_wait_projection; exact Hsem|exact Hstep|exact Hold].
  - left; eapply tmr_task_sem_critical_projection; eassumption.
  - left; exact (tmr_task_sem_tick_projection sg cut before after tid old Hstep Hold).
  - left; destruct Hstep as [timers [_ ->]];
      eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - left; destruct Hstep as [_ [_ [_ ->]]];
      eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - left; destruct Hstep as [node [_ [_ Habort]]].
    eapply sem_pend_abort_critical_projection; eassumption.
  - left; eapply tmr_task_sem_suspend_projection; eassumption.
Qed.

Lemma tmr_task_sem_registered_source_projection :
  forall external critical sg before after action tid old eid generation,
  tmr_task_registered_source_coverage external critical ->
  critical.(critical_region_clients) action -> UCOS2_state_inv sg before ->
  kernel_client_step action sg before after ->
  (forall actor event kind message result,
    action = event_task_rdy_source_client actor event kind message result ->
    tmr_task_sem_event_ready_call_input sg before event kind result) ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros external critical sg before after action tid old eid generation
    Hcoverage Hin Hvalid Hstep Hcalls Hold Hcont.
  destruct (tmr_task_sem_source_projection_or_event_call external action sg before after tid old
    eid generation (proj1 (Hcoverage action Hin)) Hvalid Hstep Hold Hcont) as [Hprojection|Hcall].
  - exact Hprojection.
  - destruct Hcall as [actor [event [kind [message [result [Haction Hactual]]]]]].
    eapply tmr_task_sem_event_ready_call_projection;
      [exact Hvalid|exact (Hcalls actor event kind message result Haction)|
       exact Hactual|exact Hold|exact Hcont].
Qed.

(** This parameter is a source-domain proof for registered actual calls,
    not a new public Pend premise or a proved consequence of coverage.
    An actual EventReady caller must retain it when forming that action.
    The trace, actor restrictions, stopped bit and critical resources are
    exactly the caller's existing objects. *)
Lemma tmr_task_sem_registered_trace_projection :
  forall external critical sg observer event_observer before stopped after,
  tmr_task_registered_source_coverage external critical ->
  (forall actor event kind message result current next,
    critical.(critical_region_clients) (event_task_rdy_source_client actor event kind message result) ->
    UCOS2_state_inv sg current ->
    kernel_client_step (event_task_rdy_source_client actor event kind message result) sg current next ->
    tmr_task_sem_event_ready_call_input sg current event kind result) ->
  kernel_client_resource_trace critical.(critical_region_clients) sg observer event_observer
    before stopped after ->
  UCOS2_state_inv sg before ->
  forall tid old eid generation,
    before.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros external critical sg observer event_observer before stopped after Hcoverage Hcalls Htrace.
  induction Htrace as [state|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intros Hvalid tid old eid generation Hold Hcont.
  - apply sem_pend_task_projection_refl; exact Hold.
  - assert (Hmiddle : UCOS2_state_inv sg middle).
    { exact (proj1 (kernel_client_certificate_preserves_selected_resources action
        (critical_region_client_certificates critical action Hin) sg before middle Hvalid Hstep)). }
    destruct (tmr_task_sem_registered_source_projection external critical sg before middle action
      tid old eid generation Hcoverage Hin Hvalid Hstep
      ltac:(intros actor event kind message result Haction; subst action;
        eapply Hcalls; eassumption) Hold Hcont) as [current [Hcurrent Hfirst]].
    assert (Hcontinue : sem_pend_wait_continuation eid generation current).
    { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
    destruct (IH Hmiddle tid current eid generation Hcurrent Hcontinue) as [last [Hlast Hsecond]].
    exists last; split; [exact Hlast|eapply rt_trans; eassumption].
Qed.

Lemma tmr_task_sem_registered_trace_preserves_continuation :
  forall external critical sg observer event_observer before stopped after tid old eid generation,
  tmr_task_registered_source_coverage external critical ->
  (forall actor event kind message result current next,
    critical.(critical_region_clients) (event_task_rdy_source_client actor event kind message result) ->
    UCOS2_state_inv sg current ->
    kernel_client_step (event_task_rdy_source_client actor event kind message result) sg current next ->
    tmr_task_sem_event_ready_call_input sg current event kind result) ->
  kernel_client_resource_trace critical.(critical_region_clients) sg observer event_observer
    before stopped after ->
  UCOS2_state_inv sg before -> before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  exists current, after.(TskState).(inUsedTaskStates) tid = Some current /\
    sem_pend_wait_continuation eid generation current.
Proof.
  intros external critical sg observer event_observer before stopped after tid old eid generation
    Hcoverage Hcalls Htrace Hvalid Hold Hcont.
  destruct (tmr_task_sem_registered_trace_projection external critical sg observer event_observer
    before stopped after Hcoverage Hcalls Htrace Hvalid tid old eid generation Hold Hcont)
    as [current [Hcurrent Heffects]].
  exists current; split; [exact Hcurrent|].
  eapply sem_pend_wait_trace_preserves_continuation; eassumption.
Qed.

Lemma tmr_task_sem_registered_resumption_projection :
  forall external critical sg observer event_observer before stopped after tid old eid generation,
  tmr_task_registered_source_coverage external critical ->
  (forall actor event kind message result current next,
    critical.(critical_region_clients) (event_task_rdy_source_client actor event kind message result) ->
    UCOS2_state_inv sg current ->
    kernel_client_step (event_task_rdy_source_client actor event kind message result) sg current next ->
    tmr_task_sem_event_ready_call_input sg current event kind result) ->
  kernel_resumption_resource_trace critical.(critical_region_clients) sg observer event_observer
    before stopped after ->
  UCOS2_state_inv sg before -> before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros external critical sg observer event_observer before stopped after tid old eid generation
    Hcoverage Hcalls Htrace Hvalid Hold Hcont.
  eapply tmr_task_sem_registered_trace_projection;
    [exact Hcoverage|exact Hcalls| |exact Hvalid|exact Hold|exact Hcont].
  apply kernel_resumption_resource_trace_erases; exact Htrace.
Qed.
