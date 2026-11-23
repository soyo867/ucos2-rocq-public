Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality Coq.micromega.Lia.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_state_machine.
Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Shared Time actions from V2.93.01 Source/os_time.c. Time has no extra
    state record or heap owner: its stores affect Task, Scheduler and Tick.
    These are masked source segments, not whole API specifications. Entry
    observations, Save/Restore, trace hooks and OS_Sched remain separate
    source boundaries. In particular an observation made before Save cannot
    silently be identified with the later acquired state. *)
Definition task_set_delay (t : TaskAbstractState) (ticks : Z) : TaskAbstractState :=
  {| taskID := t.(taskID); taskGeneration := t.(taskGeneration);
     tcbStkPtr := t.(tcbStkPtr); tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom); tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt); tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode); tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName); tcbReg0 := t.(tcbReg0);
 tcbCtxSwCtr := t.(tcbCtxSwCtr);
 tcbCyclesTot := t.(tcbCyclesTot);
 tcbCyclesStart := t.(tcbCyclesStart);
 tcbStkBase := t.(tcbStkBase);
 tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42); tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
     curPrio := t.(curPrio); stat := t.(stat); statPend := t.(statPend);
     dly := ticks; eventPtr := t.(eventPtr);
     eventMultiWaitEvents := t.(eventMultiWaitEvents);
     eventMultiRdy := t.(eventMultiRdy); msg := t.(msg);
     nextTCB := t.(nextTCB); prevTCB := t.(prevTCB); delReq := t.(delReq) |}.

Lemma task_set_delay_layout_image_eq : forall sg t ticks,
  task_layout_image sg (task_set_delay t ticks) =
    tcb_layout_write (task_layout_image sg t) (TCBCommonField TCBDly) (Some ticks).
Proof.
  intros; apply functional_extensionality; intros [field| | | | | | |]; try reflexivity;
    destruct field; reflexivity.
Qed.

Lemma task_set_delay_not_ready : forall t ticks,
  ticks <> 0 ->
  is_effectively_ready (task_set_delay t ticks).(stat) (task_set_delay t ticks).(dly) = false.
Proof.
  intros t ticks Hticks; unfold is_effectively_ready; cbn [task_set_delay stat dly].
  rewrite (proj2 (Z.eqb_neq ticks 0) Hticks).
  destruct (Z.eqb (task_non_suspension_bits t.(stat)) 0); simpl;
    rewrite ?Bool.andb_false_r; reflexivity.
Qed.

(** OSTimeDlyResume:196--205. Clear the delay and PEND_ANY, but retain
    SUSPEND, MULTI, Event/Flag registrations and the message. The waiting
    continuation performs the later unlink/cleanup. This is not TaskResume. *)
Definition task_expire_delay (t : TaskAbstractState) : TaskAbstractState :=
  {| taskID := t.(taskID); taskGeneration := t.(taskGeneration);
     tcbStkPtr := t.(tcbStkPtr); tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom); tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt); tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode); tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName); tcbReg0 := t.(tcbReg0);
 tcbCtxSwCtr := t.(tcbCtxSwCtr);
 tcbCyclesTot := t.(tcbCyclesTot);
 tcbCyclesStart := t.(tcbCyclesStart);
 tcbStkBase := t.(tcbStkBase);
 tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42); tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr); curPrio := t.(curPrio);
     stat := task_status_after_timeout t.(stat);
     statPend := snd (task_status_timeout (encode_task_status t.(stat)));
     dly := 0; eventPtr := t.(eventPtr);
     eventMultiWaitEvents := t.(eventMultiWaitEvents);
     eventMultiRdy := t.(eventMultiRdy); msg := t.(msg);
     nextTCB := t.(nextTCB); prevTCB := t.(prevTCB); delReq := t.(delReq) |}.

Lemma task_expire_delay_eq_last_tick : forall t,
  t.(dly) = 1 -> task_expire_delay t = tick_task_update t.
Proof. intros t Hd; unfold tick_task_update; rewrite Hd; reflexivity. Qed.

Lemma task_expire_delay_layout_image_eq : forall sg t,
  task_layout_image sg (task_expire_delay t) =
    tcb_multi_timeout_image
      (tcb_layout_update_common (fun image => tcb_write image TCBDly (Some 0))
        (task_layout_image sg t)) (encode_task_status t.(stat)).
Proof.
  intros sg t.
  pose proof (tick_task_update_layout_image_eq sg (task_set_delay t 1)
    ltac:(cbn; lia)) as Himage.
  change (task_layout_image sg (task_expire_delay t) =
    tcb_multi_timeout_image
      (tcb_layout_update_common (fun image => tcb_write image TCBDly (Some 0))
        (task_layout_image sg (task_set_delay t 1))) (encode_task_status t.(stat))) in Himage.
  rewrite Himage; f_equal.
  apply functional_extensionality; intros [field| | | | | | |]; try reflexivity;
    destruct field; reflexivity.
Qed.

Lemma task_expire_delay_preserves_linked_phase : forall t kind,
  t.(dly) <> 0 -> task_linked_wait_phase t kind ->
  task_linked_wait_phase (task_expire_delay t) kind.
Proof.
  intros t kind Hd [Hp|[_ [_ Hzero]]]; [|contradiction].
  unfold task_linked_wait_phase; cbn [task_expire_delay stat statPend dly].
  rewrite (task_status_single_of_mask t.(stat) (Some kind) Hp).
  destruct kind; destruct (task_is_suspended t.(stat));
    try (left; reflexivity); right; repeat split; reflexivity.
Qed.

Lemma task_expire_delay_preserves_suspension : forall t,
  task_is_suspended (task_expire_delay t).(stat) = task_is_suspended t.(stat).
Proof. intros; apply task_status_after_timeout_preserves_suspension. Qed.

Lemma task_expire_delay_ready_test : forall t,
  task_status_reserved_bits_clear false t.(stat) ->
  is_effectively_ready (task_expire_delay t).(stat) (task_expire_delay t).(dly) =
    negb (task_status_is_suspended (encode_task_status (task_expire_delay t).(stat))).
Proof.
  intros t Hbits; unfold is_effectively_ready; cbn [task_expire_delay stat dly].
  rewrite task_status_after_timeout_no_multi_pending_bits by exact Hbits.
  cbn [Z.eqb]; rewrite Bool.andb_true_r; reflexivity.
Qed.

Lemma task_expire_delay_preserves_cross_module_consistency : forall sg s tid old,
  s.(TskState).(inUsedTaskStates) tid = Some old -> old.(dly) <> 0 ->
  cross_module_consistency sg s ->
  cross_module_consistency sg
    (replace_TskS (glob_task_set_usedtask s.(TskState) tid (task_expire_delay old)) s).
Proof.
  intros sg s tid old Hold Hd [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflag Htimer]]]]]].
  split; [eapply task_mutex_priotbl_consistency_update_task; [exact Hold|reflexivity|exact Htable]|].
  split; [eapply mutex_owner_snapshot_update_task; [exact Hold|exact Hsnapshot]|].
  split.
  - eapply event_wait_object_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity| |exact Hwait].
    intros; apply task_expire_delay_preserves_linked_phase; assumption.
  - split; [exact Hprotocol|]; split; [exact Hunique|]; split; [|exact Htimer].
    eapply task_flag_waiter_consistency_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|reflexivity| | |exact Hflag].
    + apply task_expire_delay_preserves_linked_phase; exact Hd.
    + intro Hpending; exfalso.
      exact (task_status_after_timeout_no_single_pending old.(stat) PendFlag
        ltac:(discriminate) Hpending).
Qed.

(** The successful masked action after a nonzero-delay lookup. The source
    tests SUSPEND alone for ready insertion. This total transformer keeps
    that test even for Multi; its ordinary global-invariant theorem below
    uses the selected no-Multi profile rather than changing the operation. *)
Definition time_dly_resume_state (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (tid : TaskID) (old : TaskAbstractState) : UCOS2_Verify_State :=
  let new := task_expire_delay old in
  replace_SchedS (sched_wake_by_status sg s.(TskState) s.(SchedState) tid
      (encode_task_status new.(stat)))
    (replace_TskS (glob_task_set_usedtask s.(TskState) tid new) s).

Lemma time_dly_resume_preserves_validity : forall sg s tid old,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  old.(dly) <> 0 -> UCOS2_state_inv sg (time_dly_resume_state sg s tid old).
Proof.
  intros sg s tid old [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus Hmodules]]]]]]]
    Hold Hd.
  destruct Hmodules as
    [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]].
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false).
  { unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto. }
  assert (Hbits : task_status_reserved_bits_clear false old.(stat)).
  { rewrite <- Hmulti; exact (Hstatus tid old Hold). }
  assert (HreferencesAfter : kernel_names_valid sg (time_dly_resume_state sg s tid old)).
  { eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
    - eapply task_update_name_references; [exact Hold|reflexivity].
    - intros; assumption.
    - intros; assumption.
    - intros; assumption.
    - intros; assumption. }
  assert (HstacksAfter : parked_stacks_consistent
    (glob_task_set_usedtask s.(TskState) tid (task_expire_delay old))
    s.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  unfold time_dly_resume_state; cbn zeta.
  split; [exact Hprofile|]; split.
  - eapply task_update_preserves_in_range; try eassumption; reflexivity.
  - split.
    + cbn [replace_SchedS replace_TskS TskState SchedState].
      rewrite (sched_wake_by_status_eq_wake_task sg s.(TskState) s.(SchedState) tid
        (encode_task_status (task_expire_delay old).(stat)) (task_expire_delay old)
        (task_expire_delay_ready_test old Hbits)).
      eapply sched_wake_task_preserves_in_range;
        [exact Htasks|exact Hsched|exact Hold|reflexivity|].
      unfold is_effectively_ready; rewrite (proj2 (Z.eqb_neq old.(dly) 0) Hd).
      destruct (Z.eqb (task_non_suspension_bits old.(stat)) 0);
        rewrite ?Bool.andb_false_r; discriminate.
    + split.
      * eapply event_update_task_preserves_in_range;
          [exact Hold|reflexivity|reflexivity|reflexivity| |exact Hevents].
        intros; apply task_expire_delay_preserves_linked_phase; assumption.
      * split.
        -- apply cross_module_consistency_sched_frame; [apply sched_wake_by_status_running_eq|].
           apply task_expire_delay_preserves_cross_module_consistency; assumption.
        -- split.
           ++ intro Hrun; cbn [replace_SchedS replace_TskS SchedState] in Hrun.
              rewrite sched_wake_by_status_running_eq in Hrun.
              eapply task_update_preserves_idle_tail;
                [exact Hold|reflexivity|apply Hidle; exact Hrun].
           ++ split.
              2: { repeat (split; [assumption|]); exact Hpending. }
              apply task_reserved_bits_clear_update_task; [exact Hstatus|].
              apply task_status_after_timeout_preserves_reserved_bits; exact (Hstatus tid old Hold).
Qed.

Lemma time_dly_resume_selected_transition : forall sg,
  UCOS2SelectedTransition sg task_sched_modules
    (fun before after => exists tid old,
      before.(TskState).(inUsedTaskStates) tid = Some old /\ old.(dly) <> 0 /\
      after = time_dly_resume_state sg before tid old).
Proof.
  intro sg; constructor.
  - intros before after Hvalid (tid & old & Hold & Hd & ->).
    apply time_dly_resume_preserves_validity; assumption.
  - intros before after Hvalid (tid & old & Hold & Hd & ->) owner Hkept.
    destruct owner; simpl in Hkept; try discriminate; try reflexivity.
    unfold UCOS2_module_rep, time_dly_resume_state;
      cbn [replace_SchedS replace_TskS TskState EventState].
    rewrite (event_raw_rep_change_task_index sg before.(TskState)
      (glob_task_set_usedtask before.(TskState) tid (task_expire_delay old)) before.(EventState));
      [reflexivity|].
    apply event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hold|reflexivity].
Qed.

(** OSTimeDly:71--78. Zero ticks is a no-op. Positive ticks remove the
    current task's ready bits and update only its delay; scheduler caches
    remain unchanged until the later OS_Sched. The old TCB is the acquired
    current-task lookup, not an arbitrary earlier snapshot. *)
Definition time_dly_state (s : UCOS2_Verify_State)
  (tid : TaskID) (old : TaskAbstractState) (ticks : Z) : UCOS2_Verify_State :=
  if Z.eqb ticks 0 then s else
  replace_SchedS (sched_remove_ready_task s.(SchedState) tid)
    (replace_TskS (glob_task_set_usedtask s.(TskState) tid (task_set_delay old ticks)) s).

Lemma time_dly_zero_eq : forall s tid old, time_dly_state s tid old 0 = s.
Proof. reflexivity. Qed.

Lemma time_dly_current_blocked_before_schedule : forall s tid old ticks,
  sched_current_ready_at s.(TskState) s.(SchedState) tid old -> ticks <> 0 ->
  sched_current_blocked_before_schedule
    (time_dly_state s tid old ticks).(TskState)
    (time_dly_state s tid old ticks).(SchedState) tid (task_set_delay old ticks).
Proof.
  intros s tid old ticks [Hold [Hcurrent [Hpriority [Hmember Hready]]]] Hticks.
  unfold time_dly_state; rewrite (proj2 (Z.eqb_neq ticks 0) Hticks).
  unfold sched_current_blocked_before_schedule.
  cbn [replace_SchedS replace_TskS TskState SchedState glob_task_set_usedtask
    inUsedTaskStates sched_remove_ready_task sched_set_ready curTaskID curSchedPrio
    readyList task_set_delay curPrio].
  rewrite Z.eqb_refl; split; [reflexivity|].
  split; [exact Hcurrent|]; split; [exact Hpriority|].
  split; [apply remove_Z_eqb_notin|apply task_set_delay_not_ready; exact Hticks].
Qed.

(** This is an application-entry protocol, not a new guard in the C
    function. A ready task still carrying a timeout-linked Event/Flag
    registration must first finish its Pend continuation. Delaying it in
    that intermediate phase would destroy the zero-delay cleanup fact. *)
Lemma time_dly_preserves_validity : forall sg s tid old ticks,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  is_effectively_ready old.(stat) old.(dly) = true ->
  old.(eventPtr) = None -> old.(tcbFlagNode) = 0 ->
  UCOS2_state_inv sg (time_dly_state s tid old ticks).
Proof.
  intros sg s tid old ticks Hvalid Hold Hready Hptr Hnode.
  unfold time_dly_state; destruct (Z.eqb ticks 0) eqn:Hzero; [exact Hvalid|].
  apply Z.eqb_neq in Hzero.
  destruct Hvalid as [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus Hmodules]]]]]]].
  destruct Hmodules as
    [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]].
  assert (Habsent : forall eid e, s.(EventState).(inUsedEventStates) eid = Some e ->
    ~ In tid e.(waitList)).
  { intros eid e He Hin.
    destruct Hcross as [_ [_ [[Hentries _] _]]].
    destruct (event_waiter_task_fields sg s.(TskState) eid e tid (Hentries eid e He) Hin)
      as (found & kind & Hfound & Hkind & Hfoundptr & Hrest).
    rewrite Hold in Hfound; injection Hfound as Hsame; subst found; congruence. }
  assert (HreferencesAfter : kernel_names_valid sg (time_dly_state s tid old ticks)).
  { unfold time_dly_state.
    rewrite (proj2 (Z.eqb_neq ticks 0) Hzero).
    eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
    - eapply task_update_name_references; [exact Hold|reflexivity].
    - intros; assumption.
    - intros; assumption.
    - intros; assumption.
    - intros; assumption. }
  assert (HstacksAfter : parked_stacks_consistent
    (glob_task_set_usedtask s.(TskState) tid (task_set_delay old ticks))
    s.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  unfold time_dly_state in HreferencesAfter.
  rewrite (proj2 (Z.eqb_neq ticks 0) Hzero) in HreferencesAfter.
  split; [exact Hprofile|]; split.
  - eapply task_update_preserves_in_range; try eassumption; reflexivity.
  - split.
    + eapply sched_remove_ready_task_preserves_in_range;
        [exact Hsched|exact Hold|reflexivity|apply task_set_delay_not_ready; exact Hzero].
    + split.
      * apply event_update_unlisted_task_preserves_in_range; assumption.
      * split.
        -- apply cross_module_consistency_sched_frame; [reflexivity|].
           destruct Hcross as [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflag Hinit]]]]]].
           split; [eapply task_mutex_priotbl_consistency_update_task;
             [exact Hold|reflexivity|exact Htable]|].
           split; [eapply mutex_owner_snapshot_update_task;
             [exact Hold|exact Hsnapshot]|].
           split; [eapply event_wait_object_update_unlisted_task;
             [exact Hold|reflexivity|reflexivity|exact Habsent|exact Hwait]|].
           split; [exact Hprotocol|]; split; [exact Hunique|]; split; [|exact Hinit].
           eapply task_flag_waiter_consistency_update_unregistered_task;
             [exact Hold|exact Hnode|exact Hnode| |exact Hflag].
           change (task_non_suspension_bits old.(stat) <> task_pend_mask PendFlag).
           rewrite (task_effectively_ready_has_no_pending old Hready); discriminate.
        -- split.
           ++ intro Hrun; eapply task_update_preserves_idle_tail;
                [exact Hold|reflexivity|apply Hidle; exact Hrun].
           ++ split.
              2: { repeat (split; [assumption|]); exact Hpending. }
              apply task_reserved_bits_clear_update_task; [exact Hstatus|exact (Hstatus tid old Hold)].
Qed.

Lemma time_dly_selected_transition : forall sg,
  UCOS2SelectedTransition sg task_sched_modules
    (fun before after => exists tid old ticks,
      before.(TskState).(inUsedTaskStates) tid = Some old /\
      is_effectively_ready old.(stat) old.(dly) = true /\
      old.(eventPtr) = None /\ old.(tcbFlagNode) = 0 /\
      0 <= ticks < 4294967296 /\ after = time_dly_state before tid old ticks).
Proof.
  intro sg; constructor.
  - intros before after Hvalid (tid & old & ticks & Hold & Hready & Hptr & Hnode & Hticks & ->).
    apply time_dly_preserves_validity; assumption.
  - intros before after Hvalid (tid & old & ticks & Hold & Hready & Hptr & Hnode & Hticks & ->)
      owner Hkept.
    unfold time_dly_state; destruct (Z.eqb ticks 0); [reflexivity|].
    destruct owner; simpl in Hkept; try discriminate; try reflexivity.
    unfold UCOS2_module_rep; cbn [replace_SchedS replace_TskS TskState EventState].
    rewrite (event_raw_rep_change_task_index sg before.(TskState)
      (glob_task_set_usedtask before.(TskState) tid (task_set_delay old ticks)) before.(EventState));
      [reflexivity|].
    apply event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hold|reflexivity].
Qed.

(** OSTimeSet writes only OSTime, preserving task delays and the
    single-step control byte.
    The typed UInt argument supplies the bound for the updated Tick heap. *)
Definition time_set_state (s : UCOS2_Verify_State) (ticks : Z) : UCOS2_Verify_State :=
  replace_TickS {| ostime := ticks;
                  tickStepState := s.(TickState).(tickStepState) |} s.

Definition time_get (s : UCOS2_Verify_State) : Z := s.(TickState).(ostime).

Lemma time_get_after_set : forall s ticks, time_get (time_set_state s ticks) = ticks.
Proof. reflexivity. Qed.

Lemma time_set_preserves_validity : forall sg s ticks,
  UCOS2_state_inv sg s -> UCOS2_state_inv sg (time_set_state s ticks).
Proof. intros; exact H. Qed.

Definition tick_modules (owner : UCOS2Module) : bool :=
  match owner with TickModule => true | _ => false end.

Lemma time_set_selected_transition : forall sg,
  UCOS2SelectedTransition sg tick_modules
    (fun before after => exists ticks, 0 <= ticks < 4294967296 /\
      after = time_set_state before ticks).
Proof.
  intro sg; constructor.
  - intros before after Hvalid (ticks & Hticks & ->); apply time_set_preserves_validity; exact Hvalid.
  - intros before after Hvalid (ticks & Hticks & ->) owner Hkept.
    destruct owner; simpl in Hkept; discriminate || reflexivity.
Qed.

(** OSTimeDlyHMSM:147--149, using the selected 32-bit unsigned C arithmetic.
    Parameters are the already typed input values; a source instantiation
    supplies 8-bit hours/minutes/seconds, 16-bit ms and a positive UInt rate.
    In particular the millisecond product wraps BEFORE division by 1000.
    None denotes the source's undefined division at rate zero, not a new
    API error code. Argument/ISR/lock error branches precede this expression.
    A nonzero duration may round to zero ticks, which OSTimeDly accepts as
    a no-op. No ideal real-time rounding law is assumed here. *)
Definition time_hmsm_ticks (rate hours minutes seconds ms : Z) : option Z :=
  if Z.eqb rate 0 then None else
  let total_seconds := kernel_u32
    (kernel_u32 (kernel_u32 (hours * 3600) + kernel_u32 (minutes * 60)) + seconds) in
  let whole := kernel_u32 (total_seconds * rate) in
  let fraction := kernel_u32 (rate * kernel_u32 (ms + 500 / rate)) / 1000 in
  Some (kernel_u32 (whole + fraction)).

Lemma time_hmsm_ticks_defined : forall rate hours minutes seconds ms,
  0 < rate -> exists ticks, time_hmsm_ticks rate hours minutes seconds ms = Some ticks.
Proof.
  intros; unfold time_hmsm_ticks; rewrite (proj2 (Z.eqb_neq rate 0) ltac:(lia)); eauto.
Qed.

Lemma time_hmsm_ticks_in_range : forall rate hours minutes seconds ms ticks,
  time_hmsm_ticks rate hours minutes seconds ms = Some ticks -> 0 <= ticks < 4294967296.
Proof.
  intros rate hours minutes seconds ms ticks Hticks; unfold time_hmsm_ticks in Hticks.
  destruct (Z.eqb rate 0); [discriminate|]; injection Hticks as Hticks; subst ticks.
  apply kernel_u32_in_range.
Qed.

(** A consumer of the shared spatial composition theorem. Supplying the
    changed Task/Scheduler heap remains the source proof's responsibility;
    the Event/Flag registrations and all other owners are retained. *)
Lemma time_dly_resume_resources_merge : forall sg s tid old,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some old -> old.(dly) <> 0 ->
  UCOS2_selected_rep sg (time_dly_resume_state sg s tid old) task_sched_modules **
    UCOS2_selected_rep sg s (fun owner => negb (task_sched_modules owner)) |--
  UCOS2_inv sg (time_dly_resume_state sg s tid old).
Proof.
  intros sg s tid old Hvalid Hold Hd.
  eapply ucos2_selected_transition_composes.
  - apply time_dly_resume_selected_transition.
  - exact Hvalid.
  - exists tid, old; repeat split; assumption || reflexivity.
Qed.
