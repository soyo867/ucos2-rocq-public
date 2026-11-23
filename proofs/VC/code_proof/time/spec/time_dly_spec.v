Require Export Ucos2Verify.lib.time.
Require Export Ucos2Verify.VC.code.task.spec.task_suspend_api_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The three no-call branches are ordered exactly as Source/os_time.c.
    The observation is unit: OSTimeDly has no C error or result value. *)
Definition time_dly_noop (ticks : Z) (before : UCOS2_Verify_State) : bool :=
  if 0 <? os_sched_ints before then true else
  if 0 <? os_sched_locks before then true else negb (0 <? ticks).

(** This relation describes only the real protected current-task update.
    Readiness, clean Pend phase and Scheduler admissibility are NOT hidden
    guards of the program; they are separate source/resource obligations. *)
Definition time_dly_protected (ticks : Z) : program UCOS2_Verify_State unit :=
  fun acquired _ released =>
    exists tid old,
      acquired.(SchedState).(curTaskID) = Some tid /\
      acquired.(TskState).(inUsedTaskStates) tid = Some old /\
      released = time_dly_state acquired tid old ticks.

Definition time_dly_prefix_program environment critical sg caller mask ticks
  : program UCOS2_Verify_State (bool * TaskSuspendCaller) :=
  StateRelMonad.bind (StateRelBasic.get' (fun state => state)) (fun before =>
    if time_dly_noop ticks before then StateRelMonad.ret (false, caller) else
    StateRelMonad.bind (task_suspend_save_program environment critical sg caller mask)
      (fun entered => StateRelMonad.bind (time_dly_protected ticks)
        (fun _ => StateRelMonad.bind
          (task_suspend_restore_program environment critical sg (fst entered))
          (fun returned => StateRelMonad.ret (true, returned))))).

Definition time_dly_tail_program environment critical sg mask
  (result : bool * TaskSuspendCaller) : program UCOS2_Verify_State unit :=
  if fst result then
    StateRelMonad.bind (task_suspend_schedule_program environment critical sg (snd result) mask)
      (fun _ => StateRelMonad.ret tt)
  else StateRelMonad.ret tt.

Definition time_dly_program environment critical sg caller mask ticks
  : program UCOS2_Verify_State unit :=
  StateRelMonad.bind (time_dly_prefix_program environment critical sg caller mask ticks)
    (time_dly_tail_program environment critical sg mask).

Definition time_dly_safe environment critical sg caller mask ticks before
  (X : unit -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (time_dly_program environment critical sg caller mask ticks) X.

Definition time_dly_return_safe current (X : unit -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = current) (StateRelMonad.ret tt) X.

Definition time_dly_scheduler_safe environment critical sg caller mask before
  (X : unit -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (StateRelMonad.bind (task_suspend_schedule_program environment critical sg caller mask)
      (fun _ => StateRelMonad.ret tt)) X.

Lemma time_dly_noop_isr : forall ticks before,
  0 < os_sched_ints before -> time_dly_noop ticks before = true.
Proof.
  intros; unfold time_dly_noop; rewrite (proj2 (Z.ltb_lt _ _) H); reflexivity.
Qed.

Lemma time_dly_noop_locked : forall ticks before,
  0 < os_sched_locks before -> time_dly_noop ticks before = true.
Proof.
  intros; unfold time_dly_noop; destruct (0 <? os_sched_ints before); [reflexivity|].
  rewrite (proj2 (Z.ltb_lt _ _) H); reflexivity.
Qed.

Lemma time_dly_noop_zero : forall before, time_dly_noop 0 before = true.
Proof.
  intros; unfold time_dly_noop; destruct (0 <? os_sched_ints before),
    (0 <? os_sched_locks before); reflexivity.
Qed.

Lemma time_dly_positive : forall ticks before,
  os_sched_ints before = 0 -> os_sched_locks before = 0 -> 0 < ticks ->
  time_dly_noop ticks before = false.
Proof.
  intros; unfold time_dly_noop; rewrite H, H0, (proj2 (Z.ltb_lt _ _) H1); reflexivity.
Qed.

Lemma time_dly_prefix_noop : forall environment critical sg caller mask ticks before,
  time_dly_noop ticks before = true ->
  time_dly_prefix_program environment critical sg caller mask ticks before (false, caller) before.
Proof.
  intros; unfold time_dly_prefix_program; exists before, before.
  split; [split; reflexivity|]. rewrite H; split; reflexivity.
Qed.

Lemma time_dly_prefix_delay : forall environment critical sg caller mask ticks before
  saved active acquired tid old released returned current,
  time_dly_noop ticks before = false ->
  task_suspend_save_effect environment critical sg caller active mask saved before acquired ->
  acquired.(SchedState).(curTaskID) = Some tid ->
  acquired.(TskState).(inUsedTaskStates) tid = Some old ->
  released = time_dly_state acquired tid old ticks ->
  task_suspend_restore_effect environment critical sg active returned released current ->
  time_dly_prefix_program environment critical sg caller mask ticks before (true, returned) current.
Proof.
  intros environment critical sg caller mask ticks before saved active acquired tid old released
    returned current Hpositive Hsave Hcurrent Hold Hreleased Hrestore.
  unfold time_dly_prefix_program; exists before, before; split; [split; reflexivity|].
  rewrite Hpositive; exists (active, saved), acquired; split; [exact Hsave|].
  exists tt, released; split.
  - exists tid, old; auto.
  - exists returned, current; split; [exact Hrestore|split; reflexivity].
Qed.

Lemma time_dly_prefix_safe_continuation : forall environment critical sg caller mask ticks
  before scheduled returned current X,
  time_dly_prefix_program environment critical sg caller mask ticks before (scheduled, returned) current ->
  time_dly_safe environment critical sg caller mask ticks before X ->
  safeExec (fun state => state = current)
    (time_dly_tail_program environment critical sg mask (scheduled, returned)) X.
Proof.
  intros environment critical sg caller mask ticks before scheduled returned current X Hprefix Hsafe.
  eapply (highstepbind_derive
    (time_dly_prefix_program environment critical sg caller mask ticks)
    (time_dly_tail_program environment critical sg mask)
    (fun state => state = before) (scheduled, returned) (fun state => state = current)).
  - intros state ->; exists current; split; [exact Hprefix|reflexivity].
  - exact Hsafe.
Qed.

Lemma time_dly_noop_safe_return : forall environment critical sg caller mask ticks before X,
  time_dly_noop ticks before = true ->
  time_dly_safe environment critical sg caller mask ticks before X ->
  time_dly_return_safe before X.
Proof.
  intros; exact (time_dly_prefix_safe_continuation environment critical sg caller mask ticks
    before false caller before X (time_dly_prefix_noop _ _ _ _ _ _ _ H) H0).
Qed.

Lemma time_dly_scheduler_result_safe_return : forall environment critical sg caller mask before
  returned current X,
  task_suspend_schedule_program environment critical sg caller mask before returned current ->
  time_dly_scheduler_safe environment critical sg caller mask before X ->
  time_dly_return_safe current X.
Proof.
  intros environment critical sg caller mask before returned current X Hstep Hsafe.
  eapply (highstepbind_derive (task_suspend_schedule_program environment critical sg caller mask)
    (fun _ => StateRelMonad.ret tt) (fun state => state = before) returned
    (fun state => state = current)).
  - intros state ->; exists current; split; [exact Hstep|reflexivity].
  - exact Hsafe.
Qed.

(** Same-heap result: the actual returned caller and endpoint index both
    the source history and all closed resources. No eventual-return claim. *)
Definition time_dly_scheduler_post environment critical saved_local sg caller mask before
  (X : unit -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned current,
    coq_prop (task_suspend_schedule_program environment critical sg caller mask before returned current /\
      time_dly_return_safe current X) &&
    task_suspend_closed environment critical saved_local sg returned mask current.

Lemma time_dly_scheduler_history_post : forall environment critical saved_local sg caller mask before X,
  time_dly_scheduler_safe environment critical sg caller mask before X ->
  task_suspend_scheduler_history_post environment critical saved_local sg caller mask before |--
  time_dly_scheduler_post environment critical saved_local sg caller mask before X.
Proof.
  intros environment critical saved_local sg [call|view] mask before X Hsafe;
    unfold time_dly_scheduler_post; cbn [task_suspend_scheduler_history_post].
  - unfold os_sched_continuation_history_return_post at 1; Intros returned current.
    assert (Hprogram : task_suspend_schedule_program environment critical sg
      (TaskSuspendTask call) mask before (TaskSuspendTask returned) current).
    { cbn [task_suspend_schedule_program]; exists returned, current; split.
      - apply os_sched_continuation_program_iff; tauto.
      - split; reflexivity. }
    pose proof (time_dly_scheduler_result_safe_return environment critical sg
      (TaskSuspendTask call) mask before (TaskSuspendTask returned) current X Hprogram Hsafe).
    Exists (TaskSuspendTask returned) current.
    cbn [task_suspend_closed]; rewrite task_tcb_init_continuation_save_input_closed_world; entailer!.
  - unfold sched_disabled_contextual_post at 1; Intros saved acquired current.
    assert (Hprogram : task_suspend_schedule_program environment critical sg
      (TaskSuspendDisabled view) mask before (TaskSuspendDisabled view) current).
    { cbn [task_suspend_schedule_program].
      exists (TaskSuspendDisabled view, saved), acquired; split.
      - cbn [task_suspend_save_program task_suspend_save_effect fst snd]; split; [reflexivity|tauto].
      - exists tt, acquired; split.
        + split; [tauto|reflexivity].
        + cbn [task_suspend_restore_program task_suspend_restore_effect fst]; split; [reflexivity|tauto]. }
    pose proof (time_dly_scheduler_result_safe_return environment critical sg
      (TaskSuspendDisabled view) mask before (TaskSuspendDisabled view) current X Hprogram Hsafe).
    Exists (TaskSuspendDisabled view) current; cbn [task_suspend_closed]; entailer!; tauto.
Qed.

Definition time_dly_result environment critical sg caller mask ticks before returned current : Prop :=
  if time_dly_noop ticks before then returned = caller /\ current = before else
    exists checkpoint_call checkpoint,
      time_dly_prefix_program environment critical sg caller mask ticks before (true, checkpoint_call) checkpoint /\
      task_suspend_schedule_program environment critical sg checkpoint_call mask checkpoint returned current.

Definition time_dly_call_post environment critical saved_local sg caller mask ticks before
  (frame : Assertion) (X : unit -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned current,
    coq_prop (time_dly_result environment critical sg caller mask ticks before returned current /\
      time_dly_return_safe current X) &&
    (task_suspend_closed environment critical saved_local sg returned mask current ** frame).

Lemma time_dly_result_program : forall environment critical sg caller mask ticks before returned current,
  time_dly_result environment critical sg caller mask ticks before returned current ->
  time_dly_program environment critical sg caller mask ticks before tt current.
Proof.
  intros environment critical sg caller mask ticks before returned current Hresult.
  unfold time_dly_result in Hresult; unfold time_dly_program.
  destruct (time_dly_noop ticks before) eqn:Hnoop.
  - destruct Hresult as [-> ->]; exists (false, caller), before.
    split; [apply time_dly_prefix_noop; exact Hnoop|split; reflexivity].
  - destruct Hresult as [middle [checkpoint [Hprefix Hschedule]]].
    exists (true, middle), checkpoint; split; [exact Hprefix|].
    exists returned, current; split; [exact Hschedule|split; reflexivity].
Qed.

(** The shared updater leaves every generation, stack image and parked
    continuation key unchanged. These are transports, not new owners. *)
Lemma time_dly_used_lookup_frame : forall tasks tid target ticks slot node,
  tasks.(inUsedTaskStates) tid = Some target ->
  (glob_task_set_usedtask tasks tid (task_set_delay target ticks)).(inUsedTaskStates) slot = Some node ->
  exists old, tasks.(inUsedTaskStates) slot = Some old /\
    old.(taskGeneration) = node.(taskGeneration) /\ old.(tcbStkPtr) = node.(tcbStkPtr).
Proof.
  intros tasks tid target ticks slot node Htarget Hnode.
  cbn [glob_task_set_usedtask inUsedTaskStates] in Hnode.
  destruct (Z.eqb slot tid) eqn:Hslot.
  - apply Z.eqb_eq in Hslot; subst slot; injection Hnode as Hnode; subst node.
    exists target; repeat split; assumption || reflexivity.
  - exists node; repeat split; assumption || reflexivity.
Qed.

Lemma time_dly_preserves_stack_coverage : forall tasks tid target ticks active,
  tasks.(inUsedTaskStates) tid = Some target -> task_stack_live_coverage tasks active ->
  task_stack_live_coverage (glob_task_set_usedtask tasks tid (task_set_delay target ticks)) active.
Proof.
  intros tasks tid target ticks active Htarget Hcoverage.
  eapply task_stack_live_coverage_used_map_frame with (before := tasks);
    [|reflexivity|exact Hcoverage].
  intros slot node Hnode.
  destruct (time_dly_used_lookup_frame tasks tid target ticks slot node Htarget Hnode)
    as [old [Hold [Hg Hsp]]]; exists old; auto.
Qed.

Lemma time_dly_continuation_capsules : forall environment saved_local before tid target ticks,
  before.(TskState).(inUsedTaskStates) tid = Some target ->
  task_tcb_init_continuation_capsules environment saved_local before |--
  task_tcb_init_continuation_capsules environment saved_local (time_dly_state before tid target ticks).
Proof.
  intros environment saved_local before tid target ticks Htarget.
  unfold time_dly_state; destruct (Z.eqb ticks 0); [entailer!|].
  unfold task_tcb_init_continuation_capsules.
  change (store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations) before.(TskState)
      (task_create_continuation_local saved_local)) before.(TskState).(parkedTaskStacks) |--
    store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations)
      (glob_task_set_usedtask before.(TskState) tid (task_set_delay target ticks))
      (task_create_continuation_local saved_local)) before.(TskState).(parkedTaskStacks)).
  apply kernel_saved_continuation_map_reindex.
  intros key payload node Hstack Hnode Hg.
  eapply time_dly_used_lookup_frame; eassumption.
Qed.

Lemma time_dly_call_resources_updated : forall environment saved_local sg caller before tid target ticks,
  before.(TskState).(inUsedTaskStates) tid = Some target ->
  task_suspend_call_resources environment saved_local sg caller before |--
  task_suspend_call_resources environment saved_local sg caller (time_dly_state before tid target ticks).
Proof.
  intros environment saved_local sg [call|view] before tid target ticks Htarget;
    unfold task_suspend_call_resources; [|entailer!].
  Intros.
  sep_apply_l_atomic (time_dly_continuation_capsules environment saved_local before tid target ticks Htarget).
  entailer!.
  unfold time_dly_state; destruct (Z.eqb ticks 0); [assumption|].
  apply time_dly_preserves_stack_coverage; assumption.
Qed.

Lemma time_dly_delay_field_merge : forall sg tasks tid target ticks,
  tcb_field_address (task_slot_addr sg tid) TCBDly # UInt |-> ticks **
  task_public_storage_without_field sg tasks tid target (TCBCommonField TCBDly) |--
  task_public_storage sg (glob_task_set_usedtask tasks tid (task_set_delay target ticks)).
Proof.
  intros; apply (task_public_storage_merge_updated_field sg tasks tid target
    (task_set_delay target ticks) (TCBCommonField TCBDly) (Some ticks)).
  - apply tcb_configured_common_field_in.
  - apply task_set_delay_layout_image_eq.
Qed.

(** Only the positive-delay call domain uses these Task facts.  In
    particular [kernel_call_task_source] alone says neither ready nor clean
    Pend.  The other member is the minimal selection condition: it need not
    be Idle, and OSTimeDly itself has no Idle guard. *)
Definition time_dly_target_facts sg state tid target : Prop :=
  UCOS2_state_inv sg state /\
  sched_current_ready_at state.(TskState) state.(SchedState) tid target /\
  target.(eventPtr) = None /\ target.(tcbFlagNode) = 0 /\
  exists other, other <> tid /\ In other state.(SchedState).(readyList).

Definition time_dly_scheduler_source sg caller state : Prop :=
  match caller with
  | TaskSuspendTask call =>
      kernel_call_task_source call state /\ kernel_call_stack_available call state /\
      tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
        task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) /\
      state.(SchedState).(readyList) <> []
  | TaskSuspendDisabled _ => False
  end.

Definition time_dly_call_stage sg caller state : Prop :=
  time_dly_scheduler_source sg caller state /\
  exists tid target, time_dly_target_facts sg state tid target.

(** This is an explicit C-call protocol, not an axiom or a strengthened
    Save/Restore summary.  It only constrains actual completed effects of
    THIS call.  The first endpoint must still be in the ordinary Task API
    stage; the second transports the outgoing source and the remaining-ready
    condition through the real Restore.  It assumes no Scheduler result,
    no wake-up and no termination.  HMSM/Stat consumers must discharge it. *)
Definition time_dly_completed_calls environment critical sg original mask ticks before : Prop :=
  (forall active saved acquired,
    task_suspend_save_effect environment critical sg original active mask saved before acquired ->
    UCOS2_state_inv sg acquired -> time_dly_call_stage sg active acquired) /\
  (forall active saved acquired tid target returned current,
    task_suspend_save_effect environment critical sg original active mask saved before acquired ->
    time_dly_target_facts sg acquired tid target ->
    task_suspend_restore_effect environment critical sg active returned
      (time_dly_state acquired tid target ticks) current ->
    time_dly_scheduler_source sg active (time_dly_state acquired tid target ticks) ->
    time_dly_scheduler_source sg returned current).

Definition time_dly_entry_facts environment critical sg caller mask ticks before : Prop :=
  0 <= ticks < 4294967296 /\
    (time_dly_noop ticks before = false ->
      time_dly_call_stage sg caller before /\
      time_dly_completed_calls environment critical sg caller mask ticks before /\
      kernel_sched_ready_clients critical).

Definition time_dly_call_pre environment critical saved_local sg caller mask ticks before
  (frame : Assertion) : Assertion :=
  coq_prop (time_dly_entry_facts environment critical sg caller mask ticks before) &&
  (task_suspend_closed environment critical saved_local sg caller mask before ** frame).

(** Initial TCB construction is a concrete producer of the two clean-Pend
    fields.  This does not assert that arbitrary later calls are clean. *)
Lemma time_dly_initialized_pend_fields : forall args old,
  (task_tcb_init_before_hooks args old).(eventPtr) = None /\
  (task_tcb_init_before_hooks args old).(tcbFlagNode) = 0.
Proof. intros; split; reflexivity. Qed.

(** A completed Event Pend cleanup also produces eventPtr=None, while the
    separate Flag protocol must already have removed its node. *)
Lemma time_dly_event_cleanup_pend_fields : forall multi clear_message target,
  target.(tcbFlagNode) = 0 ->
  (task_event_pend_cleanup multi clear_message target).(eventPtr) = None /\
  (task_event_pend_cleanup multi clear_message target).(tcbFlagNode) = 0.
Proof. intros [] [] target Hnode; split; (reflexivity || exact Hnode). Qed.

(** A concrete two-distinct-member ready list meets the selection side of
    the domain.  No non-Idle condition or contradictory invariant is used. *)
Lemma time_dly_two_ready_members : forall (tid other : Z) (rest : list Z),
  other <> tid -> exists member, member <> tid /\ In member (tid :: other :: rest).
Proof. intros; exists other; simpl; auto. Qed.

Lemma time_dly_stage_from_task_boundary : forall sg call state tid target other,
  UCOS2_state_inv sg state ->
  kernel_call_task_source call state -> kernel_call_stack_available call state ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  sched_current_ready_at state.(TskState) state.(SchedState) tid target ->
  target.(eventPtr) = None -> target.(tcbFlagNode) = 0 ->
  other <> tid -> In other state.(SchedState).(readyList) ->
  time_dly_call_stage sg (TaskSuspendTask call) state.
Proof.
  intros sg call state tid target other Hvalid Hsource Havailable Hlayout Hready Hptr Hflag Hneq Hin.
  split.
  - cbn [time_dly_scheduler_source].
    split; [exact Hsource|]; split; [exact Havailable|]; split; [exact Hlayout|].
    intro E; rewrite E in Hin; contradiction.
  - exists tid, target; unfold time_dly_target_facts.
    split; [exact Hvalid|]; split; [exact Hready|]; split; [exact Hptr|]; split; [exact Hflag|].
    exists other; auto.
Qed.

Lemma time_dly_protected_scheduler_source : forall sg caller acquired tid target ticks,
  time_dly_target_facts sg acquired tid target ->
  time_dly_scheduler_source sg caller acquired ->
  time_dly_scheduler_source sg caller (time_dly_state acquired tid target ticks).
Proof.
  intros sg [call|view] acquired tid target ticks Htarget Hsource; [|contradiction].
  destruct Htarget as [Hvalid [[Hlookup Hready] [Hptr [Hflag [other [Hneq Hin]]]]]].
  unfold time_dly_state; destruct (Z.eqb ticks 0); [exact Hsource|].
  destruct Hsource as [[Horigin [Hactive Hcurrent]] [Havailable [Hlayout Hnonempty]]].
  cbn [time_dly_scheduler_source]; split.
  - split; [exact Horigin|]; split; [|exact Hcurrent].
    eapply glob_task_set_usedtask_preserves_invocation_active;
      [exact Hlookup|reflexivity|exact Hactive].
  - split; [exact Havailable|]; split; [exact Hlayout|].
    assert (Hmember : In other (helpers.remove_Z_eqb tid acquired.(SchedState).(readyList))).
    { apply helpers.remove_Z_eqb_in_neq; assumption. }
    intro E; change (helpers.remove_Z_eqb tid acquired.(SchedState).(readyList) = []) in E.
    rewrite E in Hmember; contradiction.
Qed.

Lemma time_dly_scheduler_source_pre : forall environment critical saved_local sg caller mask state,
  kernel_sched_ready_clients critical -> time_dly_scheduler_source sg caller state ->
  task_suspend_closed environment critical saved_local sg caller mask state |--
  task_suspend_scheduler_pre environment critical saved_local sg caller mask state.
Proof.
  intros environment critical saved_local sg [call|view] mask state Hclients Hsource;
    [|contradiction].
  unfold task_suspend_closed, task_tcb_init_continuation_save_input, task_create_continuation_input.
  Intros.
  assert (Hvalid : UCOS2_state_inv sg state) by tauto.
  destruct Hsource as [Htask [Havailable [Hlayout Hready]]].
  assert (Hbinding : os_sched_current_storage_binding sg call state).
  { apply kernel_call_task_source_current_storage; assumption. }
  assert (Hparked : state.(TskState).(parkedTaskStacks)
    (task_stack_key call.(os_sched_call_stack)) = None).
  { unfold kernel_call_stack_available in Havailable.
    destruct Htask as [Horigin _]; rewrite Horigin in Havailable; exact Havailable. }
  assert (Hcut : os_sched_call_cut sg call state) by (unfold os_sched_call_cut; auto).
  unfold task_suspend_scheduler_pre, os_sched_continuation_call_pre; entailer!.
  unfold os_sched_continuation_pre.
  sep_apply_r_atomic (proj1 (task_tcb_init_continuation_save_input_closed_world
    environment critical saved_local sg call mask state)).
  unfold task_tcb_init_continuation_save_input, task_create_continuation_input; entailer!.
Qed.

(** Original-value prefix splitting is reversible for both caller variants.
    The ISR/locked/zero branches need no Task lease or scheduler source. *)
Definition time_dly_outside_resources environment saved_local sg caller mask state : Assertion :=
  interrupt_platform_running environment.(task_stack_call_platform)
    (task_suspend_view caller).(os_execution_invocation)
    (task_suspend_view caller).(os_execution_origin) mask **
  task_suspend_call_resources environment saved_local sg caller state.

Lemma time_dly_closed_inv_equiv : forall environment critical saved_local sg caller mask state,
  task_suspend_closed environment critical saved_local sg caller mask state --||--
  (UCOS2_inv sg state ** time_dly_outside_resources environment saved_local sg caller mask state).
Proof.
  intros environment critical saved_local sg [call|view] mask state;
    unfold task_suspend_closed, time_dly_outside_resources, task_suspend_call_resources,
      task_suspend_view, os_sched_execution_view,
      task_tcb_init_continuation_save_input, task_create_continuation_input,
      task_tcb_init_continuation_capsules, kernel_call_execution_owned,
      sched_disabled_closed, critical_region_outside;
    rewrite critical_region_outside_without_running_rep;
    rewrite <- UCOS2_raw_rep_split_running;
    unfold UCOS2_inv; split; entailer!.
Qed.

Definition time_dly_prefix_frame environment saved_local sg caller mask state : Assertion :=
  sched_disabled_counter_frame sg state **
  time_dly_outside_resources environment saved_local sg caller mask state.

Lemma time_dly_closed_split_counters : forall environment critical saved_local sg caller mask state,
  task_suspend_closed environment critical saved_local sg caller mask state --||--
  (sg.(g_OSIntNesting) # UChar |-> os_sched_ints state **
   sg.(g_OSLockNesting) # UChar |-> os_sched_locks state **
   time_dly_prefix_frame environment saved_local sg caller mask state).
Proof.
  intros; rewrite time_dly_closed_inv_equiv, sched_disabled_inv_split_counters.
  unfold time_dly_prefix_frame; split; entailer!.
Qed.

Lemma time_dly_residual_eq : forall sg state tid target ticks,
  state.(TskState).(inUsedTaskStates) tid = Some target ->
  UCOS2_raw_rep_missing_task_storage_sched sg (time_dly_state state tid target ticks) =
  UCOS2_raw_rep_missing_task_storage_sched sg state.
Proof.
  intros sg state tid target ticks Htarget.
  unfold time_dly_state; destruct (Z.eqb ticks 0); [reflexivity|].
  unfold UCOS2_raw_rep_missing_task_storage_sched; simpl.
  rewrite (event.event_raw_rep_change_task_index sg state.(TskState)
    (glob_task_set_usedtask state.(TskState) tid (task_set_delay target ticks)) state.(EventState));
    [reflexivity|].
  apply event.event_wait_priority_agreement_encodes.
  eapply event.glob_task_set_usedtask_preserves_event_priority_agreement; [exact Htarget|reflexivity].
Qed.

Lemma time_dly_inv_merge_updated : forall sg state tid target ticks,
  time_dly_target_facts sg state tid target ->
  task_public_storage sg (time_dly_state state tid target ticks).(TskState) **
  sched_raw_rep sg (time_dly_state state tid target ticks).(TskState)
    (time_dly_state state tid target ticks).(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg state |--
  UCOS2_inv sg (time_dly_state state tid target ticks).
Proof.
  intros sg state tid target ticks [Hvalid [[Hlookup [_ [_ [_ Hready]]]] [Hptr [Hflag Hother]]]].
  apply UCOS2_inv_merge_updated_task_storage_sched.
  - apply time_dly_preserves_validity; assumption.
  - symmetry; apply time_dly_residual_eq; assumption.
Qed.

Definition time_dly_cleared_row := task_suspend_cleared_row.
Definition time_dly_updated_group := task_suspend_updated_group.

Definition time_dly_acquired_facts environment critical sg original mask ticks before saved
  active acquired tid target : Prop :=
  0 < ticks < 4294967296 /\ time_dly_noop ticks before = false /\
  time_dly_completed_calls environment critical sg original mask ticks before /\
  kernel_sched_ready_clients critical /\
  task_suspend_save_effect environment critical sg original active mask saved before acquired /\
  armv7a_irq_fiq_mask saved = mask /\
  time_dly_scheduler_source sg active acquired /\ time_dly_target_facts sg acquired tid target.

Definition time_dly_prefix_step environment critical sg caller mask ticks before returned current : Prop :=
  time_dly_prefix_program environment critical sg caller mask ticks before (true, returned) current.

Lemma time_dly_acquired_target_lookup : forall environment critical sg caller mask ticks before saved
  active acquired tid target,
  time_dly_acquired_facts environment critical sg caller mask ticks before saved active acquired tid target ->
  acquired.(TskState).(inUsedTaskStates) tid = Some target /\
  acquired.(SchedState).(curTaskID) = Some tid.
Proof.
  intros; unfold time_dly_acquired_facts, time_dly_target_facts, sched_current_ready_at in H; tauto.
Qed.

Lemma time_dly_acquired_restore_continuation : forall environment critical sg caller mask ticks before saved
  active acquired tid target returned current X,
  time_dly_acquired_facts environment critical sg caller mask ticks before saved active acquired tid target ->
  task_suspend_restore_effect environment critical sg active returned
    (time_dly_state acquired tid target ticks) current ->
  time_dly_safe environment critical sg caller mask ticks before X ->
  time_dly_prefix_step environment critical sg caller mask ticks before returned current /\
  time_dly_scheduler_source sg returned current /\
  time_dly_scheduler_safe environment critical sg returned mask current X.
Proof.
  intros environment critical sg caller mask ticks before saved active acquired tid target returned current X
    Hfacts Hrestore Hsafe.
  pose proof (time_dly_acquired_target_lookup _ _ _ _ _ _ _ _ _ _ _ _ Hfacts) as [Hlookup Hcurrent].
  destruct Hfacts as [Hticks [Hpositive [Hcompleted [Hclients [Hsave [Hmask [Hsource Htarget]]]]]]].
  assert (Hprefix : time_dly_prefix_step environment critical sg caller mask ticks before returned current).
  { eapply time_dly_prefix_delay; eassumption || reflexivity. }
  split; [exact Hprefix|]; split.
  - eapply (proj2 Hcompleted); [exact Hsave|exact Htarget|exact Hrestore|].
    apply time_dly_protected_scheduler_source; assumption.
  - exact (time_dly_prefix_safe_continuation _ _ _ _ _ _ _ true _ _ _ Hprefix Hsafe).
Qed.

Lemma time_dly_noop_call_post : forall environment critical saved_local sg caller mask ticks before frame X,
  time_dly_noop ticks before = true ->
  time_dly_safe environment critical sg caller mask ticks before X ->
  task_suspend_closed environment critical saved_local sg caller mask before ** frame |--
  time_dly_call_post environment critical saved_local sg caller mask ticks before frame X.
Proof.
  intros environment critical saved_local sg caller mask ticks before frame X Hnoop Hsafe.
  unfold time_dly_call_post; Exists caller before.
  pose proof (time_dly_noop_safe_return environment critical sg caller mask ticks before X Hnoop Hsafe).
  entailer!; unfold time_dly_result; rewrite Hnoop; auto.
Qed.

Lemma time_dly_schedule_call_post : forall environment critical saved_local sg caller mask ticks before
  checkpoint_call checkpoint frame X,
  time_dly_noop ticks before = false ->
  time_dly_prefix_program environment critical sg caller mask ticks before (true, checkpoint_call) checkpoint ->
  time_dly_scheduler_post environment critical saved_local sg checkpoint_call mask checkpoint X ** frame |--
  time_dly_call_post environment critical saved_local sg caller mask ticks before frame X.
Proof.
  intros environment critical saved_local sg caller mask ticks before checkpoint_call checkpoint frame X Hnoop Hprefix.
  unfold time_dly_scheduler_post at 1; Intros returned current.
  unfold time_dly_call_post; Exists returned current; entailer!.
  unfold time_dly_result; rewrite Hnoop; exists checkpoint_call, checkpoint; tauto.
Qed.
