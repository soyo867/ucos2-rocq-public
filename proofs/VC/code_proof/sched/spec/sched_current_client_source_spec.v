Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_status Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.flag Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Import TaskStateDef ListNotations.
Local Open Scope Z_scope.

(** Reuse the actual one-TCB update and its lookup.  This permits changes
    to readiness, waiting state and delay, while retaining the priority
    which the source did not write. *)
Lemma sched_current_consistency_update_task : forall before after slot old updated,
  before.(TskState).(inUsedTaskStates) slot = Some old ->
  updated.(curPrio) = old.(curPrio) ->
  after.(TskState) = glob_task_set_usedtask before.(TskState) slot updated ->
  after.(SchedState).(curTaskID) = before.(SchedState).(curTaskID) ->
  after.(SchedState).(curSchedPrio) = before.(SchedState).(curSchedPrio) ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros before after slot old updated Hold Hpriority Htasks Hcurrent Hcache Hconsistent.
  eapply sched_current_consistency_fields_frame; [exact Hcurrent|exact Hcache| |exact Hconsistent].
  intros current node Hslot Hnode; rewrite Htasks.
  destruct (Z.eq_dec current slot) as [->|Hother].
  - rewrite Hold in Hnode; inversion Hnode; subst node.
    exists updated; split; [|exact Hpriority].
    cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
  - exists node; split; [|reflexivity].
    cbn [glob_task_set_usedtask inUsedTaskStates].
    rewrite (proj2 (Z.eqb_neq current slot) Hother); exact Hnode.
Qed.

Lemma sched_wake_by_status_current_cache_frame : forall sg tasks sched slot bits,
  (sched_wake_by_status sg tasks sched slot bits).(curTaskID) = sched.(curTaskID) /\
  (sched_wake_by_status sg tasks sched slot bits).(curSchedPrio) = sched.(curSchedPrio).
Proof.
  intros; unfold sched_wake_by_status; destruct (task_status_is_suspended bits);
    split; reflexivity.
Qed.

Lemma task_suspend_state_preserves_current_consistency : forall before slot old,
  before.(TskState).(inUsedTaskStates) slot = Some old ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency (task_suspend_state before slot old).(TskState)
    (task_suspend_state before slot old).(SchedState).
Proof.
  intros before slot old Hlookup Hconsistent.
  eapply sched_current_consistency_update_task with (updated := task_suspend old);
    [exact Hlookup|reflexivity|reflexivity|reflexivity|reflexivity|exact Hconsistent].
Qed.

Lemma task_resume_state_preserves_current_consistency : forall sg before slot old,
  before.(TskState).(inUsedTaskStates) slot = Some old ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency (task_resume_state sg before slot old).(TskState)
    (task_resume_state sg before slot old).(SchedState).
Proof.
  intros sg before slot old Hlookup Hconsistent.
  assert (Hframe := sched_wake_by_status_current_cache_frame sg before.(TskState)
    before.(SchedState) slot (encode_task_status (task_resume old).(stat))).
  eapply sched_current_consistency_update_task with (updated := task_resume old);
    [exact Hlookup|reflexivity|reflexivity| | |exact Hconsistent].
  all: cbn [task_resume_state replace_TskS replace_SchedS SchedState];
    unfold sched_resume_task; destruct (task_resume_ready_test old); try reflexivity; tauto.
Qed.

Lemma task_suspend_critical_preserves_current_consistency : forall sg priority before result after,
  task_suspend_critical sg priority before result after ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros sg priority before result after [current [node [_ [_ [_ Hstep]]]]] Hconsistent.
  destruct (before.(TskState).(prioTbl) (fst (task_suspend_selection sg priority node))).
  - destruct Hstep as [_ ->]; exact Hconsistent.
  - destruct Hstep as [_ ->]; exact Hconsistent.
  - destruct Hstep as [old [Hlookup [_ ->]]].
    eapply task_suspend_state_preserves_current_consistency; eassumption.
Qed.

Lemma task_resume_critical_preserves_current_consistency : forall sg priority before result after,
  task_resume_critical sg priority before result after ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros sg priority before result after [_ Hstep] Hconsistent.
  destruct (before.(TskState).(prioTbl) priority).
  - destruct Hstep as [_ ->]; exact Hconsistent.
  - destruct Hstep as [_ ->]; exact Hconsistent.
  - destruct Hstep as [old [Hlookup Hstep]]; destruct (task_is_suspended old.(stat)).
    + destruct Hstep as [_ ->]; eapply task_resume_state_preserves_current_consistency; eassumption.
    + destruct Hstep as [_ ->]; exact Hconsistent.
Qed.

Lemma task_suspend_client_preserves_current_consistency : forall actor priority sg before after,
  kernel_client_step (task_suspend_critical_client actor priority) sg before after ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros actor priority sg before after [_ [result Hstep]] Hconsistent.
  eapply task_suspend_critical_preserves_current_consistency; eassumption.
Qed.

Lemma task_resume_client_preserves_current_consistency : forall actor priority sg before after,
  kernel_client_step (task_resume_critical_client actor priority) sg before after ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros actor priority sg before after [_ [result Hstep]] Hconsistent.
  eapply task_resume_critical_preserves_current_consistency; eassumption.
Qed.

Lemma flag_wake_state_preserves_current_consistency : forall sg before waiter flags old bits result,
  before.(TskState).(inUsedTaskStates) waiter.(flagTask) = Some old ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency (flag_wake_state sg before waiter flags old bits result).(TskState)
    (flag_wake_state sg before waiter flags old bits result).(SchedState).
Proof.
  intros sg before waiter flags old bits result Hlookup Hconsistent.
  eapply sched_current_consistency_update_task with (updated := task_flag_wake old bits result);
    [exact Hlookup|reflexivity|reflexivity|reflexivity|reflexivity|exact Hconsistent].
Qed.

Lemma flag_task_rdy_preserves_current_consistency : forall sg before pointer bits result schedule after,
  flag_task_rdy sg before pointer bits result = Some (schedule, after) ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros sg before pointer bits result schedule after Hstep Hconsistent.
  destruct (flag_task_rdy_result sg before pointer bits result schedule after Hstep)
    as [waiter [flags [old [Hunlink [Hlookup [-> Hschedule]]]]]].
  eapply flag_wake_state_preserves_current_consistency; eassumption.
Qed.

Lemma event_wake_state_preserves_current_consistency : forall sg before eid event slot old kind message result,
  before.(TskState).(inUsedTaskStates) slot = Some old ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency (event_wake_state sg before eid event slot old kind message result).(TskState)
    (event_wake_state sg before eid event slot old kind message result).(SchedState).
Proof.
  intros sg before eid event slot old kind message result Hlookup Hconsistent.
  assert (Hframe := sched_wake_by_status_current_cache_frame sg before.(TskState)
    before.(SchedState) slot (encode_task_status (task_event_wake_single old kind message result).(stat))).
  eapply sched_current_consistency_update_task with (updated := task_event_wake_single old kind message result);
    [exact Hlookup|reflexivity|reflexivity|exact (proj1 Hframe)|exact (proj2 Hframe)|exact Hconsistent].
Qed.

Lemma event_task_rdy_preserves_current_consistency : forall sg before eid kind message result priority after,
  event_task_rdy sg before eid kind message result = Some (priority, after) ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros sg before eid kind message result priority after Hstep Hconsistent.
  unfold event_task_rdy in Hstep.
  destruct (before.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
  destruct (before.(TskState).(prioTbl) (event_wait_priority before.(TskState) event))
    as [| |slot]; try discriminate.
  destruct (before.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hlookup;
    [|discriminate].
  inversion Hstep; subst after.
  eapply event_wake_state_preserves_current_consistency; eassumption.
Qed.

Lemma tick_task_step_preserves_current_consistency : forall sg before slot old,
  before.(TskState).(inUsedTaskStates) slot = Some old ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency (tick_task_step sg slot old before).(TskState)
    (tick_task_step sg slot old before).(SchedState).
Proof.
  intros sg before slot old Hlookup Hconsistent.
  assert (Hpriority : (tick_task_update old).(curPrio) = old.(curPrio)).
  { exact (proj1 (proj2 (proj2 (tick_task_preserves_non_timeout_fields old)))). }
  assert (Hframe := sched_wake_by_status_current_cache_frame sg before.(TskState)
    before.(SchedState) slot (encode_task_status (tick_task_update old).(stat))).
  eapply sched_current_consistency_update_task with (updated := tick_task_update old);
    [exact Hlookup|exact Hpriority|apply tick_task_step_task_state_eq; exact Hlookup| | |exact Hconsistent].
  all: unfold tick_task_step, sched_wake_by_status; cbn zeta;
    repeat match goal with
    | |- context [if ?condition then _ else _] => destruct condition
    end; reflexivity.
Qed.

Lemma time_tick_scan_preserves_current_consistency : forall sg visited before,
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency (time_tick_scan sg before visited).(TskState)
    (time_tick_scan sg before visited).(SchedState).
Proof.
  intros sg visited; induction visited as [|slot rest IH]; intros before Hconsistent;
    [exact Hconsistent|].
  change (sched_current_consistency (time_tick_scan sg (time_tick_visit sg before slot) rest).(TskState)
    (time_tick_scan sg (time_tick_visit sg before slot) rest).(SchedState)).
  apply IH; unfold time_tick_visit.
  destruct (before.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hlookup;
    [eapply tick_task_step_preserves_current_consistency; eassumption|exact Hconsistent].
Qed.

(** The application hook is outside this theorem.  The theorem begins at
    the actual returned hook state and covers the clock and TCB scan. *)
Lemma time_tick_serialized_after_hook_preserves_current_consistency : forall sg before,
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency (time_tick_serialized_after_hook sg before).(TskState)
    (time_tick_serialized_after_hook sg before).(SchedState).
Proof.
  intros sg before Hconsistent; unfold time_tick_serialized_after_hook.
  destruct (time_tick_process_tasks before);
    [apply time_tick_scan_preserves_current_consistency|]; exact Hconsistent.
Qed.

(** Runtime control observations come from each actual source operation.
    None of these statements asserts that an arbitrary external client or
    the Tick application hook preserves OSRunning. *)
Lemma task_suspend_critical_running_eq : forall sg priority before result after,
  task_suspend_critical sg priority before result after ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros sg priority before result after [current [node [_ [_ [_ Hstep]]]]].
  destruct (before.(TskState).(prioTbl) (fst (task_suspend_selection sg priority node))).
  - destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [old [_ [_ ->]]]; reflexivity.
Qed.

Lemma task_resume_critical_running_eq : forall sg priority before result after,
  task_resume_critical sg priority before result after ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros sg priority before result after [_ Hstep].
  destruct (before.(TskState).(prioTbl) priority).
  - destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [old [_ Hstep]]; destruct (task_is_suspended old.(stat)).
    + destruct Hstep as [_ ->].
      unfold task_resume_state, sched_resume_task.
      destruct (task_resume_ready_test old); [|reflexivity].
      apply sched_wake_by_status_running_eq.
    + destruct Hstep as [_ ->]; reflexivity.
Qed.

Lemma flag_task_rdy_running_eq : forall sg before pointer bits result schedule after,
  flag_task_rdy sg before pointer bits result = Some (schedule, after) ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros sg before pointer bits result schedule after Hstep.
  destruct (flag_task_rdy_result sg before pointer bits result schedule after Hstep)
    as [waiter [flags [old [Hunlink [Hlookup [-> Hschedule]]]]]].
  reflexivity.
Qed.

Lemma event_task_rdy_running_eq : forall sg before eid kind message result priority after,
  event_task_rdy sg before eid kind message result = Some (priority, after) ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros sg before eid kind message result priority after Hstep.
  unfold event_task_rdy in Hstep.
  destruct (before.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
  destruct (before.(TskState).(prioTbl) (event_wait_priority before.(TskState) event))
    as [| |slot]; try discriminate.
  destruct (before.(TskState).(inUsedTaskStates) slot) as [old|]; [|discriminate].
  inversion Hstep; subst after.
  apply sched_wake_by_status_running_eq.
Qed.

Lemma tick_task_step_running_eq : forall sg before slot old,
  (tick_task_step sg slot old before).(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros; unfold tick_task_step, sched_wake_by_status; cbn zeta;
    repeat match goal with
    | |- context [if ?condition then _ else _] => destruct condition
    end; reflexivity.
Qed.

Lemma time_tick_serialized_after_hook_running_eq : forall sg before,
  (time_tick_serialized_after_hook sg before).(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros; unfold time_tick_serialized_after_hook.
  destruct (time_tick_process_tasks before); [rewrite time_tick_scan_running_eq|]; reflexivity.
Qed.

(** The existing source family includes allocation, private writes,
    publication and invocation retirement.  Even retirement does not
    write OSRunning; no current-TCB consistency is asserted for it. *)
Lemma task_creation_client_running_eq : forall action sg before after,
  kernel_client_step (task_creation_client action) sg before after ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros action sg before after [Hguard [Hname ->]]; destruct action; reflexivity.
Qed.
