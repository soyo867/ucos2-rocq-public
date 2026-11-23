Require Import Coq.ZArith.ZArith.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Import TaskStateDef.
Local Open Scope Z_scope.

(** Local TaskDel effects preserve the running flag even when deleting
    the current task.  No current-TCB liveness, interrupt-counter frame,
    complete API return or phase-rely property is asserted here. *)
Lemma task_delete_ready_state_sched_eq : forall before tid,
  (task_delete_ready_state before tid).(SchedState) =
    sched_remove_ready_task before.(SchedState) tid.
Proof. intros; reflexivity. Qed.

Lemma task_delete_prepare_single_wait_sched_eq : forall before tid old after loan,
  task_delete_prepare_single_wait before tid old = Some (after, loan) ->
  after.(SchedState) = sched_remove_ready_task before.(SchedState) tid.
Proof.
  intros before tid old after loan Hstep.
  destruct (task_delete_prepare_single_wait_frame before tid old after loan Hstep)
    as [node [Hstate Hfields]].
  rewrite Hstate; reflexivity.
Qed.

Lemma task_delete_prepare_single_wait_running_eq : forall before tid old after loan,
  task_delete_prepare_single_wait before tid old = Some (after, loan) ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros before tid old after loan Hstep.
  rewrite (task_delete_prepare_single_wait_sched_eq before tid old after loan Hstep).
  reflexivity.
Qed.

Lemma task_delete_event_state_sched_eq : forall before tid node eid event,
  (task_delete_event_state before tid node eid event).(SchedState) = before.(SchedState).
Proof. intros; reflexivity. Qed.

Lemma task_delete_flag_state_sched_eq : forall before tid node flags,
  (task_delete_flag_state before tid node flags).(SchedState) = before.(SchedState).
Proof. intros; reflexivity. Qed.

Lemma task_delete_prepare_state_sched_eq : forall before tid node,
  (task_delete_prepare_state before tid node).(SchedState) = before.(SchedState).
Proof. intros; reflexivity. Qed.

Lemma task_delete_event_unlinked_sched_eq : forall before tid node after updated,
  task_delete_event_unlinked before tid node after updated ->
  after.(SchedState) = before.(SchedState).
Proof.
  intros before tid node after updated Hstep.
  unfold task_delete_event_unlinked in Hstep.
  destruct node.(eventPtr) as [eid|].
  - destruct Hstep as [event [Hlookup [-> Hupdated]]]; reflexivity.
  - destruct Hstep as [-> Hupdated]; reflexivity.
Qed.

Lemma task_delete_flag_unlinked_sched_eq : forall before tid node after updated loan,
  task_delete_flag_unlinked before tid node after updated loan ->
  after.(SchedState) = before.(SchedState).
Proof.
  intros before tid node after updated loan Hstep.
  unfold task_delete_flag_unlinked in Hstep.
  destruct (Z.eqb node.(tcbFlagNode) 0).
  - destruct Hstep as [-> Hrest]; reflexivity.
  - destruct Hstep as [waiter [flags [Hunlink [-> Hrest]]]]; reflexivity.
Qed.

Lemma task_delete_locked_sched_eq : forall prepared,
  (task_delete_locked prepared).(SchedState) = prepared.(SchedState).
Proof. intros; reflexivity. Qed.

Lemma task_delete_released_sched_eq : forall prepared resumed,
  (task_delete_released prepared resumed).(SchedState) = resumed.(SchedState).
Proof. intros; reflexivity. Qed.

Lemma task_delete_recycled_sched_eq : forall sg tid priority node name resumed added,
  (task_delete_recycled sg tid priority node name resumed added).(SchedState) =
    resumed.(SchedState).
Proof. intros; reflexivity. Qed.

Lemma task_delete_cut_sched_eq : forall sg prepared resumed tid priority node name,
  (task_delete_cut sg prepared resumed tid priority node name).(SchedState) =
    resumed.(SchedState).
Proof. intros; reflexivity. Qed.
