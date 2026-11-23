Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.VC.code.event.spec.event_pend_multi_carrier_spec.
Import ListNotations UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma event_pend_multi_ids_valid_length : forall sg pointers ids,
  event_pend_multi_ids_valid sg pointers ids -> Zlength pointers = Zlength ids.
Proof.
  intros sg pointers ids [Hp Hids].
  rewrite Hp, !Zlength_correct, List.length_map; reflexivity.
Qed.

Lemma event_pend_multi_scan_loop_split_ids :
  forall sg entry pointers ids index events ready messages waiting,
  event_pend_multi_scan_loop sg entry pointers ids index events ready messages waiting |--
  coq_prop (event_pend_multi_ids_valid sg pointers ids) &&
  event_pend_multi_scan_loop sg entry pointers ids index events ready messages waiting.
Proof.
  intros; unfold event_pend_multi_scan_loop; entailer!; tauto.
Qed.

Lemma event_pend_multi_scan_finished_output_bounds :
  forall sg entry pointers ids events ready messages waiting code
    ready_base messages_base old_ready old_messages,
  event_pend_multi_ids_valid sg pointers ids ->
  event_pend_multi_output_limits ready_base messages_base pointers old_ready old_messages ->
  event_pend_multi_scan_finished sg entry ids events ready messages waiting code |--
  coq_prop (0 <= Zlength ready < Zlength old_ready /\
      0 <= Zlength messages <= Zlength old_messages) &&
  event_pend_multi_scan_finished sg entry ids events ready messages waiting code.
Proof.
  intros sg entry pointers ids events ready messages waiting code
    ready_base messages_base old_ready old_messages Hids Hlimits.
  pose proof (event_pend_multi_ids_valid_length sg pointers ids Hids) as Hlength.
  unfold event_pend_multi_scan_finished; Intros.
  match goal with Hscan : event_pend_multi_scan _ _ _ _ = Some _ |- _ =>
    pose proof (event_pend_multi_scan_lengths _ _ _ _ _ Hscan) as Hbounds end.
  cbn in Hbounds.
  pose proof (Zlength_nonneg ready); pose proof (Zlength_nonneg messages).
  unfold event_pend_multi_output_limits in Hlimits.
  rewrite !Zlength_correct in *; unfold addr in *; entailer!; lia.
Qed.

(** Only the original entry identity is retained. Neither definition says
    that a scheduled/resumed task is current, alive, or the same generation.
    Those properties still need the actual scheduler/Save source producer. *)
Definition event_pend_multi_blocked_task_checkpoint (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (tid : TaskID) (ids : list EventID)
  (base timeout : Z) (waiting : UCOS2_Verify_State) : Assertion :=
  coq_prop (entry.(SchedState).(curTaskID) = Some tid) &&
  event_pend_multi_blocked_checkpoint sg entry ids base timeout waiting.

Definition event_pend_multi_schedule_task_checkpoint
  (external : OsSchedExternalResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (call returned : OsSchedCallContext)
  (entry : UCOS2_Verify_State) (tid : TaskID) (ids : list EventID)
  (base timeout : Z) (scheduled : UCOS2_Verify_State) : Assertion :=
  coq_prop (entry.(SchedState).(curTaskID) = Some tid) &&
  event_pend_multi_schedule_checkpoint external critical sg call returned
    entry ids base timeout scheduled.

Lemma event_pend_multi_blocked_task_checkpoint_equiv :
  forall sg entry ids base timeout waiting,
  event_pend_multi_blocked_checkpoint sg entry ids base timeout waiting --||--
  EX tid, event_pend_multi_blocked_task_checkpoint sg entry tid ids base timeout waiting.
Proof.
  intros; unfold event_pend_multi_blocked_task_checkpoint,
    event_pend_multi_blocked_checkpoint; split.
  - Intros.
    match goal with H : exists result tid task, _ |- _ =>
      pose proof H as Hfields; destruct Hfields as [result [tid [task Hfields]]] end.
    Exists tid; entailer!; tauto.
  - Intros tid; entailer!.
Qed.

Lemma event_pend_multi_schedule_task_checkpoint_equiv :
  forall external critical sg call returned entry ids base timeout scheduled,
  event_pend_multi_schedule_checkpoint external critical sg call returned
    entry ids base timeout scheduled --||--
  EX tid, event_pend_multi_schedule_task_checkpoint external critical sg call returned
    entry tid ids base timeout scheduled.
Proof.
  intros; unfold event_pend_multi_schedule_task_checkpoint,
    event_pend_multi_schedule_checkpoint; split.
  - Intros waiting sched_entry.
    unfold event_pend_multi_blocked_checkpoint; Intros.
    match goal with H : exists result tid task, _ |- _ =>
      pose proof H as Hfields; destruct Hfields as [result [tid [task Hfields]]] end.
    Exists tid waiting sched_entry; entailer!; tauto.
  - Intros tid waiting sched_entry; Exists waiting sched_entry; entailer!.
Qed.

Lemma event_pend_multi_blocked_task_checkpoint_intro :
  forall sg entry tid ids base timeout waiting,
  entry.(SchedState).(curTaskID) = Some tid ->
  event_pend_multi_blocked_checkpoint sg entry ids base timeout waiting |--
  event_pend_multi_blocked_task_checkpoint sg entry tid ids base timeout waiting.
Proof.
  intros; unfold event_pend_multi_blocked_task_checkpoint; entailer!.
Qed.

Lemma event_pend_multi_schedule_task_checkpoint_intro :
  forall external critical sg call returned entry tid ids base timeout scheduled,
  entry.(SchedState).(curTaskID) = Some tid ->
  event_pend_multi_schedule_checkpoint external critical sg call returned
    entry ids base timeout scheduled |--
  event_pend_multi_schedule_task_checkpoint external critical sg call returned
    entry tid ids base timeout scheduled.
Proof.
  intros; unfold event_pend_multi_schedule_task_checkpoint; entailer!.
Qed.
