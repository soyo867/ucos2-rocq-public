Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Local Open Scope Z_scope.

(** Admission for the selected C source's possible successful runtime
    path. Priority-invalid and ISR calls retain their original error
    domain; Boot has no running-task obligation. A locked caller need not
    be ready. Identity and availability refer to THIS entry state, never
    to a future return. The public C annotation consumes this predicate
    before its first Save and carries it to the guarded source path. *)
Definition task_create_runtime_call_input args call state : Prop :=
  args.(createPriority) <= 63 -> state.(IntrState).(intNesting) = 0 ->
  state.(SchedState).(isRunning) = true ->
  kernel_call_task_source call state /\ kernel_call_stack_available call state.

(** The already supported register/selected/sequential entry packet is
    a real producer. Its caller-ready field is deliberately not retained
    in the weaker public runtime admission used by this C API. *)
Lemma task_create_source_entry_runtime_call_input : forall sg args name call state,
  task_create_source_entry sg args name call state ->
  task_create_runtime_call_input args call state.
Proof.
  intros sg args name call state Hentry Hpriority Hnesting Hrunning.
  split.
  - eapply task_create_source_entry_running_source; eassumption.
  - destruct (proj2 Hentry) as [Horigin Hstage].
    unfold kernel_call_stack_available.
    destruct call.(os_sched_call_origin) as [|slot generation] eqn:Hcall; [exact I|].
    destruct Hstage as [Hslot [Hgeneration [Habsent Hready]]].
    unfold task_stack_key in Habsent.
    rewrite <- Hslot, <- Hgeneration in Habsent; exact Habsent.
Qed.

Lemma task_create_runtime_call_input_priority_error : forall args call state,
  63 < args.(createPriority) -> task_create_runtime_call_input args call state.
Proof. intros args call state Hpriority Hrange; lia. Qed.

Lemma task_create_runtime_call_input_isr : forall args call state,
  state.(IntrState).(intNesting) <> 0 -> task_create_runtime_call_input args call state.
Proof. intros args call state Hnesting Hpriority Hzero; contradiction. Qed.

Lemma task_create_runtime_call_input_boot : forall args call state,
  state.(SchedState).(isRunning) = false -> task_create_runtime_call_input args call state.
Proof. intros args call state Hboot Hpriority Hnesting Hrunning; congruence. Qed.

(** The source's first Save has already returned, and the actual ISR
    guard has selected the zero-nesting branch. Control transport is a
    C rely fact; only same-call availability is consumed from the shared
    platform return contract. No future return or caller readiness is
    assumed. *)
Lemma task_create_runtime_call_after_save : forall sg args original before returned acquired,
  task_create_runtime_call_input args original before ->
  args.(createPriority) <= 63 ->
  kernel_call_control_rely sg before acquired ->
  kernel_call_normal_return original before returned acquired ->
  task_tcb_init_stack_source_preserved original before acquired ->
  acquired.(IntrState).(intNesting) = 0 ->
  acquired.(SchedState).(isRunning) = true ->
  kernel_call_task_source returned acquired /\ kernel_call_stack_available returned acquired.
Proof.
  intros sg args original before returned acquired Hadmit Hpriority
    [Hrunning Hintr] [Hsame Havailable] Hsource Hnesting Hstarted.
  assert (Hinitial_nesting : before.(IntrState).(intNesting) = 0)
    by (rewrite <- Hintr; exact Hnesting).
  destruct (Hadmit Hpriority Hinitial_nesting ltac:(congruence)) as [Horigin Hnone].
  split.
  - apply (proj2 (task_tcb_init_stack_same_call_source_iff returned original acquired Hsame)).
    apply Hsource; exact Horigin.
  - apply Havailable; exact Hnone.
Qed.
