Require Export Ucos2Verify.VC.code.task.spec.task_sw_hook_spec.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.

(** Select the checked hook while retaining the chosen architecture instance.
    These definitions only reindex existing records.  Their resource families,
    transitions and laws are copied from the supplied ABI; no new port law or
    runtime hook-binding premise is introduced. *)
Definition task_sw_hook_continuation_abi external platform port
  (abi : Armv7aContinuationABI external platform port) :
  Armv7aContinuationABI (task_sw_hook_external external) platform port :=
  @Build_Armv7aContinuationABI (task_sw_hook_external external) platform port
    (@armv7a_dormant_continuation external platform port abi)
    (@armv7a_initial_execution external platform port abi)
    (@armv7a_save_transition external platform port abi)
    (@armv7a_restore_transition external platform port abi)
    (@armv7a_save_transition_observations external platform port abi)
    (@armv7a_save_transition_resources external platform port abi)
    (@armv7a_restore_transition_resources external platform port abi).

Definition task_sw_hook_task_context_abi external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi) :
  Armv7aTaskContextABI (task_sw_hook_external external) platform port
    (task_sw_hook_continuation_abi external platform port abi) :=
  @Build_Armv7aTaskContextABI (task_sw_hook_external external) platform port
    (task_sw_hook_continuation_abi external platform port abi)
    (@armv7a_task_switch_control external platform port abi task_abi)
    (@armv7a_task_capture_transition external platform port abi task_abi)
    (@armv7a_task_restore_transition external platform port abi task_abi)
    (@armv7a_task_capture_resources external platform port abi task_abi)
    (@armv7a_task_dormant_restore_source external platform port abi task_abi)
    (@armv7a_task_restore_resources external platform port abi task_abi).

Definition task_sw_hook_initial_entry_abi external platform port
  (abi : Armv7aContinuationABI external platform port)
  (initial : Armv7aInitialEntryABI external platform port abi) :
  Armv7aInitialEntryABI (task_sw_hook_external external) platform port
    (task_sw_hook_continuation_abi external platform port abi) :=
  @Build_Armv7aInitialEntryABI (task_sw_hook_external external) platform port
    (task_sw_hook_continuation_abi external platform port abi)
    (@armv7a_initial_restore_source external platform port abi initial)
    (@armv7a_initial_restore_resources external platform port abi initial).

Definition task_sw_hook_call_environment (environment : TaskStackCallEnvironment) :
  TaskStackCallEnvironment :=
  {| task_stack_call_external :=
       task_sw_hook_external environment.(task_stack_call_external);
     task_stack_call_platform := environment.(task_stack_call_platform);
     task_stack_call_port := environment.(task_stack_call_port);
     task_stack_call_continuations :=
       task_sw_hook_continuation_abi environment.(task_stack_call_external)
         environment.(task_stack_call_platform) environment.(task_stack_call_port)
         environment.(task_stack_call_continuations) |}.

Lemma task_sw_hook_call_environment_external_eq : forall environment,
  (task_sw_hook_call_environment environment).(task_stack_call_external) =
    task_sw_hook_external environment.(task_stack_call_external).
Proof. intros; reflexivity. Qed.

Lemma task_sw_hook_call_environment_platform_eq : forall environment,
  (task_sw_hook_call_environment environment).(task_stack_call_platform) =
    environment.(task_stack_call_platform).
Proof. intros; reflexivity. Qed.

Lemma task_sw_hook_call_environment_port_eq : forall environment,
  (task_sw_hook_call_environment environment).(task_stack_call_port) =
    environment.(task_stack_call_port).
Proof. intros; reflexivity. Qed.

Lemma task_sw_hook_call_environment_continuations_eq : forall environment,
  (task_sw_hook_call_environment environment).(task_stack_call_continuations) =
    task_sw_hook_continuation_abi environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations).
Proof. intros; reflexivity. Qed.

Lemma task_sw_hook_call_environment_source_binding : forall environment,
  task_sw_hook_source_binding
    (task_sw_hook_call_environment environment).(task_stack_call_external).
Proof. intros; apply task_sw_hook_external_source_binding. Qed.

Lemma task_sw_hook_call_environment_step : forall environment sg state,
  kernel_client_step
    (task_sw_hook_call_environment environment).(task_stack_call_external).(os_sched_hook_action)
    sg state state.
Proof. intros; apply task_sw_hook_external_step. Qed.

Lemma task_sw_hook_call_environment_stops_false : forall environment invocation,
  kernel_client_stops
    (task_sw_hook_call_environment environment).(task_stack_call_external).(os_sched_hook_action)
    invocation = false.
Proof. intros; apply task_sw_hook_external_stops_false. Qed.

(** Physical context and parked-stack ownership do not change when the
    configured callback is selected.  These are representation equalities,
    not transports of arbitrary old source traces or safeExec programs. *)
Lemma task_sw_hook_call_environment_context_resources_eq : forall environment call,
  task_tcb_init_stack_context (task_sw_hook_call_environment environment) call =
    task_tcb_init_stack_context environment call.
Proof. intros; reflexivity. Qed.

Lemma task_sw_hook_call_environment_capsules_eq : forall environment state,
  task_tcb_init_stack_capsules (task_sw_hook_call_environment environment) state =
    task_tcb_init_stack_capsules environment state.
Proof. intros; reflexivity. Qed.

(** The hook cut is the real state after saving the outgoing SP.  The
    architecture save and the selected destination remain source obligations;
    the checked identity callback supplies exactly the intervening action. *)
Lemma task_sw_hook_call_environment_switch_source :
  forall environment sg entry context sp outgoing incoming resumed,
  os_sched_requests_switch entry = true ->
  environment.(task_stack_call_external).(os_sched_arch_save_source) context sp outgoing ->
  os_sched_destination_binding
    (task_sw_hook_call_environment environment).(task_stack_call_external) context outgoing
    (os_sched_save_current_sp (os_sched_prefix_state entry)
      context.(os_sched_call_stack).(stackLeaseSlot) sp) incoming resumed ->
  os_sched_switch_source
    (task_sw_hook_call_environment environment).(task_stack_call_external) sg entry context
    (os_sched_install_context context outgoing incoming
      (os_sched_save_current_sp (os_sched_prefix_state entry)
        context.(os_sched_call_stack).(stackLeaseSlot) sp)).
Proof.
  intros environment sg entry context sp outgoing incoming resumed
    Hrequested Hsaved Hdestination.
  unfold os_sched_switch_source.
  split; [exact Hrequested|].
  exists sp, outgoing,
    (os_sched_save_current_sp (os_sched_prefix_state entry)
      context.(os_sched_call_stack).(stackLeaseSlot) sp), incoming, resumed.
  split; [exact Hsaved|].
  split; [apply task_sw_hook_call_environment_step|].
  split; [exact Hdestination|reflexivity].
Qed.

