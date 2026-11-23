Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_runtime_inv.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_unowned_history_spec.
Local Open Scope Z_scope.

(** C-level normal-return history. The actual registered source path and
    the selected platform's same-call/execution-return clause are kept
    separately. No arbitrary endpoint, waiter value or readiness fact is
    introduced here. The older ISA histories remain available as more
    detailed optional refinements. *)
Definition sem_pend_modular_call_history environment critical sg original before returned after : Prop :=
  kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    before false returned.(os_sched_call_origin) after /\
  kernel_call_normal_return original before returned after.

Definition sem_pend_save_call_history environment critical sg original before returned after : Prop :=
  kernel_call_save_history environment critical sg original before returned after \/
  sem_pend_modular_call_history environment critical sg original before returned after.

Definition sem_pend_restore_call_history environment critical sg original before returned after : Prop :=
  kernel_call_restore_history environment critical sg original before returned after \/
  sem_pend_modular_call_history environment critical sg original before returned after.

(** The no-capsule caller uses exactly the same registered C source and
    normal-return observation, without acquiring a Task environment or an
    Idle/ready premise. Its old instruction history remains an optional
    refinement. The spatial consumer must still supply returned CPU and
    context resources. *)
Definition sem_pend_unowned_return_history external platform critical sg original before returned after : Prop :=
  sem_pend_unowned_restore_history external platform critical sg original before returned after \/
  exists port,
    kernel_resumption_task_source_trace external port critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None original.(os_sched_call_origin)
      before false returned.(os_sched_call_origin) after /\
    kernel_call_normal_return original before returned after.

Lemma sem_pend_save_call_history_same_call : forall environment critical sg original before returned after,
  sem_pend_save_call_history environment critical sg original before returned after ->
  kernel_stack_call_same_call returned original.
Proof.
  intros * [Hsource|[_ [Hsame _]]].
  - eapply kernel_call_save_history_same_call; exact Hsource.
  - exact Hsame.
Qed.

Lemma sem_pend_restore_call_history_same_call : forall environment critical sg original before returned after,
  sem_pend_restore_call_history environment critical sg original before returned after ->
  kernel_stack_call_same_call returned original.
Proof.
  intros * [Hsource|[_ [Hsame _]]].
  - eapply kernel_call_restore_history_same_call; exact Hsource.
  - exact Hsame.
Qed.

(** These are the C environment's obligations between two normal call
    boundaries. Counter zero is not asserted at intermediate IRQ steps;
    Idle and the balanced control result must follow the admitted C/RG
    behavior. They are not part of the ARM normal-return clause. *)
Definition sem_pend_blocking_rely sg before after : Prop :=
  (task_idle_ready sg before.(TskState) -> task_idle_ready sg after.(TskState)) /\
  (before.(IntrState).(intNesting) = 0 /\ before.(IntrState).(lockNesting) = 0 ->
   after.(IntrState).(intNesting) = 0 /\ after.(IntrState).(lockNesting) = 0) /\
  (sched_current_consistency before.(TskState) before.(SchedState) ->
    sched_current_consistency after.(TskState) after.(SchedState)).

(** C/RG endpoint obligation for an interruptible Save returning to its
    caller. It preserves an already established Task-ready boundary, not
    a blocked intermediate stage. Idle is the initialized C runtime fact;
    balanced counters are a C control responsibility. These clauses are
    never attributed to the platform's same-call normal-return law. *)
Definition sem_pend_save_rely sg before after : Prop :=
  kernel_call_control_rely sg before after /\
  (kernel_running_idle_ready sg before -> kernel_running_idle_ready sg after) /\
  (sched_current_consistency before.(TskState) before.(SchedState) ->
    sched_current_consistency after.(TskState) after.(SchedState)) /\
  (forall tid, before.(SchedState).(curTaskID) = Some tid ->
    In tid before.(SchedState).(readyList) -> In tid after.(SchedState).(readyList)).
