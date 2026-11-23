Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Shared C-facing RESOURCE interfaces. They do not install a callee
    contract or add CPU laws. The resource parameter can be the selected
    or full program owner, with the whole private ECB pool when present.

    [active] is the actual source world's coverage exception; it is not
    inferred from current/ready and does not assert an absent map entry.
    None admits Boot/no-current worlds. Live IRQ producers separately
    establish their required current/generation/absent-key bindings.
    No new state Record, lifecycle field or platform law is introduced. *)
Definition kernel_stack_call_closed {external platform port}
  (abi : Armv7aContinuationABI external platform port) resources sg active call mask state : Assertion :=
  kernel_call_execution_owned external platform call mask **
    kernel_stack_inv abi resources sg active state.

(** [acquired] is the Save history index of the masked token; [state] is
    the current kernel state, which can change during the critical body.
    The same physical owner is handed to Restore, not privately framed
    across its possible interrupt/switch interval. *)
Definition kernel_stack_call_masked {external platform port}
  (abi : Armv7aContinuationABI external platform port) resources critical sg active call saved acquired state : Assertion :=
  critical_region_masked platform critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) saved acquired ** os_sched_context_resources external call **
    kernel_stack_inv abi resources sg active state.

(** An actual returning Save supplies the source history AND the complete
    resource owner. Merely proving the logical history cannot establish
    this assertion. The matching source producers live separately. *)
Definition kernel_stack_call_save_post {external platform port}
  (abi : Armv7aContinuationABI external platform port) resources critical sg active original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (kernel_call_save_source external port critical sg original returned mask saved before acquired) &&
    kernel_stack_call_masked abi resources critical sg active returned saved acquired acquired.

Definition kernel_stack_call_return_source external port critical sg original released returned current : Prop :=
  kernel_resumption_task_source_trace external port critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin) released false
    returned.(os_sched_call_origin) current /\
  returned.(os_sched_call_invocation) = original.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = original.(os_sched_call_origin) /\
  returned.(os_sched_call_stack) = original.(os_sched_call_stack).

Definition kernel_stack_call_restore_post {external platform port}
  (abi : Armv7aContinuationABI external platform port) resources critical sg active original mask released : Assertion :=
  EX returned current,
    coq_prop (kernel_stack_call_return_source external port critical sg original released returned current) &&
    kernel_stack_call_closed abi resources sg active returned mask current.

Lemma kernel_stack_call_save_post_open : forall external platform port
  (abi : Armv7aContinuationABI external platform port) resources critical sg active original mask saved before,
  kernel_stack_call_save_post abi resources critical sg active original mask saved before |--
  EX returned acquired,
    coq_prop (kernel_call_save_source external port critical sg original returned mask saved before acquired) &&
    (critical_region_masked platform critical sg returned.(os_sched_call_invocation)
       returned.(os_sched_call_origin) saved acquired ** os_sched_context_resources external returned **
     kernel_stack_inv abi resources sg active acquired).
Proof. intros; reflexivity. Qed.

Lemma kernel_stack_call_restore_post_open : forall external platform port
  (abi : Armv7aContinuationABI external platform port) resources critical sg active original mask released,
  kernel_stack_call_restore_post abi resources critical sg active original mask released |--
  EX returned current,
    coq_prop (kernel_stack_call_return_source external port critical sg original released returned current) &&
    (kernel_call_execution_owned external platform returned mask ** kernel_stack_inv abi resources sg active current).
Proof. intros; reflexivity. Qed.
