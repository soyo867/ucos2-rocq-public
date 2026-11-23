Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** [checkpoint] is the state after the exact semaphore count or task
    cleanup stores. The resource state at the eventual return is selected
    by the actual Restore history. In particular it is not identified
    with [checkpoint], nor chosen independently of the source execution.

    The error cell is the caller-owned cell carried through that same
    execution. This interface is consumed by the common cleanup source;
    it does not strengthen a generic Restore callee's Ensure. *)
Definition sem_pend_restore_call_post environment critical sg original mask
  checkpoint perr error : Assertion :=
  perr # UChar |-> error **
  kernel_stack_call_history_restore_post environment.(task_stack_call_continuations)
    kernel_program_inv sg (task_stack_call_active_key original)
    (kernel_call_restore_history environment critical sg) original mask checkpoint.

Lemma sem_pend_restore_call_post_intro : forall environment critical sg
  original returned mask checkpoint current perr error,
  kernel_call_restore_history environment critical sg original checkpoint returned current ->
  kernel_stack_call_same_call returned original ->
  kernel_stack_call_closed environment.(task_stack_call_continuations) kernel_program_inv sg
    (task_stack_call_active_key original) returned mask current ** perr # UChar |-> error |--
  sem_pend_restore_call_post environment critical sg original mask checkpoint perr error.
Proof.
  intros * Hhistory Hsame.
  unfold sem_pend_restore_call_post, kernel_stack_call_history_restore_post.
  Exists returned current; entailer!.
Qed.
