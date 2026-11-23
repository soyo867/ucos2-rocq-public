Require Export Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_return_hook_spec.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.lib.sched.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem SeparationLogic.

Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OS_TaskReturn composes the selected Return hook with the adopted SELF
    deletion contract.  Function-specific assertions and proved resource
    localisation belong here; the callee semantics remain read-only. *)

(** The C wrapper discards the returned error byte.  Its postcondition
    retains that actual result existentially, the deletion cut and the
    distinct eventual return world already specified by OSTaskDel. *)
Definition task_return_post environment critical saved_local sg name call mask initial : Assertion :=
  EX result,
    task_delete_post environment critical saved_local sg 255 name call mask initial result.

(** Reading OSTCBCur neither dereferences a TCB nor changes its lifetime.
    The reconstruction wand retains the complete original entry, including
    its environment protocol and continuation resources. *)
Lemma task_return_entry_split_current :
  forall environment critical saved_local completed sg call mask initial,
  task_delete_entry environment critical saved_local completed sg 255 call mask initial |--
  task_delete_ptr_cell sg.(g_OSTCBCur) (task_delete_current sg initial) **
  wand (task_delete_ptr_cell sg.(g_OSTCBCur) (task_delete_current sg initial))
    (task_delete_entry environment critical saved_local completed sg 255 call mask initial).
Proof.
  intros; unfold task_delete_entry, task_delete_call_closed,
    kernel_continuation_call_closed, kernel_continuation_inv,
    task_delete_phase_resources, task_delete_phase_valid.
  rewrite (UCOS2_raw_rep_split_module sg initial SchedModule).
  cbn [UCOS2_module_rep].
  unfold sched_raw_rep, sched_physical_rep, task_delete_ptr_cell, task_delete_current.
  Intros; entailer!.
  apply_sepcon_adjoint; entailer!.
Qed.

Lemma task_return_entry_merge_current :
  forall environment critical saved_local completed sg call mask initial,
  task_delete_ptr_cell sg.(g_OSTCBCur) (task_delete_current sg initial) **
  wand (task_delete_ptr_cell sg.(g_OSTCBCur) (task_delete_current sg initial))
    (task_delete_entry environment critical saved_local completed sg 255 call mask initial) |--
  task_delete_entry environment critical saved_local completed sg 255 call mask initial.
Proof. intros; apply derivable1_wand_elim2. Qed.

Lemma task_return_post_from_delete :
  forall environment critical saved_local sg name call mask initial result,
  task_delete_post environment critical saved_local sg 255 name call mask initial result |--
  task_return_post environment critical saved_local sg name call mask initial.
Proof. intros; unfold task_return_post; Exists result; entailer!. Qed.
