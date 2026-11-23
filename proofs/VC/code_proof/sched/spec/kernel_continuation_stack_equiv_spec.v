Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.

(** Shared by the Sem and Del emp compatibility interfaces. Both
    directions keep the same saved descriptor, binding and live-SP facts. *)
Lemma kernel_saved_continuation_map_emp_equiv : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks stacks,
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks (fun _ => emp)) stacks --||--
  armv7a_task_stack_continuations abi tasks stacks.
Proof.
  intros external platform port abi tasks stacks.
  unfold armv7a_task_stack_continuations, store_parked_continuations.
  split; apply TaskFieldStorage.store_map_mono; intros key payload Hlookup;
    unfold kernel_saved_continuation_entry, armv7a_task_stack_entry;
    Intros descriptor; Exists descriptor; entailer!.
Qed.

(** Empty local is exactly the existing SP-indexed continuation owner.
    This is an equivalence, not an erasure rule for arbitrary locals. In
    particular nonempty maps and retired generations keep their entries,
    descriptors, live-SP constraints and dormant execution authority.
    The adapter leaves both existing representation modules unchanged. *)
Lemma kernel_continuation_call_closed_emp_equiv : forall external platform port
  (abi : Armv7aContinuationABI external platform port) resources sg active call mask state,
  kernel_continuation_call_closed abi resources (fun _ => emp) sg active call mask state --||--
  kernel_stack_call_closed abi resources sg active call mask state.
Proof.
  intros external platform port abi resources sg active call mask state.
  pose proof (kernel_saved_continuation_map_emp_equiv external platform port abi
    state.(TskState) state.(TskState).(parkedTaskStacks)) as Hmap.
  unfold kernel_continuation_call_closed, kernel_continuation_inv,
    kernel_stack_call_closed, kernel_stack_inv.
  split; Intros;
    [sep_apply_l_atomic (proj1 Hmap)|sep_apply_l_atomic (proj2 Hmap)]; entailer!.
Qed.
