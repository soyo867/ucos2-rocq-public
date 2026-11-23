Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.sched.spec.sched_del_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_api_continuation_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The shared Scheduler C contract supplies its actual three-part
    history and its returned closed resource at the same tuple. *)
Lemma mutex_api_scheduler_post_from_callee :
  forall environment external platform critical saved_local sg original mask before,
  mutex_del_callsite_environment environment external platform ->
  sched_del_history_return_post (mutex_del_runtime_sched_environment environment)
    critical saved_local sg original mask before |--
  mutex_api_scheduler_post environment external platform critical saved_local
    sg original mask before.
Proof.
  intros * [He Hp]; subst external platform.
  unfold sched_del_history_return_post; Intros returned current.
  destruct H as [Hhistory [Hsame Hsource]].
  assert (Hactive : task_stack_call_active_key returned = task_stack_call_active_key original).
  { unfold task_stack_call_active_key; rewrite (proj1 (proj2 Hsame)); reflexivity. }
  unfold mutex_api_scheduler_post, mutex_del_continuation_return_at.
  Exists returned current environment; rewrite Hactive.
  unfold mutex_api_scheduler_history, mutex_del_callsite_environment;
    cbn [mutex_del_runtime_sched_environment task_stack_call_continuations]; entailer!.
Qed.

Lemma mutex_api_scheduler_callee_after_restore :
  forall environment external platform critical saved_local sg original mask checkpoint
    restored unmasked,
  mutex_del_callsite_environment environment external platform ->
  mutex_api_restore_history environment critical sg original checkpoint restored unmasked ->
  sched_del_history_return_post (mutex_del_runtime_sched_environment environment)
    critical saved_local sg restored mask unmasked |--
  mutex_api_tail_post environment external platform critical saved_local
    sg original mask checkpoint 1.
Proof.
  intros * Henv Hrestore.
  sep_apply_l_atomic (mutex_api_scheduler_post_from_callee environment external platform
    critical saved_local sg restored mask unmasked Henv).
  apply mutex_api_scheduler_post_after_restore; exact Hrestore.
Qed.
