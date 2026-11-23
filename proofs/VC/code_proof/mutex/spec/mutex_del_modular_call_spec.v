Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_stage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_region_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** These are the four conversions used by the actual Del Save/Restore
    declarations. The common platform boundary supplies same-call and
    normal-return availability. The completed C environment interval must
    preserve the admitted Del call stage. This condition is a module R/G
    obligation, not an ARM guarantee or a consequence of registration.
    Owner history is derived below from the existing source-client proof.
    The heap after a switch is always indexed by its actual returned state;
    the private ECB pool is never an invariant external frame. *)

Lemma mutex_del_modular_save_pre : forall environment external platform critical
  saved_local sg call mask before,
  mutex_del_continuation_source_save_pre environment external platform critical
    saved_local sg call mask before |--
  coq_prop (mutex_del_callsite_environment environment external platform /\
    mutex_del_call_stage call before /\ kernel_call_stack_available call before /\
    UCOS2_state_inv sg before) &&
  kernel_continuation_call_closed environment.(mutex_del_call_continuations)
    mutex_del_stack_resources (task_create_continuation_local saved_local) sg
    (task_stack_call_active_key call) call mask before.
Proof.
  intros; unfold mutex_del_continuation_source_save_pre,
    mutex_del_continuation_source_entry; Intros_p Hfacts.
  unfold mutex_del_continuation_entry; Intros selected.
  destruct H as [Henv ->].
  unfold kernel_continuation_call_closed, kernel_continuation_inv,
    mutex_del_stack_resources, kernel_program_inv; entailer!.
Qed.

Lemma mutex_del_modular_save_post : forall environment configuration saved_local rely
  sg original mask saved before,
  UCOS2_state_inv sg before ->
  mutex_del_call_stage original before -> kernel_call_stack_available original before ->
  (forall after, rely sg before after -> mutex_del_call_stage original before ->
    mutex_del_call_stage original after) ->
  kernel_call_modular_save_post environment.(mutex_del_call_continuations)
    mutex_del_stack_resources (task_create_continuation_local saved_local)
    (mutex_program_region configuration) rely sg original mask saved before |--
  mutex_del_continuation_source_save_post environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) (mutex_program_region configuration)
    saved_local sg original mask saved before.
Proof.
  intros environment configuration saved_local rely sg original mask saved before
    Hvalid Hstage Havailable Hstage_rely.
  unfold kernel_call_modular_save_post; Intros returned acquired.
  assert (Hsave : kernel_call_save_source environment.(mutex_del_call_external)
    environment.(mutex_del_call_port) (mutex_program_region configuration) sg
    original returned mask saved before acquired) by tauto.
  assert (Hnormal : kernel_call_normal_return original before returned acquired) by tauto.
  assert (Hrely : rely sg before acquired) by tauto.
  assert (Hhistory : mutex_owner_source_history sg before acquired).
  { eapply mutex_owner_region_interval_history.
    - apply mutex_program_region_protocol.
    - constructor.
    - exact Hvalid.
    - eapply kernel_call_save_source_region_interval; exact Hsave. }
  assert (Hstage' : mutex_del_call_stage original acquired) by
    (apply Hstage_rely; assumption).
  destruct Hnormal as [Hsame Hreturned_available].
  assert (Havailable' : kernel_call_stack_available original acquired).
  { specialize (Hreturned_available Havailable).
    destruct Hsame as [_ [Ho _]].
    unfold kernel_call_stack_available in *; rewrite Ho in Hreturned_available;
      exact Hreturned_available. }
  assert (Hactive : task_stack_call_active_key returned = task_stack_call_active_key original).
  { unfold task_stack_call_active_key; destruct Hsame as [_ [Ho _]]; rewrite Ho; reflexivity. }
  assert (Hsaved : interrupt_saved_value mask saved) by (destruct Hsave as [_ [_ [_ [_ Hsaved]]]]; exact Hsaved).
  rewrite Hactive.
  sep_apply_l_atomic (mutex_del_continuation_source_save_post_from_masked environment
    (mutex_program_region configuration) saved_local sg original returned mask saved before acquired
    Hstage' Havailable' Hhistory Hsame Hsaved).
  entailer!.
Qed.

Lemma mutex_del_modular_restore_pre : forall environment external platform critical
  saved_local sg original mask saved acquired checkpoint,
  mutex_del_continuation_source_restore_pre environment external platform critical
    saved_local sg original mask saved acquired checkpoint |--
  EX call,
    coq_prop (mutex_del_callsite_environment environment external platform /\
      kernel_stack_call_same_call call original /\ interrupt_saved_value mask saved /\
      mutex_del_call_stage call checkpoint /\ kernel_call_stack_available call checkpoint) &&
    kernel_continuation_call_masked environment.(mutex_del_call_continuations)
      mutex_del_stack_resources (task_create_continuation_local saved_local) critical sg
      (task_stack_call_active_key call) call saved acquired checkpoint.
Proof.
  intros; unfold mutex_del_continuation_source_restore_pre; Intros_p Hfacts.
  destruct Hfacts as [Hstage Havailable].
  unfold mutex_del_continuation_restore_pre; Intros selected call.
  destruct H as [Henv [Hsame [Hsaved ->]]].
  assert (Hstage' : mutex_del_call_stage call checkpoint).
  { eapply mutex_del_same_call_stage; eassumption. }
  assert (Havailable' : kernel_call_stack_available call checkpoint).
  { destruct Hsame as [_ [Ho _]]; unfold kernel_call_stack_available; rewrite Ho; exact Havailable. }
  assert (Hactive : task_stack_call_active_key call = task_stack_call_active_key original).
  { unfold task_stack_call_active_key; destruct Hsame as [_ [Ho _]]; rewrite Ho; reflexivity. }
  Exists call; rewrite Hactive; entailer!.
Qed.

Lemma mutex_del_modular_restore_post : forall environment critical saved_local rely
  sg original call mask released,
  kernel_stack_call_same_call call original ->
  mutex_del_call_stage call released -> kernel_call_stack_available call released ->
  (forall after, rely sg released after -> mutex_del_call_stage call released ->
    mutex_del_call_stage call after) ->
  kernel_call_modular_restore_post environment.(mutex_del_call_continuations)
    mutex_del_stack_resources (task_create_continuation_local saved_local) critical rely
    sg call mask released |--
  mutex_del_continuation_source_return environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) saved_local sg original mask.
Proof.
  intros environment critical saved_local rely sg original call mask released
    Hcall Hstage Havailable Hstage_rely.
  unfold kernel_call_modular_restore_post; Intros returned current.
  assert (Hnormal : kernel_call_normal_return call released returned current) by tauto.
  assert (Hrely : rely sg released current) by tauto.
  destruct Hnormal as [Hsame Hreturned_available].
  assert (Hsame_original : kernel_stack_call_same_call returned original).
  { destruct Hsame as [Hi [Ho Hs]], Hcall as [Hi' [Ho' Hs']].
    unfold kernel_stack_call_same_call; repeat split; congruence. }
  assert (Hstage' : mutex_del_call_stage returned current).
  { eapply mutex_del_same_call_stage; [exact Hsame|].
    apply Hstage_rely; assumption. }
  assert (Havailable' : kernel_call_stack_available returned current)
    by (apply Hreturned_available; exact Havailable).
  assert (Hactive : task_stack_call_active_key returned = task_stack_call_active_key original).
  { unfold task_stack_call_active_key; destruct Hsame_original as [_ [Ho _]]; rewrite Ho; reflexivity. }
  unfold mutex_del_continuation_source_return, mutex_del_continuation_source_return_at,
    mutex_del_continuation_return_at.
  Exists returned current environment; rewrite Hactive.
  unfold mutex_del_callsite_environment; entailer!.
Qed.
