Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The execution owner and active map key already observe [origin].
    Its duplicate slot/generation fields in the pure lease can be chosen
    to agree with that origin without changing a byte, execution view or
    public input. This also applies to an ISR or priority-error input;
    no interrupt, priority, readiness or scheduler-lock guard is added.

    The remaining current-pointer equivalence is explicit. Normalising
    metadata does not establish that the observed origin is OSTCBCur.
    Boot needs no task-lease normalisation and keeps its original input. *)
Lemma task_create_continuation_pre_normalize_lease :
  forall environment critical saved_local sg region args task_return
    lower old_frame upper name original mask initial slot generation,
  original.(os_sched_call_origin) = RunningInvocation slot generation ->
  task_create_continuation_pre environment critical saved_local sg region args task_return
    lower old_frame upper name original mask initial |--
  EX normalized,
    coq_prop (os_sched_execution_view normalized = os_sched_execution_view original /\
      task_stack_call_active_key normalized = task_stack_call_active_key original /\
      normalized.(os_sched_call_stack).(stackLeaseSlot) = slot /\
      normalized.(os_sched_call_stack).(stackLeaseGeneration) = generation /\
      (kernel_call_task_source normalized initial <->
       task_execution_current original.(os_sched_call_origin) initial)) &&
    task_create_continuation_pre environment critical saved_local sg region args task_return
      lower old_frame upper name normalized mask initial.
Proof.
  intros environment critical saved_local sg region args task_return
    lower old_frame upper name original mask initial slot generation Horigin.
  unfold task_create_continuation_pre; Intros.
  assert (Hactive : task_invocation_active initial.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { unfold task_create_stack_entry in *; tauto. }
  set (normalized :=
    {| os_sched_call_invocation := original.(os_sched_call_invocation);
       os_sched_call_origin := original.(os_sched_call_origin);
       os_sched_call_stack :=
         {| stackLeaseRegion := original.(os_sched_call_stack).(stackLeaseRegion);
            stackLeaseSlot := slot;
            stackLeaseGeneration := generation |};
       os_sched_call_fragments := original.(os_sched_call_fragments) |}).
  assert (Hsource : kernel_call_task_source normalized initial <->
    task_execution_current original.(os_sched_call_origin) initial).
  { unfold kernel_call_task_source, normalized;
      cbn [os_sched_call_origin os_sched_call_stack os_sched_call_invocation
        stackLeaseSlot stackLeaseGeneration].
    rewrite Horigin; rewrite Horigin in Hactive; tauto. }
  assert (Hview : os_sched_execution_view normalized = os_sched_execution_view original)
    by reflexivity.
  assert (Hkey : task_stack_call_active_key normalized = task_stack_call_active_key original)
    by reflexivity.
  assert (Hentry : task_create_stack_entry sg args name normalized initial =
    task_create_stack_entry sg args name original initial) by reflexivity.
  assert (Hinput : task_create_continuation_input environment critical saved_local sg
    normalized mask initial = task_create_continuation_input environment critical saved_local sg
    original mask initial) by reflexivity.
  Exists normalized; rewrite Hentry, Hinput; entailer!.
Qed.

(** The public result can be returned with the original pure lease. The
    returned fragments, kernel state, child-buffer alternative and every
    resource stay unchanged. Full [same_call] is reconstructed for that
    original lease, so this rule does not weaken the public postcondition.
    It never rewrites a parked descriptor or a source transition. *)
Lemma task_create_continuation_post_execution_view :
  forall environment critical saved_local sg region args task_return
    lower old_frame upper first second mask result,
  os_sched_execution_view first = os_sched_execution_view second ->
  task_create_continuation_post environment critical saved_local sg region args task_return
    lower old_frame upper first mask result |--
  task_create_continuation_post environment critical saved_local sg region args task_return
    lower old_frame upper second mask result.
Proof.
  intros environment critical saved_local sg region args task_return
    lower old_frame upper first second mask result Hview.
  pose proof (f_equal os_execution_invocation Hview) as Hi.
  pose proof (f_equal os_execution_origin Hview) as Ho.
  pose proof (f_equal os_execution_stack Hview) as Hr.
  change (first.(os_sched_call_invocation) = second.(os_sched_call_invocation)) in Hi.
  change (first.(os_sched_call_origin) = second.(os_sched_call_origin)) in Ho.
  change (first.(os_sched_call_stack).(stackLeaseRegion) =
    second.(os_sched_call_stack).(stackLeaseRegion)) in Hr.
  unfold task_create_continuation_post; Intros returned current.
  assert (Hsame : task_tcb_init_stack_same_call returned first) by tauto.
  destruct Hsame as [Hinvocation [Horigin Hstack]].
  set (relabeled :=
    {| os_sched_call_invocation := returned.(os_sched_call_invocation);
       os_sched_call_origin := returned.(os_sched_call_origin);
       os_sched_call_stack := second.(os_sched_call_stack);
       os_sched_call_fragments := returned.(os_sched_call_fragments) |}).
  assert (Hsame : task_tcb_init_stack_same_call relabeled second).
  { unfold task_tcb_init_stack_same_call, relabeled;
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack];
      repeat split; congruence. }
  assert (Hregion : second.(os_sched_call_stack).(stackLeaseRegion) =
    returned.(os_sched_call_stack).(stackLeaseRegion)) by (rewrite Hstack; symmetry; exact Hr).
  assert (Hinput : task_create_continuation_input environment critical saved_local sg
    relabeled mask current = task_create_continuation_input environment critical saved_local sg
    returned mask current).
  { unfold task_create_continuation_input, kernel_call_execution_owned,
      os_sched_context_resources, os_sched_execution_view, task_stack_call_active_key,
      relabeled; cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack
        os_sched_call_fragments]; rewrite Hregion; reflexivity. }
  Exists relabeled current; rewrite Hinput; entailer!.
Qed.
