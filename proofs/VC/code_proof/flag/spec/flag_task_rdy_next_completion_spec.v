Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_fields_resources_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_resources_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.flag_execution.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.flag_node_fields.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagTaskRdyNextCompletion.

Definition flag_task_rdy_next_input (environment : TaskStackCallEnvironment)
  sg entry (reference call : OsSchedCallContext) pointer waiter old bits (result : PendStatus) local pnode frame : Assertion :=
  flag_task_rdy_fields_pre sg entry pointer waiter old bits **
    (UCOS2_raw_rep_missing_task_storage_sched_flag sg entry **
     store_parked_continuations
       (kernel_saved_continuation_entry environment.(task_stack_call_continuations) entry.(TskState) local)
       entry.(TskState).(parkedTaskStacks) ** (pnode # Ptr |-> pointer ** frame)).

Definition flag_task_rdy_next_output (environment : TaskStackCallEnvironment)
  sg post reference call pointer waiter (bits : Z) (result : PendStatus)
  (c_result : Z) (schedule : bool) local pnode observed frame : Assertion :=
  coq_prop (c_result = (if schedule then 1 else 0) /\
    observed = waiter.(flagWaitImage).(flagNodeNext) /\
    post.(FlagState).(flagWaitNodes) pointer = None) &&
  (pnode # Ptr |-> observed ** UCOS2_fields_inv sg post **
   store_parked_continuations
     (kernel_saved_continuation_entry environment.(task_stack_call_continuations) post.(TskState)
       (flag_continuation_local_node reference.(os_sched_call_stack)
         (flag_active_waiting sg reference pointer call post) local))
     post.(TskState).(parkedTaskStacks) ** frame).

(** The intermediate heap is the actual helper return; the final heap is
    the actual Next assignment.  The state equation names that call's
    deterministic post.  No output resource, cache, or receipt guarantee
    is a constructor premise. *)
Inductive flag_task_rdy_next_c_segment (environment : TaskStackCallEnvironment) (sg : StableGlobVars) :
  UCOS2_Verify_State -> model -> Assertion -> bool ->
  UCOS2_Verify_State -> model -> Assertion -> Prop :=
| FlagTaskRdyNextCompletionCSegment :
    forall entry reference call pointer waiter old bits result c_result local fragments pnode frame
      before middle after observed schedule post,
    UCOS2_state_inv sg entry ->
    flag_task_rdy_domain sg entry pointer waiter old bits ->
    flag_active_waiting_registration reference pointer call entry ->
    waiter.(flagNodeAddr) = pointer ->
    entry.(TskState).(parkedTaskStacks) (task_stack_key reference.(os_sched_call_stack)) =
      Some (reference.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
    flag_pend_sched_fields_task_rdy_call sg pointer bits result c_result before middle ->
    flag_source_next_assignment pnode pointer observed middle after ->
    flag_task_rdy_next_input environment sg entry reference call pointer waiter old bits result
      local pnode frame before ->
    flag_task_rdy sg entry pointer bits result =
      Some (schedule, post) ->
    flag_task_rdy_next_c_segment environment sg entry before
      (flag_task_rdy_next_input environment sg entry reference call pointer waiter old bits result
        local pnode frame) false post after
      (flag_task_rdy_next_output environment sg post reference call pointer waiter bits result
        c_result schedule local pnode observed frame).

Lemma flag_task_rdy_next_c_segment_from_call :
  forall (environment : TaskStackCallEnvironment) sg entry reference call pointer waiter old bits result
    c_result local fragments pnode frame before middle after observed,
  UCOS2_state_inv sg entry ->
  flag_task_rdy_domain sg entry pointer waiter old bits ->
  flag_active_waiting_registration reference pointer call entry ->
  waiter.(flagNodeAddr) = pointer ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key reference.(os_sched_call_stack)) =
    Some (reference.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  flag_pend_sched_fields_task_rdy_call sg pointer bits result c_result before middle ->
  flag_source_next_assignment pnode pointer observed middle after ->
  flag_task_rdy_next_input environment sg entry reference call pointer waiter old bits result
    local pnode frame before ->
  exists post schedule,
    flag_task_rdy_next_c_segment environment sg entry before
      (flag_task_rdy_next_input environment sg entry reference call pointer waiter old bits result
        local pnode frame) false post after
      (flag_task_rdy_next_output environment sg post reference call pointer waiter bits result
        c_result schedule local pnode observed frame).
Proof.
  intros environment sg entry reference call pointer waiter old bits result c_result local fragments
    pnode frame before middle after observed Hvalid Hdomain Hregistration Haddr Hparked Hcall Hnext Hpre.
  destruct (flag_active_task_rdy_next_publish _ _ _ environment.(task_stack_call_continuations)
    sg entry reference call pointer waiter old bits result c_result local fragments pnode frame
    before middle after observed Hvalid Hdomain Hregistration Haddr Hparked Hcall Hnext Hpre)
    as [post [schedule [Hstep Houtput]]].
  exists post, schedule; eapply FlagTaskRdyNextCompletionCSegment; eassumption.
Qed.

Lemma flag_task_rdy_next_c_segment_resources :
  forall environment sg entry before input stopped post after output,
  flag_task_rdy_next_c_segment environment sg entry before input stopped post after output ->
  input before /\ output after.
Proof.
  intros environment sg entry before input stopped post after output Hsegment.
  destruct Hsegment as [entry reference call pointer waiter old bits result c_result local fragments pnode frame
    before middle after observed schedule post Hvalid Hdomain Hregistration Haddr Hparked Hcall Hnext Hpre Hstep].
  split; [exact Hpre|].
  destruct (flag_active_task_rdy_next_publish _ _ _ environment.(task_stack_call_continuations)
    sg entry reference call pointer waiter old bits result c_result local fragments pnode frame
    before middle after observed Hvalid Hdomain Hregistration Haddr Hparked Hcall Hnext Hpre)
    as [actual [actual_schedule [Hactual [Hresult [Hobserved [Hnone Houtput]]]]]].
  rewrite Hstep in Hactual; injection Hactual as Hschedule Hpost; subst actual_schedule actual.
  exact (conj (conj Hresult (conj Hobserved Hnone)) Houtput).
Qed.

Lemma flag_task_rdy_next_c_segment_source :
  forall environment sg entry before input stopped post after output,
  flag_task_rdy_next_c_segment environment sg entry before input stopped post after output ->
  stopped = false /\ WakeComponent.kernel_wake_c_source sg entry post.
Proof.
  intros environment sg entry before input stopped post after output Hsegment.
  destruct Hsegment; split; [reflexivity|].
  eapply WakeComponent.KernelWakeCFlagSource; eassumption.
Qed.

Lemma flag_task_rdy_next_c_segment_lifetime :
  forall environment sg entry before input stopped post after output observer origin,
  flag_task_rdy_next_c_segment environment sg entry before input stopped post after output ->
  task_observer_lifetime_result observer origin entry.(TskState) post.(TskState) stopped.
Proof.
  intros environment sg entry before input stopped post after output observer origin Hsegment.
  destruct (flag_task_rdy_next_c_segment_source _ _ _ _ _ _ _ _ _ Hsegment) as [-> Hsource].
  eapply WakeComponent.kernel_wake_c_source_lifetime_result; exact Hsource.
Qed.

Lemma flag_task_rdy_next_c_segment_observer :
  forall environment sg entry before input stopped post after output observer origin,
  flag_task_rdy_next_c_segment environment sg entry before input stopped post after output ->
  task_invocation_active entry.(TskState) observer origin /\ sched_observer_current_cache origin entry ->
  task_invocation_active post.(TskState) observer origin /\ sched_observer_current_cache origin post.
Proof.
  intros environment sg entry before input stopped post after output observer origin Hsegment [Hactive Hcache].
  pose proof (proj2 (flag_task_rdy_next_c_segment_source _ _ _ _ _ _ _ _ _ Hsegment)) as Hsource.
  split.
  - eapply WakeComponent.kernel_wake_c_source_preserves_observer_active; eassumption.
  - eapply WakeComponent.kernel_wake_c_source_preserves_observer_cache; eassumption.
Qed.

Lemma flag_task_rdy_next_c_segment_source_frames :
  forall environment sg entry before input stopped post after output task_observer event_observer,
  flag_task_rdy_next_c_segment environment sg entry before input stopped post after output ->
  task_creation_frame task_observer entry.(TskState) post.(TskState) /\
  event_creation_frame event_observer entry.(EventState) post.(EventState) /\
  entry.(NameState) = post.(NameState) /\ timer_execution.timer_public_trace sg entry.(TimerState) post.(TimerState).
Proof.
  intros environment sg entry before input stopped post after output task_observer event_observer Hsegment.
  apply NamedSourceFrames.kernel_wake_c_source_creation_frames.
  exact (proj2 (flag_task_rdy_next_c_segment_source _ _ _ _ _ _ _ _ _ Hsegment)).
Qed.

Lemma flag_task_rdy_next_c_segment_control_fields :
  forall environment sg entry before input stopped post after output,
  flag_task_rdy_next_c_segment environment sg entry before input stopped post after output ->
  entry.(SchedState).(isRunning) = post.(SchedState).(isRunning) /\
  entry.(IntrState) = post.(IntrState).
Proof.
  intros environment sg entry before input stopped post after output Hsegment.
  destruct Hsegment as [entry reference call pointer waiter old bits result c_result local fragments pnode frame
    before middle after observed schedule post Hvalid Hdomain Hregistration Haddr Hparked Hcall Hnext Hpre Hstep].
  destruct (flag_task_rdy_result _ _ _ _ _ _ _ Hstep)
    as [actual_waiter [flags [actual_old [Hunlink [Hold [-> Hschedule]]]]]].
  split; reflexivity.
Qed.

End FlagTaskRdyNextCompletion.

