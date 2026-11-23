Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope sac_scope.

(** A C-level consumer of the actual Scheduler return relation.  The
    registered C actions establish the wait-field projection; the actual
    returning selection supplies the current pointer and ready membership.
    Neither an architectural running token nor [os_sched_c_return] alone
    establishes readiness.  No eventual return is asserted here.

    This is the pure resume-entry component needed by
    [sem_pend_phase_sched_output].  The caller still transports its existing
    wait history and obtains the current resource world from the Scheduler
    contract; this lemma neither creates that world nor a physical history. *)
Lemma sem_pend_sched_c_return_resume_entry :
  forall external critical sg entry call returned final tid old eid generation,
  (forall action, critical.(critical_region_clients) action ->
    sem_pend_projected_source_client action) ->
  sem_pend_projected_source_client external.(os_sched_hook_action) ->
  os_sched_c_return external critical sg entry call returned final ->
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  UCOS2_state_inv sg final ->
  final.(SchedState).(curTaskID) = Some tid ->
  In tid final.(SchedState).(readyList) ->
  exists current,
    sem_pend_resume_entry sg final eid tid current /\
    current.(taskGeneration) = generation.
Proof.
  intros external critical sg entry call returned final tid old eid generation
    Hclients Hhook Hreturn Hold Hwait Hvalid Hcurrent Hready.
  destruct (sem_pend_sched_return_projection external critical sg entry call returned final
    tid old Hclients Hhook Hreturn Hold) as [node [Hnode Heffects]].
  pose proof (sem_pend_wait_trace_preserves_continuation eid generation old node
    Heffects Hwait) as Hcontinued.
  pose proof (proj1 (proj1 (proj2 (proj2 Hvalid)))) as Hready_inv.
  destruct (proj1 Hready_inv tid Hready) as [selected [Hselected [_ Heffective]]].
  assert (selected = node) by congruence; subst selected.
  destruct (sem_pend_wait_ready_resume_registration eid generation node Hcontinued Heffective)
    as [Hregistration Hgeneration].
  exists node; split; [|exact Hgeneration].
  unfold sem_pend_resume_entry.
  split; [exact Hvalid|]. split; [exact Hcurrent|]. split; [exact Hnode|].
  split; assumption.
Qed.

(** The same consumer after the already-defined registered intervals on
    either side of Scheduler's C return.  The two intervals are actual
    finite past relations, not a promise about every future acquisition.
    Use the first lemma at Scheduler's C-body return and this one when its
    approved platform boundary has returned the complete registered chain.
    Final current/ready observations must belong to that SAME endpoint. *)
Lemma sem_pend_schedule_return_resume_entry :
  forall external critical sg call returned waiting final tid old eid generation,
  (forall action, critical.(critical_region_clients) action ->
    sem_pend_projected_source_client action) ->
  sem_pend_projected_source_client external.(os_sched_hook_action) ->
  sem_pend_schedule_return external critical sg call returned waiting final ->
  waiting.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  UCOS2_state_inv sg final ->
  final.(SchedState).(curTaskID) = Some tid ->
  In tid final.(SchedState).(readyList) ->
  exists current,
    sem_pend_resume_entry sg final eid tid current /\
    current.(taskGeneration) = generation.
Proof.
  intros external critical sg call returned waiting final tid old eid generation
    Hclients Hhook Hreturn Hold Hwait Hvalid Hcurrent Hready.
  destruct (sem_pend_schedule_return_preserves_continuation external critical sg call returned
    waiting final tid old eid generation Hclients Hhook Hreturn Hold Hwait)
    as [node [Hnode Hcontinued]].
  pose proof (proj1 (proj1 (proj2 (proj2 Hvalid)))) as Hready_inv.
  destruct (proj1 Hready_inv tid Hready) as [selected [Hselected [_ Heffective]]].
  assert (selected = node) by congruence; subst selected.
  destruct (sem_pend_wait_ready_resume_registration eid generation node Hcontinued Heffective)
    as [Hregistration Hgeneration].
  exists node; split; [|exact Hgeneration].
  unfold sem_pend_resume_entry.
  split; [exact Hvalid|]. split; [exact Hcurrent|]. split; [exact Hnode|].
  split; assumption.
Qed.

(** Consume the real C return for the same input wait.  Its state relation
    extends the existing history; its identity theorem fixes the returned
    invocation.  The selected waiter and the history share [final].
    This supplies the pure conjunct of the canonical phase Ensure. *)
Lemma sem_pend_wait_at_sched_c_return_selected :
  forall environment critical sg original mask initial observed eid timeout waiting
    call entry returned final,
  (forall action, critical.(critical_region_clients) action ->
    sem_pend_projected_source_client action) ->
  sem_pend_projected_source_client
    environment.(task_stack_call_external).(os_sched_hook_action) ->
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout
    waiting call entry ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry call returned final ->
  UCOS2_state_inv sg final ->
  final.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  In original.(os_sched_call_stack).(stackLeaseSlot) final.(SchedState).(readyList) ->
  sem_pend_wait_selected_at (Some environment) critical sg original mask initial observed eid timeout
    waiting returned final.
Proof.
  intros environment critical sg original mask initial observed eid timeout waiting
    call entry returned final Hclients Hhook Hwait Hreturn Hvalid Hcurrent Hready.
  destruct Hwait as [owned [Howned [Hsame [Hobserved Hpath]]]].
  inversion Howned; subst owned.
  destruct (sem_pend_observed_wait_history_waiter _ _ _ _ _ _ _ _ _ _ Hobserved)
    as [first [Hfirst Hfirst_wait]].
  destruct (sem_pend_wait_source_history_preserves_waiter environment critical sg original eid
    original.(os_sched_call_stack).(stackLeaseGeneration) waiting entry Hpath
    first Hfirst Hfirst_wait) as [old [Hold Hcontinued]].
  destruct (sem_pend_sched_c_return_resume_entry environment.(task_stack_call_external)
    critical sg entry call returned final original.(os_sched_call_stack).(stackLeaseSlot)
    old eid original.(os_sched_call_stack).(stackLeaseGeneration)
    Hclients Hhook Hreturn Hold Hcontinued Hvalid Hcurrent Hready)
    as [node [Hresume Hgeneration]].
  pose proof (os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hreturn) as Hreturned.
  assert (Hjoined : kernel_stack_call_same_call returned original).
  { unfold kernel_stack_call_same_call in *; intuition congruence. }
  split.
  - exists environment; split; [reflexivity|]. split; [exact Hjoined|].
    split; [exact Hobserved|].
    eapply SemPendWaitSourceTrans; [exact Hpath|].
    eapply SemPendWaitSourceCScheduler; eassumption.
  - exists node; exact Hresume.
Qed.

(** Full C-level phase consequence, including the registered intervals on
    both sides of this actual Scheduler return.  No independently chosen
    history endpoint or future-return premise is introduced.  The spatial
    Scheduler result must expose these SAME [returned]/[final] indices
    before combining this fact with [sem_pend_stack_save_input]. *)
Lemma sem_pend_wait_at_schedule_return_selected :
  forall environment critical sg original mask initial observed eid timeout waiting
    call before returned final,
  (forall action, critical.(critical_region_clients) action ->
    sem_pend_projected_source_client action) ->
  sem_pend_projected_source_client
    environment.(task_stack_call_external).(os_sched_hook_action) ->
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout
    waiting call before ->
  sem_pend_schedule_return environment.(task_stack_call_external) critical sg call returned before final ->
  UCOS2_state_inv sg final ->
  final.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  In original.(os_sched_call_stack).(stackLeaseSlot) final.(SchedState).(readyList) ->
  sem_pend_wait_selected_at (Some environment) critical sg original mask initial observed eid timeout
    waiting returned final.
Proof.
  intros environment critical sg original mask initial observed eid timeout waiting
    call before returned final Hclients Hhook Hwait Hreturn Hvalid Hcurrent Hready.
  destruct Hwait as [owned [Howned [Hsame [Hobserved Hpath]]]].
  inversion Howned; subst owned.
  destruct (sem_pend_observed_wait_history_waiter _ _ _ _ _ _ _ _ _ _ Hobserved)
    as [first [Hfirst Hfirst_wait]].
  destruct (sem_pend_wait_source_history_preserves_waiter environment critical sg original eid
    original.(os_sched_call_stack).(stackLeaseGeneration) waiting before Hpath
    first Hfirst Hfirst_wait) as [old [Hold Hcontinued]].
  destruct (sem_pend_schedule_return_resume_entry environment.(task_stack_call_external)
    critical sg call returned before final original.(os_sched_call_stack).(stackLeaseSlot)
    old eid original.(os_sched_call_stack).(stackLeaseGeneration)
    Hclients Hhook Hreturn Hold Hcontinued Hvalid Hcurrent Hready)
    as [node [Hresume Hgeneration]].
  destruct Hreturn as [entry [scheduled [Hfirst_interval [Hbody Hlast_interval]]]].
  pose proof (os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hbody) as Hreturned.
  assert (Hjoined : kernel_stack_call_same_call returned original).
  { unfold kernel_stack_call_same_call in *; intuition congruence. }
  pose proof (proj1 Hsame) as Hinvocation.
  rewrite Hinvocation in Hfirst_interval, Hlast_interval.
  split.
  - exists environment; split; [reflexivity|]. split; [exact Hjoined|].
    split; [exact Hobserved|].
    eapply SemPendWaitSourceTrans; [exact Hpath|].
    eapply SemPendWaitSourceTrans.
    + eapply SemPendWaitSourceCInterval; [exact Hclients|exact Hfirst_interval].
    + eapply SemPendWaitSourceTrans.
      * eapply SemPendWaitSourceCScheduler; [exact Hclients|exact Hhook|exact Hbody].
      * eapply SemPendWaitSourceCInterval; [exact Hclients|exact Hlast_interval].
  - exists node; exact Hresume.
Qed.

(** Consume a source-bearing Scheduler result on one heap. The history,
    current/ready observations and resources refer to the same returned
    state. The weaker [os_sched_stack_return_post] alone does not supply
    those observations. No future-return or opaque-save law is assumed. *)
Lemma sem_pend_schedule_return_phase_output :
  forall environment critical sg original mask initial observed eid timeout waiting
    call before (frame : Assertion),
  (forall action, critical.(critical_region_clients) action ->
    sem_pend_projected_source_client action) ->
  sem_pend_projected_source_client
    environment.(task_stack_call_external).(os_sched_hook_action) ->
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout
    waiting call before ->
  kernel_stack_call_history_restore_post environment.(task_stack_call_continuations)
    kernel_program_inv sg (task_stack_call_active_key call)
    (fun entered entry returned current =>
      sem_pend_schedule_return environment.(task_stack_call_external) critical sg
        entered returned entry current /\
      current.(SchedState).(curTaskID) = Some entered.(os_sched_call_stack).(stackLeaseSlot) /\
      In entered.(os_sched_call_stack).(stackLeaseSlot) current.(SchedState).(readyList))
    call mask before ** frame |--
  sem_pend_phase_sched_output
    (SemPendWaitPhase original mask initial observed eid timeout waiting)
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical sg call mask before ** frame.
Proof.
  intros environment critical sg original mask initial observed eid timeout waiting
    call before frame Hclients Hhook Hwait.
  unfold kernel_stack_call_history_restore_post; Intros returned current.
  assert (Hreturn : sem_pend_schedule_return environment.(task_stack_call_external)
    critical sg call returned before current) by tauto.
  assert (Hcurrent : current.(SchedState).(curTaskID) =
    Some call.(os_sched_call_stack).(stackLeaseSlot)) by tauto.
  assert (Hready : In call.(os_sched_call_stack).(stackLeaseSlot)
    current.(SchedState).(readyList)) by tauto.
  assert (Hsame : kernel_stack_call_same_call returned call) by tauto.
  assert (Hactive : task_stack_call_active_key call = task_stack_call_active_key returned).
  { unfold task_stack_call_active_key.
    destruct Hsame as [Hi [Ho Hstack]]; rewrite Ho; reflexivity. }
  rewrite Hactive, <- (task_tcb_init_stack_save_input_closed_world environment critical sg
    returned mask current).
  unfold task_tcb_init_stack_save_input; Intros.
  assert (Hvalid : UCOS2_state_inv sg current) by tauto.
  pose proof Hwait as [owned [Howned [Horiginal Hhistory]]].
  pose proof (proj2 (proj2 Horiginal)) as Hstack.
  rewrite Hstack in Hcurrent, Hready.
  pose proof (sem_pend_wait_at_schedule_return_selected environment critical sg original mask
    initial observed eid timeout waiting call before returned current Hclients Hhook Hwait
    Hreturn Hvalid Hcurrent Hready) as Hselected.
  cbn [sem_pend_phase_sched_output]; Exists returned current.
  rewrite sem_pend_stack_save_input_owned.
  unfold task_tcb_init_stack_save_input; entailer!.
Qed.

Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.

(** The same actual returning C history now carries the caller's full
    continuation family. The existential is only a resource-bearing
    endpoint view, not a new history relation or an eventual-return law. *)
Lemma sem_pend_continuation_schedule_return_phase_output :
  forall environment critical saved_local sg original mask initial observed eid timeout waiting
    call before (frame : Assertion),
  (forall action, critical.(critical_region_clients) action ->
    sem_pend_projected_source_client action) ->
  sem_pend_projected_source_client
    environment.(task_stack_call_external).(os_sched_hook_action) ->
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout
    waiting call before ->
  (EX returned current,
    coq_prop (sem_pend_schedule_return environment.(task_stack_call_external) critical sg
        call returned before current /\
      current.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) /\
      In call.(os_sched_call_stack).(stackLeaseSlot) current.(SchedState).(readyList) /\
      kernel_stack_call_same_call returned call) &&
    kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_inv
      (task_create_continuation_local saved_local) sg
      (task_stack_call_active_key call) returned mask current) ** frame |--
  sem_pend_continuation_phase_sched_output
    (SemPendWaitPhase original mask initial observed eid timeout waiting)
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg call mask before ** frame.
Proof.
  intros environment critical saved_local sg original mask initial observed eid timeout waiting
    call before frame Hclients Hhook Hwait.
  Intros returned current.
  assert (Hreturn : sem_pend_schedule_return environment.(task_stack_call_external)
    critical sg call returned before current) by tauto.
  assert (Hcurrent : current.(SchedState).(curTaskID) =
    Some call.(os_sched_call_stack).(stackLeaseSlot)) by tauto.
  assert (Hready : In call.(os_sched_call_stack).(stackLeaseSlot)
    current.(SchedState).(readyList)) by tauto.
  assert (Hsame : kernel_stack_call_same_call returned call) by tauto.
  assert (Hactive : task_stack_call_active_key call = task_stack_call_active_key returned).
  { unfold task_stack_call_active_key.
    destruct Hsame as [Hi [Ho Hstack]]; rewrite Ho; reflexivity. }
  rewrite Hactive, <- (task_tcb_init_continuation_save_input_closed_world environment critical saved_local sg
    returned mask current).
  unfold task_tcb_init_continuation_save_input, task_create_continuation_input; Intros.
  assert (Hvalid : UCOS2_state_inv sg current) by tauto.
  pose proof Hwait as [owned [Howned [Horiginal Hhistory]]].
  pose proof (proj2 (proj2 Horiginal)) as Hstack.
  rewrite Hstack in Hcurrent, Hready.
  pose proof (sem_pend_wait_at_schedule_return_selected environment critical sg original mask
    initial observed eid timeout waiting call before returned current Hclients Hhook Hwait
    Hreturn Hvalid Hcurrent Hready) as Hselected.
  cbn [sem_pend_continuation_phase_sched_output]; Exists returned current.
  rewrite sem_pend_continuation_save_input_owned.
  unfold task_tcb_init_continuation_save_input, task_create_continuation_input; entailer!.
Qed.
