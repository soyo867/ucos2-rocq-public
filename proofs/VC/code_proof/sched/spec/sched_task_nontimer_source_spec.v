Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.core.spec.kernel_client_resumption.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Import TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.

(** The existing family names thirteen specific source operations.  This
    consequence follows from those actual client steps; it is not a claim
    about arbitrary registered clients, stack publication completeness, or
    a whole API's interrupt intervals. *)
Lemma kernel_nontimer_source_client_running_eq : forall action sg before after,
  kernel_nontimer_source_client action ->
  kernel_client_step action sg before after ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros action sg before after Hsource; destruct Hsource.
  - apply task_creation_client_running_eq.
  - intros [_ ->]; reflexivity.
  - intros [_ ->]; reflexivity.
  - intros [_ ->]; reflexivity.
  - intros [_ ->]; reflexivity.
  - intros [_ [result Hstep]].
    unfold event_create_allocate_critical in Hstep.
    destruct before.(EventState).(unUsedEventStates).
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [image [_ [_ ->]]]; reflexivity.
  - intros [_ ->]; reflexivity.
  - intros [_ [_ ->]]; reflexivity.
  - intros [_ [_ [_ [_ [result [a [Ha Hstep]]]]]]].
    destruct free; destruct Hstep as [_ ->]; reflexivity.
  - intros [_ [_ [_ [_ ->]]]]; reflexivity.
  - intros [_ [result Hstep]].
    eapply task_suspend_critical_running_eq; exact Hstep.
  - intros [_ [result Hstep]].
    eapply task_resume_critical_running_eq; exact Hstep.
  - intros [event [_ [_ [node [fields [_ [_ [_ ->]]]]]]]].
    destruct (Z.ltb 0 fields.(semCount)); reflexivity.
Qed.

(** Publication can change an old TCB's links, but its allocated slot is
    private and cannot replace the current live TCB.  Retirement here only
    updates the invocation ledger; actual TaskDel stages are separate. *)
Lemma task_creation_client_preserves_current_consistency : forall action sg before after,
  UCOS2_state_inv sg before ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  kernel_client_step (task_creation_client action) sg before after ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros action sg before after Hvalid Hconsistent [Hguard [_ ->]].
  destruct action as [priority entry slot rest image | priority entry allocation image
                    | priority invocation node | invocation].
  - exact Hconsistent.
  - exact Hconsistent.
  - cbn [task_lifecycle_action_guard] in Hguard.
    pose proof (task_commit_identity_private before.(TskState) priority invocation node
      (proj1 Hguard)) as Hprivate.
    destruct (task_private_excludes_public sg before.(TskState) node.(taskID)
      (proj1 (proj1 (proj2 Hvalid))) Hprivate) as [Hunused _].
    eapply sched_current_consistency_fields_frame;
      [reflexivity|reflexivity| |exact Hconsistent].
    intros current old Hcurrent Hlookup.
    eapply task_commit_transports_old_priority; eassumption.
  - exact Hconsistent.
Qed.

Lemma task_create_stack_publication_preserves_current_consistency :
  forall publication sg before after,
  UCOS2_state_inv sg before ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  kernel_client_step (task_create_stack_publication_client publication) sg before after ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros publication sg before after Hvalid Hconsistent Hstep.
  destruct (task_create_stack_publication_raw_projection sg publication before after Hstep)
    as [Hraw ->].
  change (sched_current_consistency
    (task_create_stack_publication_raw_state sg publication before).(TskState)
    (task_create_stack_publication_raw_state sg publication before).(SchedState)).
  eapply task_creation_client_preserves_current_consistency; eassumption.
Qed.

(** This is the same actual action and state edge as the family membership.
    It does not classify an arbitrary environment action or assert that an
    unfinished deletion phase has the whole closed kernel invariant. *)
Lemma kernel_nontimer_source_client_preserves_current_consistency :
  forall action sg before after,
  UCOS2_state_inv sg before ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  kernel_nontimer_source_client action ->
  kernel_client_step action sg before after ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros action sg before after Hvalid Hconsistent Hsource Hstep; destruct Hsource.
  - eapply task_creation_client_preserves_current_consistency; eassumption.
  - eapply task_create_stack_publication_preserves_current_consistency; eassumption.
  - destruct Hstep as [_ ->]; exact Hconsistent.
  - destruct Hstep as [_ ->]; exact Hconsistent.
  - destruct Hstep as [_ ->]; exact Hconsistent.
  - destruct Hstep as [_ [result Hstep]].
    unfold event_create_allocate_critical in Hstep.
    destruct before.(EventState).(unUsedEventStates).
    + destruct Hstep as [_ ->]; exact Hconsistent.
    + destruct Hstep as [image [_ [_ ->]]]; exact Hconsistent.
  - destruct Hstep as [_ ->]; exact Hconsistent.
  - destruct Hstep as [_ [_ ->]]; exact Hconsistent.
  - destruct Hstep as [_ [_ [_ [_ [result [a [Ha Hstep]]]]]]].
    destruct free; destruct Hstep as [_ ->]; exact Hconsistent.
  - destruct Hstep as [_ [_ [_ [_ ->]]]]; exact Hconsistent.
  - eapply task_suspend_client_preserves_current_consistency; eassumption.
  - eapply task_resume_client_preserves_current_consistency; eassumption.
  - destruct Hstep as [event [_ [_ [node [fields [_ [_ [_ ->]]]]]]]].
    destruct (Z.ltb 0 fields.(semCount)); exact Hconsistent.
Qed.
