Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_saved_wait_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_continuation_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_checkpoint_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** EventTaskRdy retains the current pointer and priority cache. Its TCB
    writes retain priority and generation, so the cache still denotes the
    same live current task. The actual suspension test supplies a ready
    witness only on its ready-insertion branch. This conclusion does not
    claim an arbitrary foreign client preserves the cache, or that a
    suspended waiter becomes ready. *)
Lemma sem_pend_event_wake_sched_entry : forall sg state eid event tid old call,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  kernel_call_task_source call state ->
  sched_current_consistency state.(TskState) state.(SchedState) ->
  let current := event_wake_state sg state eid event tid old PendSem 0 PendOK in
  kernel_call_task_source call current /\
  sched_current_consistency current.(TskState) current.(SchedState) /\
  os_sched_selection_enabled current = os_sched_selection_enabled state /\
  (task_status_is_suspended
     (encode_task_status (task_event_wake_single old PendSem 0 PendOK).(stat)) = false ->
   current.(SchedState).(readyList) <> []).
Proof.
  intros sg state eid event tid old call Hold Hsource Hcache current.
  assert (Hcurrent : current.(SchedState).(curTaskID) = state.(SchedState).(curTaskID)).
  { unfold current, event_wake_state; cbn [replace_SchedS SchedState].
    unfold sched_wake_by_status; destruct task_status_is_suspended; reflexivity. }
  assert (Hpriority : current.(SchedState).(curSchedPrio) = state.(SchedState).(curSchedPrio)).
  { unfold current, event_wake_state; cbn [replace_SchedS SchedState].
    unfold sched_wake_by_status; destruct task_status_is_suspended; reflexivity. }
  split.
  - destruct Hsource as [Horigin [Hactive Hexecuting]].
    split; [exact Horigin|]. split.
    + change (task_invocation_active
        (glob_task_set_usedtask state.(TskState) tid (task_event_wake_single old PendSem 0 PendOK))
        call.(os_sched_call_invocation) call.(os_sched_call_origin)).
      eapply glob_task_set_usedtask_preserves_invocation_active;
        [exact Hold|reflexivity|exact Hactive].
    + unfold task_execution_current in *; rewrite Horigin in *.
      rewrite Hcurrent; exact Hexecuting.
  - split.
    + unfold sched_current_consistency in Hcache |- *; rewrite Hcurrent, Hpriority.
      destruct state.(SchedState).(curTaskID) as [slot|]; [|exact Hcache].
      destruct Hcache as [node [Hnode Hprio]].
      change (exists found,
        (if Z.eqb slot tid then Some (task_event_wake_single old PendSem 0 PendOK)
         else state.(TskState).(inUsedTaskStates) slot) = Some found /\
        state.(SchedState).(curSchedPrio) = Some found.(curPrio)).
      destruct (Z.eqb slot tid) eqn:Hslot.
      * apply Z.eqb_eq in Hslot; subst slot.
        assert (node = old) by congruence; subst node.
        exists (task_event_wake_single old PendSem 0 PendOK); split; [reflexivity|exact Hprio].
      * exists node; split; assumption.
    + split; [reflexivity|].
      intros Hready Hempty.
      assert (Hin : In tid current.(SchedState).(readyList)).
      { change (In tid (sched_wake_by_status sg state.(TskState) state.(SchedState) tid
          (encode_task_status (task_event_wake_single old PendSem 0 PendOK).(stat))).(readyList)).
        apply sched_wake_by_status_membership; right; split; [reflexivity|exact Hready]. }
      rewrite Hempty in Hin; contradiction.
Qed.

(** Start at the established EventTaskWait checkpoint and consume the
    actual SemPost/EventTaskRdy C stores. The same resulting heap carries
    the registered wait history, current-source/cache facts and all of the
    original descriptor-local owners. No ready/Idle premise is added to
    SemPend's public input. A successful non-suspended wake supplies the
    nonempty selector domain directly, even if the ready set was empty
    before this particular C effect.

    This is the current-task-preserving handler/C-effect family. A foreign
    task switch needs its actual installation/return source; this theorem
    does not use the waiting caller's execution resource as a handler's
    resource and does not assert that a handler has returned. *)
Lemma sem_pend_post_checkpoint_sched_source : forall environment critical sg original call mask
  initial observed waiting_eid timeout waiting actor eid event priority local active
  before after (frame : Assertion),
  sem_pend_observed_wait_history (Some environment) critical sg original mask initial observed
    waiting_eid timeout waiting ->
  kernel_stack_call_same_call call original ->
  critical.(critical_region_clients) (sem_pend_post_source_client actor eid) ->
  actor <> original.(os_sched_call_invocation) ->
  sem_post_lookup waiting eid event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group waiting event <> 0 -> event_object_layout_prop sg eid ->
  task_stack_live_coverage waiting.(TskState) active ->
  (kernel_program_inv sg waiting **
   store_parked_continuations
     (kernel_saved_continuation_entry environment.(task_stack_call_continuations)
       waiting.(TskState) local) waiting.(TskState).(parkedTaskStacks) ** frame) before ->
  sem_post_waiter_execution sg (event_addr sg eid) priority before after ->
  exists tid old,
    let current := event_wake_state sg waiting eid event tid old PendSem 0 PendOK in
    event_task_rdy_entry sg waiting.(TskState) eid event tid old /\
    sem_post_wake_result sg eid waiting current priority /\
    kernel_client_step (sem_pend_post_source_client actor eid) sg waiting current /\
    sem_pend_wait_at (Some environment) critical sg original mask initial observed waiting_eid timeout
      waiting call current /\
    kernel_call_task_source call current /\
    sched_current_consistency current.(TskState) current.(SchedState) /\
    os_sched_selection_enabled current = os_sched_selection_enabled waiting /\
    (task_status_is_suspended
       (encode_task_status (task_event_wake_single old PendSem 0 PendOK).(stat)) = false ->
     current.(SchedState).(readyList) <> []) /\
    task_stack_live_coverage current.(TskState) active /\
    (kernel_program_inv sg current **
     store_parked_continuations
       (kernel_saved_continuation_entry environment.(task_stack_call_continuations)
         current.(TskState) local) current.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros environment critical sg original call mask initial observed waiting_eid timeout waiting
    actor eid event priority local active before after frame Hcheckpoint Hsame Hin Hforeign
    Hlookup Htype Hgroup Hlayout Hcoverage Hpre Hrun.
  pose proof Hcheckpoint as [_ [Horiginal [Hcache _]]].
  assert (Hcall : kernel_call_task_source call waiting).
  { destruct Hsame as [Hi [Ho Hstack]].
    unfold kernel_call_task_source in *; rewrite Hi, Ho, Hstack; exact Horiginal. }
  assert (Hwait : sem_pend_wait_at (Some environment) critical sg original mask initial observed
    waiting_eid timeout waiting call waiting).
  { apply sem_pend_wait_at_waiting;
      [exists environment; reflexivity|exact Hsame|exact Hcheckpoint]. }
  destruct (sem_pend_post_continuation_source environment critical sg original call mask initial
    observed waiting_eid timeout waiting waiting actor eid event priority local active before after frame
    Hwait Hin Hforeign Hlookup Htype Hgroup Hlayout Hcoverage Hpre Hrun)
    as [tid [old [Hentry [Hwake [Hstep [Hhistory [Hcovered Hresources]]]]]]].
  pose proof Hentry as [_ [_ [_ [_ [_ [Hhead Hold]]]]]].
  destruct (sem_pend_event_wake_sched_entry sg waiting eid event tid old call Hold Hcall Hcache)
    as [Hsource [Hcurrent_cache [Hguards Hnonempty]]].
  exists tid, old; cbn zeta.
  split; [exact Hentry|]. split; [exact Hwake|]. split; [exact Hstep|].
  split; [exact Hhistory|]. split; [exact Hsource|]. split; [exact Hcurrent_cache|].
  split; [exact Hguards|]. split; [exact Hnonempty|]. split; assumption.
Qed.

(** Consume these source facts at the CURRENT canonical Scheduler input.
    The state is the concrete wake transformer of the recorded checkpoint,
    and the ready branch is the actual EventTaskRdy suspension test. The
    existing input still supplies the returned CPU/stack owners on this
    heap; no return, ABI strengthening or map reconstruction follows from
    the pure source facts. The result discharges the cache/nonempty inputs
    of [sem_pend_continuation_enabled_nonswitch_sched_call]; the enabled and
    equal-priority tests remain the actual Scheduler branch observations. *)
Lemma sem_pend_continuation_wake_sched_entry_facts : forall environment critical saved_local
  sg original call mask initial observed waiting_eid timeout waiting eid event tid old
  heap (frame : Assertion),
  waiting.(TskState).(inUsedTaskStates) tid = Some old ->
  task_status_is_suspended
    (encode_task_status (task_event_wake_single old PendSem 0 PendOK).(stat)) = false ->
  let current := event_wake_state sg waiting eid event tid old PendSem 0 PendOK in
  (sem_pend_continuation_phase_sched_input
    (SemPendWaitPhase original mask initial observed waiting_eid timeout waiting)
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg call mask current ** frame) heap ->
  (coq_prop (kernel_call_task_source call current /\
     sched_current_consistency current.(TskState) current.(SchedState) /\
     current.(SchedState).(readyList) <> []) &&
   (sem_pend_continuation_phase_sched_input
     (SemPendWaitPhase original mask initial observed waiting_eid timeout waiting)
     environment.(task_stack_call_external) environment.(task_stack_call_platform)
     (Some environment) critical saved_local sg call mask current ** frame)) heap.
Proof.
  intros environment critical saved_local sg original call mask initial observed waiting_eid timeout
    waiting eid event tid old heap frame Hold Hready current Hpre.
  match type of Hpre with ?P heap => assert (Hobserve : P |--
    coq_prop (sem_pend_wait_at (Some environment) critical sg original mask initial observed
      waiting_eid timeout waiting call current) && TT) end.
  { cbn [sem_pend_continuation_phase_sched_input]; entailer!; intros ? ?; exact I. }
  destruct (proj1 (Hobserve heap Hpre)) as [owned [Howned [Hsame [Hcheckpoint Hhistory]]]].
  pose proof Hcheckpoint as [_ [Horiginal [Hcache _]]].
  assert (Hcall : kernel_call_task_source call waiting).
  { destruct Hsame as [Hi [Ho Hstack]].
    unfold kernel_call_task_source in *; rewrite Hi, Ho, Hstack; exact Horiginal. }
  destruct (sem_pend_event_wake_sched_entry sg waiting eid event tid old call Hold Hcall Hcache)
    as [Hsource [Hcurrent_cache [Hguards Hnonempty]]].
  split; [split; [exact Hsource|split; [exact Hcurrent_cache|exact (Hnonempty Hready)]]|exact Hpre].
Qed.
