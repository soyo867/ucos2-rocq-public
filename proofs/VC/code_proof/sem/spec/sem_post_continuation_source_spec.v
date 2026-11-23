Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_saved_wait_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_post_wait_history_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The real EventTaskRdy effect changes waiting fields and ready/event
    bitmaps, but leaves each generation, saved SP and parked entry intact.
    Reindex the existing map without changing any descriptor-local owner.
    [active] is explicit: this step does not require a task-only caller. *)
Lemma sem_post_wake_preserves_continuations : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg entry eid event tid old local active,
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  task_stack_live_coverage entry.(TskState) active ->
  let after := event_wake_state sg entry eid event tid old PendSem 0 PendOK in
  store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
    entry.(TskState).(parkedTaskStacks) |--
  coq_prop (task_stack_live_coverage after.(TskState) active) &&
  store_parked_continuations (kernel_saved_continuation_entry abi after.(TskState) local)
    after.(TskState).(parkedTaskStacks).
Proof.
  intros external platform port abi sg entry eid event tid old local active Hold Hcoverage after.
  assert (Hnodes : forall slot node, after.(TskState).(inUsedTaskStates) slot = Some node ->
    exists previous, entry.(TskState).(inUsedTaskStates) slot = Some previous /\
      previous.(taskGeneration) = node.(taskGeneration) /\ previous.(tcbStkPtr) = node.(tcbStkPtr)).
  { intros slot node Hnode.
    change ((if Z.eqb slot tid then Some (task_event_wake_single old PendSem 0 PendOK)
      else entry.(TskState).(inUsedTaskStates) slot) = Some node) in Hnode.
    destruct (Z.eqb slot tid) eqn:Hslot.
    - apply Z.eqb_eq in Hslot; subst slot; injection Hnode as Hnode; subst node.
      exists old; repeat split; assumption || reflexivity.
    - exists node; repeat split; assumption || reflexivity. }
  assert (Hcovered : task_stack_live_coverage after.(TskState) active).
  { eapply task_stack_live_coverage_used_map_frame with (before := entry.(TskState));
      [|reflexivity|exact Hcoverage].
    intros slot node Hnode; destruct (Hnodes slot node Hnode) as [previous [Hprevious [Hgen Hsp]]].
    exists previous; auto. }
  assert (Htransport :
    store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
      entry.(TskState).(parkedTaskStacks) |--
    store_parked_continuations (kernel_saved_continuation_entry abi after.(TskState) local)
      after.(TskState).(parkedTaskStacks)).
  { change (store_parked_continuations
      (kernel_saved_continuation_entry abi entry.(TskState) local) entry.(TskState).(parkedTaskStacks) |--
      store_parked_continuations
      (kernel_saved_continuation_entry abi after.(TskState) local) entry.(TskState).(parkedTaskStacks)).
    apply kernel_saved_continuation_map_reindex.
    intros key payload node Hpayload Hnode Hgen; apply Hnodes; exact Hnode. }
  sep_apply_l_atomic Htransport; entailer!.
Qed.

(** Join the actual OS_EventTaskRdy post with its caller's existing map.
    Only the checked wake transformer reindexes that map; [local] itself
    has no stability premise and is neither discarded nor reconstructed. *)
Lemma sem_post_wake_merge_continuations : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg entry eid event tid old priority local active,
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid event ->
  event.(eventType) = OS_EVENT_TYPE_SEM ->
  event_task_rdy_entry sg entry.(TskState) eid event tid old ->
  task_stack_live_coverage entry.(TskState) active ->
  let after := event_wake_state sg entry eid event tid old PendSem 0 PendOK in
  event_task_rdy_post sg entry.(TskState) eid event tid old 0 1 0
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
  sem_post_wake_frame sg entry eid tid **
  store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
    entry.(TskState).(parkedTaskStacks) |--
  coq_prop (sem_post_wake_result sg eid entry after priority /\
    task_stack_live_coverage after.(TskState) active) &&
  (kernel_program_inv sg after **
   store_parked_continuations (kernel_saved_continuation_entry abi after.(TskState) local)
     after.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi sg entry eid event tid old priority local active
    Hvalid Hlookup Htype Hentry Hcoverage after.
  pose proof Hentry as [_ [_ [_ [_ [_ [Hhead Hold]]]]]].
  assert (Hkind : event_type_to_pend_type event.(eventType) = Some PendSem)
    by (rewrite Htype; reflexivity).
  destruct event.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
  inversion Hhead; subst head.
  destruct (event_wake_head sg entry eid event tid tail PendSem 0 PendOK
    Hvalid Hlookup Hkind Hlist) as [found [Hfound [Hstep Hrest]]].
  assert (found = old) by congruence; subst found.
  sep_apply_l_atomic (sem_post_wake_merge_full sg entry eid event tid old priority
    Hvalid Hlookup Htype Hentry); Intros current.
  assert (Hresult : sem_post_wake_result sg eid entry current priority) by tauto.
  unfold sem_post_wake_result in Hresult; rewrite Hstep in Hresult.
  injection Hresult as Hpriority Hcurrent; subst current.
  pose proof (sem_post_wake_preserves_continuations external platform port abi sg entry eid event
    tid old local active Hold Hcoverage) as Hstacks.
  cbn zeta in Hstacks; sep_apply_l_atomic Hstacks.
  unfold after; rewrite kernel_program_inv_split_unmap; unfold sem_post_wake_result; entailer!.
Qed.

(** A complete physical wake cut used by a suspended SemPend call.
    The C selection/stores/bitmap updates come from [execution]; the same
    resulting state supplies the registered Post effect, wait history and
    retained continuation map. No incoming or future returned state is
    supplied by the caller, and the waiting task need not be the woken one.

    This is OSSemPost's nonempty-waiter body, before its Restore/Scheduler.
    Its existing type/nonempty/layout guards are not a whole-API Require. *)
Lemma sem_pend_post_continuation_source : forall environment critical sg original call mask initial observed
  waiting_eid timeout waiting entry actor eid event priority local active before after (frame : Assertion),
  sem_pend_wait_at (Some environment) critical sg original mask initial observed waiting_eid timeout
    waiting call entry ->
  critical.(critical_region_clients) (sem_pend_post_source_client actor eid) ->
  actor <> original.(os_sched_call_invocation) ->
  sem_post_lookup entry eid event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry event <> 0 -> event_object_layout_prop sg eid ->
  task_stack_live_coverage entry.(TskState) active ->
  (kernel_program_inv sg entry **
   store_parked_continuations
     (kernel_saved_continuation_entry environment.(task_stack_call_continuations) entry.(TskState) local)
     entry.(TskState).(parkedTaskStacks) ** frame) before ->
  sem_post_waiter_execution sg (event_addr sg eid) priority before after ->
  exists tid old,
    let current := event_wake_state sg entry eid event tid old PendSem 0 PendOK in
    event_task_rdy_entry sg entry.(TskState) eid event tid old /\
    sem_post_wake_result sg eid entry current priority /\
    kernel_client_step (sem_pend_post_source_client actor eid) sg entry current /\
    sem_pend_wait_at (Some environment) critical sg original mask initial observed waiting_eid timeout
      waiting call current /\
    task_stack_live_coverage current.(TskState) active /\
    (kernel_program_inv sg current **
     store_parked_continuations
       (kernel_saved_continuation_entry environment.(task_stack_call_continuations) current.(TskState) local)
       current.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros environment critical sg original call mask initial observed waiting_eid timeout waiting entry
    actor eid event priority local active before after frame Hwait Hin Hforeign Hlookup Htype Hgroup Hlayout
    Hcoverage Hpre Hexecution.
  set (abi := environment.(task_stack_call_continuations)).
  set (stacks := store_parked_continuations
    (kernel_saved_continuation_entry abi entry.(TskState) local) entry.(TskState).(parkedTaskStacks)).
  assert (Hvalid : UCOS2_state_inv sg entry).
  { assert (Hview : kernel_program_inv sg entry ** stacks ** frame |--
      coq_prop (UCOS2_state_inv sg entry) && TT).
    { unfold kernel_program_inv; entailer!. }
    exact (proj1 (Hview before Hpre)). }
  assert (Hsplit : kernel_program_inv sg entry ** stacks ** frame |--
    EX tid, EX old, coq_prop (event_task_rdy_entry sg entry.(TskState) eid event tid old) &&
    (event_task_rdy_pre sg entry.(TskState) eid event tid old 1 0
       (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
       (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) **
     (sem_post_wake_frame sg entry eid tid ** stacks ** frame))).
  { rewrite kernel_program_inv_split_unmap.
    sep_apply_l_atomic (sem_post_wake_split_full sg entry eid event Hvalid Hlookup Htype Hgroup Hlayout).
    Intros tid old; Exists tid old; entailer!. }
  destruct (Hsplit before Hpre) as [tid [old [Hentry Howned]]].
  pose proof (sem_post_waiter_source_post sg entry.(TskState) eid event tid old
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority before after
    (sem_post_wake_frame sg entry eid tid ** stacks ** frame) Howned Hexecution) as Hpost.
  set (current := event_wake_state sg entry eid event tid old PendSem 0 PendOK).
  assert (Hmerge : event_task_rdy_post sg entry.(TskState) eid event tid old 0 1 0
      (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
      (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
      (sem_post_wake_frame sg entry eid tid ** stacks ** frame) |--
    coq_prop (sem_post_wake_result sg eid entry current priority /\
      task_stack_live_coverage current.(TskState) active) &&
    (kernel_program_inv sg current **
     store_parked_continuations (kernel_saved_continuation_entry abi current.(TskState) local)
       current.(TskState).(parkedTaskStacks) ** frame)).
  { pose proof (sem_post_wake_merge_continuations _ _ _ abi sg entry eid event tid old
      priority local active Hvalid Hlookup Htype Hentry Hcoverage) as Hjoin.
    cbn zeta in Hjoin.
    unfold stacks, current; sepcon_assoc_change.
    sep_apply_l_atomic Hjoin; entailer!. }
  destruct (Hmerge after Hpost) as [[Hwake Hcovered] Hresources].
  pose proof (sem_post_wake_result_critical sg eid entry event current priority Hlookup Hgroup Hwake)
    as Hcritical.
  pose proof (sem_pend_registered_post_wait_source environment critical sg original call mask initial
    observed waiting_eid timeout waiting entry actor eid event tid old priority Hwait Hin Hforeign
    Hlookup Hgroup Hwake) as Hcontinued.
  exists tid, old; cbn zeta; fold current.
  split; [exact Hentry|]. split; [exact Hwake|].
  split; [exists (OS_ERR_NONE, true); exact Hcritical|].
  split; [exact Hcontinued|]. split; [exact Hcovered|exact Hresources].
Qed.
