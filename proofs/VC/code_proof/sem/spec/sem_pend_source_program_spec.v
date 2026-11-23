Require Import Coq.ZArith.ZArith Coq.Lists.List.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_checkpoint_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Import TaskStateDef ListNotations.
Local Open Scope Z_scope.

(** The fields instance uses the same ordered operation and exact mutable
    checkpoints.  Only its waiting-source history admits the newly retained
    actual caller receipts.  No early-return domain or C update is changed. *)
Definition sem_pend_source_wait_at environment critical sg original mask before observed eid timeout
  waiting call current : Prop :=
  exists owned,
    environment = Some owned /\ kernel_stack_call_same_call call original /\
    sem_pend_observed_wait_history environment critical sg original mask before observed eid timeout waiting /\
    sem_pend_source_history owned critical sg original eid
      original.(os_sched_call_stack).(stackLeaseGeneration) waiting current.

Definition sem_pend_source_wait_selected_at environment critical sg original mask before observed eid timeout
  waiting call current : Prop :=
  sem_pend_source_wait_at environment critical sg original mask before observed eid timeout waiting call current /\
  exists node, sem_pend_resume_entry sg current eid original.(os_sched_call_stack).(stackLeaseSlot) node.

Lemma sem_pend_source_wait_at_waiting : forall environment critical sg original mask before observed
  eid timeout waiting call,
  sem_pend_has_stack environment -> kernel_stack_call_same_call call original ->
  sem_pend_observed_wait_history environment critical sg original mask before observed eid timeout waiting ->
  sem_pend_source_wait_at environment critical sg original mask before observed eid timeout waiting call waiting.
Proof.
  intros * [owned Howned] Hsame Hinitial.
  exists owned; split; [exact Howned|]. split; [exact Hsame|]. split; [exact Hinitial|].
  apply sem_pend_source_history_refl.
Qed.

Lemma sem_pend_source_wait_at_modular_return : forall environment critical sg original mask initial
  observed eid timeout waiting call before returned after,
  UCOS2_state_inv sg before ->
  sem_pend_source_wait_at (Some environment) critical sg original mask initial observed eid timeout
    waiting call before ->
  sem_pend_source_modular_call_history environment critical sg call before returned after ->
  sem_pend_source_wait_at (Some environment) critical sg original mask initial observed eid timeout
    waiting returned after.
Proof.
  intros * Hvalid [owned [Howned [Hsame [Hinitial Hpath]]]] [trace [Hcalls [Hreturned Havailable]]].
  injection Howned as Howned; subst owned.
  exists environment; split; [reflexivity|]. split.
  - unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence.
  - split; [exact Hinitial|]. eapply SemPendSourceHistoryTrans; [exact Hpath|].
    pose proof Hsame as [Hi [Ho Hs]].
    revert trace Hcalls; rewrite Hi, Ho; intros trace Hcalls.
    eapply SemPendSourceHistoryClients; [exact Hcalls|exact Hvalid].
Qed.

Lemma sem_pend_source_selected_from_ready_current : forall environment critical sg original mask initial
  observed eid timeout waiting call current,
  sem_pend_source_wait_at (Some environment) critical sg original mask initial observed eid timeout
    waiting call current ->
  UCOS2_state_inv sg current ->
  current.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  In original.(os_sched_call_stack).(stackLeaseSlot) current.(SchedState).(readyList) ->
  sem_pend_source_wait_selected_at (Some environment) critical sg original mask initial observed eid timeout
    waiting call current.
Proof.
  intros * Hwait Hvalid Hcurrent Hmember; split; [exact Hwait|].
  destruct Hwait as [owned [Howned [Hsame [Hinitial Hpath]]]].
  destruct (sem_pend_observed_wait_history_waiter _ _ _ _ _ _ _ _ _ _ Hinitial)
    as [first [Hfirst Hcontinuation]].
  destruct (sem_pend_source_history_preserves_waiter _ _ _ _ _ _ _ _ Hpath
    first Hfirst Hcontinuation) as [last [Hlast Hlast_wait]].
  pose proof Hvalid as [_ [_ [[Hready _] _]]].
  destruct (proj1 Hready _ Hmember) as [node [Hnode [Hpriority Heffective]]].
  assert (node = last) by congruence; subst node.
  destruct (sem_pend_wait_ready_resume_registration _ _ _ Hlast_wait Heffective)
    as [Hregistration Hgeneration].
  exists last; unfold sem_pend_resume_entry; auto.
Qed.

Lemma sem_pend_source_wait_selected_modular_return : forall environment critical sg original initial_mask
  initial observed eid timeout waiting call before returned acquired,
  sem_pend_source_wait_selected_at (Some environment) critical sg original initial_mask initial observed
    eid timeout waiting call before ->
  sem_pend_source_modular_call_history environment critical sg call before returned acquired ->
  sem_pend_save_rely sg before acquired ->
  sem_pend_source_wait_selected_at (Some environment) critical sg original initial_mask initial observed
    eid timeout waiting returned acquired.
Proof.
  intros * [Hwait [old [Hvalid [Hcurrent [Hold [Hregistration Hready]]]]]]
    Hsource [_ [_ [_ Hready_rely]]].
  pose proof (sem_pend_source_wait_at_modular_return environment critical sg original initial_mask
    initial observed eid timeout waiting call before returned acquired Hvalid Hwait Hsource) as Hwait'.
  pose proof Hwait as [owned [Howned [Hsame [Hinitial Hpath]]]].
  pose proof Hinitial as [_ [[Horigin _] _]].
  pose proof (sem_pend_source_modular_call_history_forgets _ _ _ _ _ _ _ Hsource)
    as [Htrace [Hreturned Havailable]].
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)
    as [Hresources Hcontrol].
  destruct (critical_region_interval_transports_resources critical sg
    call.(os_sched_call_invocation) before acquired Hresources Hvalid) as [Hvalid' _].
  assert (Hcaller_origin : call.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration)).
  { rewrite (proj1 (proj2 Hsame)); exact Horigin. }
  assert (Hcurrent' : acquired.(SchedState).(curTaskID) =
    Some original.(os_sched_call_stack).(stackLeaseSlot)).
  { assert (Hbefore : task_execution_current call.(os_sched_call_origin) before).
    { rewrite Hcaller_origin; exact Hcurrent. }
    pose proof (task_execution_source_trace_preserves_current _ _ _ _ _ _ _ Hcontrol Hbefore) as Hafter.
    rewrite (proj1 (proj2 Hreturned)), Hcaller_origin in Hafter; exact Hafter. }
  eapply sem_pend_source_selected_from_ready_current;
    [exact Hwait'|exact Hvalid'|exact Hcurrent'|apply Hready_rely; assumption].
Qed.

Lemma sem_pend_source_wait_at_c_scheduler : forall environment critical sg original mask initial
  observed eid timeout waiting entered entry returned released,
  sem_pend_source_wait_at (Some environment) critical sg original mask initial observed eid timeout
    waiting entered entry ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry entered returned released ->
  (forall previous,
    entry.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some previous ->
    sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) previous ->
    sem_pend_task_projection entry.(TskState) released.(TskState)
      original.(os_sched_call_stack).(stackLeaseSlot) previous) ->
  sem_pend_source_wait_at (Some environment) critical sg original mask initial observed eid timeout
    waiting returned released.
Proof.
  intros * [owned [Howned [Hsame [Hinitial Hpath]]]] Hbody Hprojection.
  injection Howned as Howned; subst owned.
  pose proof (os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hbody) as Hreturned.
  exists environment; split; [reflexivity|]. split.
  - unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence.
  - split; [exact Hinitial|]. eapply SemPendSourceHistoryTrans; [exact Hpath|].
    eapply SemPendSourceHistoryScheduler; eassumption.
Qed.

Definition sem_pend_source_resume_origin environment critical sg context mask before observed
  eid timeout resumed tid old : Prop :=
  sem_pend_resume_entry sg resumed eid tid old /\
  context.(os_sched_call_origin) = RunningInvocation tid old.(taskGeneration) /\
  exists owned waiting,
    environment = Some owned /\
    sem_pend_observed_wait_history environment critical sg context mask before observed eid timeout waiting /\
    sem_pend_source_history owned critical sg context eid old.(taskGeneration) waiting resumed.

Definition sem_pend_source_cleanup_origin environment critical sg context mask before observed
  eid timeout error cleaning tid node : Prop :=
  sem_pend_cleanup_entry sg cleaning tid node /\
  exists resumed old code,
    sem_pend_source_resume_origin environment critical sg context mask before observed
      eid timeout resumed tid old /\
    error = encode_os_err_code code /\
    sem_pend_resume_critical sg eid resumed code (event_pend_cleanup_state sg false cleaning tid node).

Definition sem_pend_source_checkpoint_result environment critical sg context pevent timeout before error checkpoint : Prop :=
  exists eid observed returned mask saved entry current start waiting,
    pevent <> 0 /\ pevent = event_addr sg eid /\ valid_event_id sg eid /\
    sem_query_public_slot before eid observed /\
    sem_pend_context_error (event_slot_type_value before.(EventState) eid)
      before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None /\
    sem_pend_optional_acquire_observation environment critical sg context returned
      mask saved before entry eid observed current /\
    sem_pend_first_critical sg eid timeout entry start waiting /\
    match start with
    | SemPendAcquired => error = 0 /\ checkpoint = waiting
    | SemPendWaiting tid generation =>
        context.(os_sched_call_origin) = RunningInvocation tid generation /\
        exists owned resumed node code,
          environment = Some owned /\
          sem_pend_source_history owned critical sg context eid generation waiting resumed /\
          sem_pend_resume_entry sg resumed eid tid node /\ node.(taskGeneration) = generation /\
          error = encode_os_err_code code /\ sem_pend_resume_critical sg eid resumed code checkpoint
    end.

Definition sem_pend_source_runtime_program external platform environment critical sg context pevent timeout
  : program UCOS2_Verify_State Z :=
  fun before error current =>
    (sem_pend_c_program external critical sg context pevent timeout before error before /\
      (pevent = 0 \/ exists eid, pevent = event_addr sg eid /\
        sem_pend_context_error (event_slot_type_value before.(EventState) eid)
          before.(IntrState).(intNesting) before.(IntrState).(lockNesting) <> None) /\
      current = before) \/
    (exists checkpoint call returned eid,
      sem_pend_source_checkpoint_result environment critical sg context pevent timeout before error checkpoint /\
      pevent <> 0 /\ pevent = event_addr sg eid /\
      sem_pend_context_error (event_slot_type_value before.(EventState) eid)
        before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None /\
      kernel_stack_call_same_call call context /\
      sem_pend_optional_restore_history external platform environment critical sg call checkpoint returned current).

Lemma sem_pend_wait_at_implies_source_wait_at : forall environment critical sg original mask before
  observed eid timeout waiting call current,
  sem_pend_wait_at environment critical sg original mask before observed eid timeout waiting call current ->
  sem_pend_source_wait_at environment critical sg original mask before observed eid timeout waiting call current.
Proof.
  intros * [owned [Howned [Hsame [Hinitial Hpath]]]].
  exists owned; split; [exact Howned|]. split; [exact Hsame|]. split; [exact Hinitial|].
  apply SemPendSourceHistoryLegacy; exact Hpath.
Qed.

Lemma sem_pend_resume_origin_implies_source_resume_origin : forall environment critical sg context mask before
  observed eid timeout resumed tid old,
  sem_pend_observed_resume_origin environment critical sg context mask before observed eid timeout resumed tid old ->
  sem_pend_source_resume_origin environment critical sg context mask before observed eid timeout resumed tid old.
Proof.
  intros * [Hresume [Horigin [owned [waiting [Howned [Hinitial Hpath]]]]]].
  split; [exact Hresume|]. split; [exact Horigin|].
  exists owned, waiting; split; [exact Howned|]. split; [exact Hinitial|].
  apply SemPendSourceHistoryLegacy; exact Hpath.
Qed.

Lemma sem_pend_cleanup_origin_implies_source_cleanup_origin : forall environment critical sg context mask before
  observed eid timeout error cleaning tid node,
  sem_pend_observed_cleanup_origin environment critical sg context mask before observed eid timeout error cleaning tid node ->
  sem_pend_source_cleanup_origin environment critical sg context mask before observed eid timeout error cleaning tid node.
Proof.
  intros * [Hclean [resumed [old [code [Hresume [Herror Hstep]]]]]].
  split; [exact Hclean|]. exists resumed, old, code; split.
  - apply sem_pend_resume_origin_implies_source_resume_origin; exact Hresume.
  - split; assumption.
Qed.

Lemma sem_pend_checkpoint_result_implies_source_checkpoint_result :
  forall environment critical sg context pevent timeout before error checkpoint,
  sem_pend_checkpoint_result environment critical sg context pevent timeout before error checkpoint ->
  sem_pend_source_checkpoint_result environment critical sg context pevent timeout before error checkpoint.
Proof.
  intros environment critical sg context pevent timeout before error checkpoint
    [eid [observed [returned [mask [saved [entry [current [start [waiting
      [Hnonnull [Haddress [Hid [Hslot [Hclear [Hacquire [Hfirst Hlast]]]]]]]]]]]]]]]].
  exists eid, observed, returned, mask, saved, entry, current, start, waiting.
  split; [exact Hnonnull|]. split; [exact Haddress|]. split; [exact Hid|].
  split; [exact Hslot|]. split; [exact Hclear|]. split; [exact Hacquire|].
  split; [exact Hfirst|].
  destruct start as [|tid generation]; [exact Hlast|].
  destruct Hlast as [Horigin [owned [resumed [node [code [Howned [Hpath Hrest]]]]]]].
  split; [exact Horigin|]. exists owned, resumed, node, code.
  split; [exact Howned|]. split; [apply SemPendSourceHistoryLegacy; exact Hpath|exact Hrest].
Qed.

Lemma sem_pend_source_immediate_result : forall environment critical sg context returned pevent timeout
  before eid observed mask saved entry current,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  sem_pend_optional_acquire_observation environment critical sg context returned mask saved
    before entry eid observed current ->
  0 < encode_event_cnt_value current ->
  sem_pend_source_checkpoint_result environment critical sg context pevent timeout before 0
    (sem_count_update_state entry eid current (encode_event_cnt_value current - 1)).
Proof.
  intros; apply sem_pend_checkpoint_result_implies_source_checkpoint_result.
  eapply sem_pend_observed_immediate_result; eassumption.
Qed.

Lemma sem_pend_runtime_program_implies_source_runtime_program :
  forall external platform environment critical sg context pevent timeout before error current,
  sem_pend_runtime_program external platform environment critical sg context pevent timeout before error current ->
  sem_pend_source_runtime_program external platform environment critical sg context pevent timeout before error current.
Proof.
  intros external platform environment critical sg context pevent timeout before error current
    [Hearly|[checkpoint [call [returned [eid [Hcheckpoint Hrest]]]]]].
  - left; exact Hearly.
  - right; exists checkpoint, call, returned, eid; split; [|exact Hrest].
    apply sem_pend_checkpoint_result_implies_source_checkpoint_result; exact Hcheckpoint.
Qed.

Lemma sem_pend_source_wait_selected_resume_origin : forall environment critical sg original mask before observed
  eid timeout waiting call current,
  sem_pend_source_wait_selected_at environment critical sg original mask before observed eid timeout
    waiting call current ->
  exists node, sem_pend_source_resume_origin environment critical sg original mask before observed eid timeout current
    original.(os_sched_call_stack).(stackLeaseSlot) node.
Proof.
  intros * [[owned [Howned [Hsame [Hinitial Hpath]]]] [node Hresume]].
  destruct (sem_pend_observed_wait_history_waiter _ _ _ _ _ _ _ _ _ _ Hinitial)
    as [first [Hfirst Hcontinuation]].
  destruct (sem_pend_source_history_preserves_waiter _ _ _ _ _ _ _ _ Hpath
    first Hfirst Hcontinuation) as [last [Hlast Hlast_continuation]].
  pose proof Hresume as [_ [_ [Hnode _]]].
  assert (last = node) by congruence; subst last.
  exists node; split; [exact Hresume|].
  pose proof Hinitial as [_ [[Horigin _] _]].
  split; [rewrite (proj1 Hlast_continuation); exact Horigin|].
  exists owned, waiting; split; [exact Howned|]. split; [exact Hinitial|].
  rewrite (proj1 Hlast_continuation); exact Hpath.
Qed.

Lemma sem_pend_source_cleanup_result : forall environment critical sg context mask before observed eid
  pevent timeout error cleaning tid node,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  sem_pend_source_cleanup_origin environment critical sg context mask before observed eid timeout
    error cleaning tid node ->
  sem_pend_source_checkpoint_result environment critical sg context pevent timeout before error
    (event_pend_cleanup_state sg false cleaning tid node).
Proof.
  intros * Hnonzero Haddr Hid Hslot Hcontext [Hclean [resumed [old [code [Hresume [Herror Hstep]]]]]].
  destruct Hresume as [Hresume [Horigin [owned [waiting [Howned [Hhistory Hpath]]]]]].
  destruct Hhistory as [Hwaiting [HwaitingSource [HwaitingCache
    [saved [returned [entry [current [first_tid [first [HfirstOrigin HwaitingEq]]]]]]]]]].
  destruct HfirstOrigin as [Hacquire [Hentry [HfirstOrigin [HfirstSource HfirstCache]]]].
  assert (Hsame : first_tid = tid /\ first.(taskGeneration) = old.(taskGeneration))
    by (rewrite Horigin in HfirstOrigin; inversion HfirstOrigin; auto).
  destruct Hsame as [-> Hgeneration].
  exists eid, observed, returned, mask, saved, entry, current,
    (SemPendWaiting tid first.(taskGeneration)), waiting.
  split; [exact Hnonzero|]. split; [exact Haddr|]. split; [exact Hid|]. split; [exact Hslot|].
  split; [exact Hcontext|]. split; [exact Hacquire|]. split.
  - rewrite HwaitingEq; apply sem_pend_wait_entry_first_critical; exact Hentry.
  - split; [exact HfirstOrigin|]. exists owned, resumed, old, code.
    split; [exact Howned|]. split; [rewrite Hgeneration; exact Hpath|].
    split; [exact Hresume|]. split; [symmetry; exact Hgeneration|]. split; assumption.
Qed.

(** The same current Task bytes select success, abort or timeout.
    These branches retain the actual source history without changing it. *)
Lemma sem_pend_source_resume_cleanup_without_timeout : forall environment critical sg context mask
  before observed eid timeout resumed tid old,
  sem_pend_source_resume_origin environment critical sg context mask before observed eid timeout resumed tid old ->
  old.(statPend) <> PendTimeout ->
  sem_pend_source_cleanup_origin environment critical sg context mask before observed eid timeout
    (encode_os_err_code (sem_pend_resume_error (encode_pend_status old.(statPend)))) resumed tid old.
Proof.
  intros * Horigin Hnotimeout.
  pose proof Horigin as [[Hvalid [Hcur [Hold [[Hmulti [Hflag Hregistration]] Hready]]]] Hhistory].
  split.
  - unfold sem_pend_cleanup_entry.
    split; [exact Hvalid|]. split; [exact Hcur|]. split; [exact Hold|].
    split; [destruct old.(statPend); assumption || contradiction|].
    split; [exact Hmulti|]. split; assumption.
  - exists resumed, old, (sem_pend_resume_error (encode_pend_status old.(statPend))).
    split; [exact Horigin|]. split; [reflexivity|].
    exists tid, old; split; [exact Hcur|]. split; [exact Hold|]. split; [reflexivity|].
    destruct old.(statPend); reflexivity || contradiction.
Qed.

Lemma sem_pend_source_resume_cleanup_timeout : forall environment critical sg context mask
  before observed eid timeout resumed tid old current,
  sem_pend_source_resume_origin environment critical sg context mask before observed eid timeout resumed tid old ->
  old.(statPend) = PendTimeout -> mutex_query_lookup resumed eid current ->
  sem_pend_source_cleanup_origin environment critical sg context mask before observed eid timeout 10
    (event_task_remove_state resumed eid current tid old) tid (task_set_event_ptr old None).
Proof.
  intros * Horigin Htimeout He.
  pose proof Horigin as [[Hvalid [Hcur [Hold [[Hmulti [Hflag Hregistration]] Hready]]]] Hhistory].
  rewrite Htimeout in Hregistration.
  destruct (sem_pend_resume_timeout_event sg resumed eid tid old Hvalid Hold Hregistration)
    as [found [Hfound Hin]].
  assert (found = current) by congruence; subst found; split.
  - unfold sem_pend_cleanup_entry; split.
    + eapply UCOS2_event_task_remove_preserves_validity; eassumption.
    + split; [exact Hcur|]. split.
      * cbn [event_task_remove_state replace_TskS replace_EventS TskState glob_task_set_usedtask inUsedTaskStates].
        rewrite Z.eqb_refl; reflexivity.
      * split; [reflexivity|]. split; [exact Hmulti|]. split; assumption.
  - exists resumed, old, OS_ERR_TIMEOUT; split; [exact Horigin|]. split; [reflexivity|].
    exists tid, old; split; [exact Hcur|]. split; [exact Hold|].
    rewrite Htimeout; split; [reflexivity|]. exists current; auto.
Qed.

