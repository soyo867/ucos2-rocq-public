Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Coq.Relations.Relation_Operators.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_status Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.task_stack Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_clear_status_wait_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_acquire_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_program_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_sem_source_projection_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Import TaskStateDef ListNotations.
Local Open Scope Z_scope.

Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_clear_status_spec.
(** Weak local producers below retain the original client runtime. *)
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.kernel_runtime_inv.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_acquire_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_restore_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.


Definition sem_pend_clear_status_call_entry sg call state : Prop :=
  sem_pend_client_phase_context sg call state /\
  sem_pend_source_call_fields sg call state /\ sem_pend_caller_status_clear call state.

Lemma sem_pend_clear_status_call_entry_return : forall environment critical sg call before returned after,
  sem_pend_client_return_source environment critical sg call before returned after ->
  sem_pend_clear_status_call_entry sg call before -> sem_pend_clear_status_call_entry sg returned after.
Proof.
  intros environment critical sg call before returned after Hreturn [Hcontext [Hfields Hclear]].
  pose proof (sem_pend_client_phase_context_return _ _ _ _ _ _ _ Hreturn Hcontext) as Hafter.
  pose proof (sem_pend_client_return_source_preserves_call_fields _ _ _ _ _ _ _ Hreturn
    (proj1 Hcontext) (proj1 (proj2 Hcontext)) Hfields) as Hfields'.
  pose proof (sem_pend_client_return_preserves_clear_status _ _ _ _ _ _ _ Hreturn
    (proj1 Hcontext) (proj1 (proj2 Hcontext)) Hclear) as Hclear'.
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hreturn) as [_ [_ Hstack]].
  split; [exact Hafter|]. split; [|exact Hclear'].
  unfold sem_pend_source_call_fields, flag_pend_non_idle_at in *; rewrite Hstack; exact Hfields'.
Qed.

Lemma sem_pend_clear_status_acquire_wait_entry :
  forall environment critical sg call returned mask saved before acquired eid observed current,
  sem_pend_client_acquire_observation environment critical sg call returned mask saved
    before acquired eid observed current ->
  sem_pend_clear_status_call_entry sg returned acquired -> encode_event_cnt_value current = 0 ->
  event_object_layout_prop sg eid ->
  exists node,
    sem_pend_clear_status_wait_entry sg acquired eid current returned.(os_sched_call_stack).(stackLeaseSlot) node /\
    returned.(os_sched_call_origin) = RunningInvocation returned.(os_sched_call_stack).(stackLeaseSlot) node.(taskGeneration) /\
    kernel_call_task_source returned acquired /\ sched_current_consistency acquired.(TskState) acquired.(SchedState).
Proof.
  intros * Hacquire [Hcontext [Hfields Hclear]] Hzero Hlayout.
  pose proof Hacquire as [_ [_ [_ [_ [_ [Hlookup [_ [Htype Hg]]]]]]]].
  destruct Hcontext as [Hvalid [Hsource [Hrunning [Hidle [Havailable Hcache]]]]].
  destruct Hfields as [_ [[nonidle [Hnonidle [Hgen Hprio]]] [node [Hnode Hnone]]]].
  destruct (kernel_call_task_source_current_at returned acquired Hsource) as [Hcurrent [found [Hfound Hgeneration]]].
  assert (found = node) by congruence; subst found.
  assert (nonidle = node) by congruence; subst nonidle.
  destruct Hnone as [Hevent [Hmulti Hflag]].
  exists node; split.
  - unfold sem_pend_clear_status_wait_entry.
    exact (conj Hvalid (conj Hzero (conj Hcurrent (conj Hnode (conj Hlookup (conj Htype
      (conj Hprio (conj Hevent (conj Hmulti (conj Hflag (conj (Hclear node Hnode) Hlayout))))))))))).
  - split.
    + rewrite Hgeneration; exact (proj1 Hsource).
    + exact (conj Hsource Hcache).
Qed.

Lemma sem_pend_clear_status_wait_preserves_call_source : forall sg context entry eid current tid old timeout,
  sem_pend_clear_status_wait_entry sg entry eid current tid old ->
  kernel_call_task_source context entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  let waiting := event_pend_state sg entry eid current tid old PendSem timeout in
  UCOS2_state_inv sg waiting /\ kernel_call_task_source context waiting /\
  sched_current_consistency waiting.(TskState) waiting.(SchedState).
Proof.
  intros sg context entry eid current tid old timeout Hentry Hsource Hcache waiting.
  pose proof Hentry as [_ [_ [Hcurrent [Hnode _]]]].
  split; [apply sem_pend_clear_status_wait_entry_preserves_validity; exact Hentry|].
  split.
  - destruct Hsource as [Hlease [Hactive Hcur]].
    split; [exact Hlease|]. split.
    + unfold waiting; cbn [event_pend_state event_wait_state replace_TskS replace_SchedS replace_EventS TskState].
      eapply glob_task_set_usedtask_preserves_invocation_active;
        [exact Hnode|reflexivity|exact Hactive].
    + exact Hcur.
  - unfold sched_current_consistency in Hcache; rewrite Hcurrent in Hcache.
    destruct Hcache as [node [Hlookup Hpriority]].
    assert (node = old) by congruence; subst node.
    unfold sched_current_consistency.
    change (match entry.(SchedState).(curTaskID) with
      | None => entry.(SchedState).(curSchedPrio) = None
      | Some selected => exists node,
          (if Z.eqb selected tid then
             Some (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid))
           else entry.(TskState).(inUsedTaskStates) selected) = Some node /\
          entry.(SchedState).(curSchedPrio) = Some node.(curPrio)
      end).
    rewrite Hcurrent; exists (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)).
    split; [rewrite Z.eqb_refl; reflexivity|exact Hpriority].
Qed.

Definition sem_pend_clear_status_wait_origin environment critical sg context returned mask saved before observed
  entry eid current tid old : Prop :=
  sem_pend_client_acquire_observation environment critical sg context returned mask saved
    before entry eid observed current /\
  sem_pend_clear_status_wait_entry sg entry eid current tid old /\
  context.(os_sched_call_origin) = RunningInvocation tid old.(taskGeneration) /\
  kernel_call_task_source context entry /\
  sched_current_consistency entry.(TskState) entry.(SchedState).

Definition sem_pend_clear_status_wait_history environment critical sg context mask before observed
  eid timeout waiting : Prop :=
  UCOS2_state_inv sg waiting /\ kernel_call_task_source context waiting /\
  sched_current_consistency waiting.(TskState) waiting.(SchedState) /\
  exists saved returned entry current tid old,
    sem_pend_clear_status_wait_origin environment critical sg context returned mask saved before observed
      entry eid current tid old /\
    waiting = event_pend_state sg entry eid current tid old PendSem timeout.

Lemma sem_pend_clear_status_wait_origin_history : forall environment critical sg context returned mask saved
  before observed entry eid current tid old timeout,
  sem_pend_clear_status_wait_origin environment critical sg context returned mask saved before observed
    entry eid current tid old ->
  sem_pend_clear_status_wait_history environment critical sg context mask before observed eid timeout
    (event_pend_state sg entry eid current tid old PendSem timeout).
Proof.
  intros * Horigin.
  pose proof Horigin as [Hacquire [Hentry [Horiginal [Hsource Hcache]]]].
  destruct (sem_pend_clear_status_wait_preserves_call_source sg context entry eid current tid old timeout
    Hentry Hsource Hcache) as [Hvalid [Hwaiting Hwaiting_cache]].
  split; [exact Hvalid|]. split; [exact Hwaiting|]. split; [exact Hwaiting_cache|].
  exists saved, returned, entry, current, tid, old; split; [exact Horigin|reflexivity].
Qed.


Lemma sem_pend_clear_status_wait_history_waiter : forall environment critical sg context mask before observed
  eid timeout waiting,
  sem_pend_clear_status_wait_history environment critical sg context mask before observed eid timeout waiting ->
  exists node,
    waiting.(TskState).(inUsedTaskStates) context.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
    sem_pend_wait_continuation eid context.(os_sched_call_stack).(stackLeaseGeneration) node.
Proof.
  intros * [_ [Hsource [_ [saved [returned [entry [current [tid [old [Horigin ->]]]]]]]]]].
  destruct Horigin as [_ [Hentry [Horiginal [Hentry_source Hcache]]]].
  pose proof (proj1 Hentry_source) as Hlease; rewrite Horiginal in Hlease.
  assert (Htid : tid = context.(os_sched_call_stack).(stackLeaseSlot)) by congruence.
  assert (Hgeneration : old.(taskGeneration) = context.(os_sched_call_stack).(stackLeaseGeneration)) by congruence.
  subst tid.
  pose proof Hentry as [Hvalid [_ [_ [Hold [_ [_ [_ [_ [Hmulti [Hflag [Hclear _]]]]]]]]]]].
  exists (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)); split.
  - cbn [event_pend_state event_wait_state replace_TskS replace_SchedS replace_EventS
      TskState glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
  - rewrite <- Hgeneration; apply sem_pend_clear_status_wait_continuation; assumption.
Qed.

Definition sem_pend_clear_status_resume_origin environment critical sg context mask before observed
  eid timeout resumed tid old : Prop :=
  sem_pend_resume_entry sg resumed eid tid old /\
  context.(os_sched_call_origin) = RunningInvocation tid old.(taskGeneration) /\
  exists waiting,
    sem_pend_clear_status_wait_history environment critical sg context mask before observed eid timeout waiting /\
    sem_pend_client_wait_source environment critical sg context eid old.(taskGeneration) waiting resumed.

Definition sem_pend_clear_status_cleanup_origin environment critical sg context mask before observed
  eid timeout error cleaning tid node : Prop :=
  sem_pend_cleanup_entry sg cleaning tid node /\
  exists resumed old code,
    sem_pend_clear_status_resume_origin environment critical sg context mask before observed
      eid timeout resumed tid old /\
    error = encode_os_err_code code /\
    sem_pend_resume_critical sg eid resumed code (event_pend_cleanup_state sg false cleaning tid node).

Lemma sem_pend_clear_status_cleanup_result : forall environment critical sg context mask before observed eid
  pevent timeout error cleaning tid node,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  sem_pend_clear_status_cleanup_origin environment critical sg context mask before observed eid timeout
    error cleaning tid node ->
  sem_pend_client_checkpoint_result environment critical sg context pevent timeout before error
    (event_pend_cleanup_state sg false cleaning tid node).
Proof.
  intros * Hnonzero Haddr Hid Hslot Hcontext [Hclean [resumed [old [code [Hresume [Herror Hstep]]]]]].
  destruct Hresume as [Hresume [Horigin [waiting [Hhistory Hpath]]]].
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
  - rewrite HwaitingEq; apply sem_pend_clear_status_wait_entry_first_critical; exact Hentry.
  - split; [exact HfirstOrigin|]. exists resumed, old, code.
    split; [rewrite Hgeneration; exact Hpath|].
    split; [exact Hresume|]. split; [symmetry; exact Hgeneration|]. split; assumption.
Qed.

Lemma sem_pend_clear_status_resume_cleanup_without_timeout : forall environment critical sg context mask
  before observed eid timeout resumed tid old,
  sem_pend_clear_status_resume_origin environment critical sg context mask before observed eid timeout resumed tid old ->
  old.(statPend) <> PendTimeout ->
  sem_pend_clear_status_cleanup_origin environment critical sg context mask before observed eid timeout
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

Lemma sem_pend_clear_status_resume_cleanup_timeout : forall environment critical sg context mask
  before observed eid timeout resumed tid old current,
  sem_pend_clear_status_resume_origin environment critical sg context mask before observed eid timeout resumed tid old ->
  old.(statPend) = PendTimeout -> mutex_query_lookup resumed eid current ->
  sem_pend_clear_status_cleanup_origin environment critical sg context mask before observed eid timeout 10
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

Definition sem_pend_clear_status_phase_wait_at environment critical sg original mask initial observed eid timeout
  waiting call current : Prop :=
  kernel_stack_call_same_call call original /\
  sem_pend_clear_status_wait_history environment critical sg original mask initial observed eid timeout waiting /\
  sem_pend_client_wait_source environment critical sg original eid
    original.(os_sched_call_stack).(stackLeaseGeneration) waiting current /\
  exists node, current.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
    sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) node.

Definition sem_pend_clear_status_phase_selected_at environment critical sg original mask initial observed eid timeout
  waiting call current : Prop :=
  sem_pend_clear_status_phase_wait_at environment critical sg original mask initial observed eid timeout
    waiting call current /\
  exists node, sem_pend_resume_entry sg current eid original.(os_sched_call_stack).(stackLeaseSlot) node.

Lemma sem_pend_clear_status_phase_wait_at_initial : forall environment critical sg original mask initial observed
  eid timeout waiting call,
  kernel_stack_call_same_call call original ->
  sem_pend_clear_status_wait_history environment critical sg original mask initial observed eid timeout waiting ->
  sem_pend_clear_status_phase_wait_at environment critical sg original mask initial observed eid timeout waiting call waiting.
Proof.
  intros * Hsame Hhistory; split; [exact Hsame|]. split; [exact Hhistory|].
  split; [apply sem_pend_client_wait_source_refl|].
  exact (sem_pend_clear_status_wait_history_waiter _ _ _ _ _ _ _ _ _ _ Hhistory).
Qed.

Lemma sem_pend_clear_status_phase_wait_at_return : forall environment critical sg original mask initial observed
  eid timeout waiting call before returned after,
  sem_pend_clear_status_phase_wait_at environment critical sg original mask initial observed eid timeout waiting call before ->
  UCOS2_state_inv sg before ->
  sem_pend_client_return_source environment critical sg call before returned after ->
  kernel_call_task_source call before -> kernel_call_task_source returned after ->
  sem_pend_clear_status_phase_wait_at environment critical sg original mask initial observed eid timeout waiting returned after.
Proof.
  intros * [Hsame [Hhistory [Hpath [node [Hnode Hwait]]]]] Hvalid Hreturn Htask Hafter.
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hreturn) as Hreturned.
  assert (Hnode_call : before.(TskState).(inUsedTaskStates)
    call.(os_sched_call_stack).(stackLeaseSlot) = Some node).
  { rewrite (proj2 (proj2 Hsame)); exact Hnode. }
  destruct (sem_pend_client_return_source_waiter_projection environment critical sg call before returned after
    node eid _ Hreturn Hvalid Htask Hafter Hnode_call Hwait) as [next [Hnext Heffects]].
  rewrite (proj2 (proj2 Hsame)) in Hnext.
  split.
  - unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence.
  - split; [exact Hhistory|]. split.
    + eapply SemPendClientWaitTrans; [exact Hpath|]. eapply SemPendClientWaitReturn; eassumption.
    + exists next; split; [exact Hnext|]. eapply sem_pend_wait_trace_preserves_continuation; eassumption.
Qed.

Lemma sem_pend_clear_status_phase_selected_from_member : forall environment critical sg original mask initial observed
  eid timeout waiting call current,
  sem_pend_clear_status_phase_wait_at environment critical sg original mask initial observed eid timeout waiting call current ->
  sem_pend_client_phase_context sg call current ->
  In original.(os_sched_call_stack).(stackLeaseSlot) current.(SchedState).(readyList) ->
  sem_pend_clear_status_phase_selected_at environment critical sg original mask initial observed eid timeout
    waiting call current.
Proof.
  intros * Hwait [Hvalid [Hsource Hrest]] Hmember; split; [exact Hwait|].
  destruct Hwait as [Hsame [Hhistory [Hpath [node [Hnode Hcont]]]]].
  destruct (kernel_call_task_source_current_at call current Hsource) as [Hcurrent Hfound].
  rewrite (proj2 (proj2 Hsame)) in Hcurrent.
  destruct (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid)))) _ Hmember)
    as [ready [Hready [_ Heffective]]].
  assert (ready = node) by congruence; subst ready.
  destruct (sem_pend_wait_ready_resume_registration _ _ _ Hcont Heffective) as [Hregistration Hgeneration].
  exists node; unfold sem_pend_resume_entry; auto.
Qed.

Lemma sem_pend_clear_status_phase_selected_resume_origin : forall environment critical sg original mask initial observed
  eid timeout waiting call current,
  sem_pend_clear_status_phase_selected_at environment critical sg original mask initial observed eid timeout
    waiting call current ->
  exists node, sem_pend_clear_status_resume_origin environment critical sg original mask initial observed eid timeout
    current original.(os_sched_call_stack).(stackLeaseSlot) node.
Proof.
  intros * [[Hsame [Hhistory [Hpath [node [Hnode Hcont]]]]] [selected Hselected]].
  pose proof Hselected as [Hvalid [Hcurrent [Hselected_node Hrest]]].
  assert (selected = node) by congruence; subst selected.
  pose proof (proj1 Hcont) as Hgeneration.
  pose proof Hhistory as [_ [Hsource _]].
  exists node; split; [exact Hselected|]. split.
  - rewrite Hgeneration; exact (proj1 Hsource).
  - exists waiting; split; [exact Hhistory|]. rewrite Hgeneration; exact Hpath.
Qed.

(** CPU cuts for the clear-status caller; the public runtime is unchanged. *)
Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_runtime_inv Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_return_resources_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_acquire_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_restore_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_program_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.flag_fields_resources Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.tick Ucos2Verify.lib.memory Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.statistics Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_storage Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_wait_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.


Definition sem_pend_clear_status_phase_save_pre phase environment critical sg call mask before : Prop :=
  sem_pend_client_phase_context sg call before /\
  match phase with
  | SemPendAcquirePhase pevent eid observed =>
      sem_pend_call_input critical sg call.(os_sched_call_invocation) pevent before eid observed /\
      pevent <> 0 /\ sem_pend_context_error (event_slot_type_value before.(EventState) eid)
        before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None /\
      sem_pend_source_call_fields sg call before /\ sem_pend_caller_status_clear call before
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      mask = initial_mask /\ sem_pend_clear_status_phase_selected_at environment critical sg original initial_mask
        initial observed eid timeout waiting call before
  | SemPendReturnPhase => False
  end.

Definition sem_pend_clear_status_phase_save_observation phase environment critical sg call returned mask saved
  before acquired : Prop :=
  sem_pend_client_phase_context sg returned acquired /\
  match phase with
  | SemPendAcquirePhase pevent eid observed =>
      exists current, sem_pend_client_acquire_observation environment critical sg call returned mask saved
        before acquired eid observed current /\ sem_pend_clear_status_call_entry sg returned acquired /\
        sem_pend_blocking_call_stage sg returned acquired
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      mask = initial_mask /\ sem_pend_clear_status_phase_selected_at environment critical sg original initial_mask
        initial observed eid timeout waiting returned acquired
  | SemPendReturnPhase => False
  end.

Definition sem_pend_clear_status_phase_save_input phase environment local critical sg call mask before : Assertion :=
  coq_prop (sem_pend_clear_status_phase_save_pre phase environment critical sg call mask before) &&
  sem_pend_fields_closed environment local sg call mask before.

Definition sem_pend_clear_status_phase_save_output phase environment local critical sg call mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (sem_pend_client_return_source environment critical sg call before returned acquired /\
      interrupt_saved_value mask saved /\ sem_pend_save_rely sg before acquired /\
      sem_pend_clear_status_phase_save_observation phase environment critical sg call returned mask saved before acquired) &&
    sem_pend_fields_masked environment local critical sg returned saved acquired acquired.

Definition sem_pend_clear_status_phase_restore_pre phase environment critical sg call mask checkpoint : Prop :=
  match phase with
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      mask = initial_mask /\ sem_pend_client_phase_context sg call checkpoint /\
      sem_pend_clear_status_phase_wait_at environment critical sg original initial_mask initial observed
        eid timeout waiting call checkpoint
  | SemPendReturnPhase => sem_pend_clear_status_call_entry sg call checkpoint
  | SemPendAcquirePhase _ _ _ => False
  end.

Definition sem_pend_clear_status_phase_restore_observation phase environment critical sg
  (call : OsSchedCallContext) (checkpoint : UCOS2_Verify_State) returned current : Prop :=
  match phase with
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      sem_pend_client_phase_context sg returned current /\
      sem_pend_clear_status_phase_wait_at environment critical sg original initial_mask initial observed
        eid timeout waiting returned current
  | SemPendReturnPhase => sem_pend_clear_status_call_entry sg returned current
  | SemPendAcquirePhase _ _ _ => False
  end.

Definition sem_pend_clear_status_phase_restore_input phase environment local critical sg call mask saved acquired
  checkpoint : Assertion :=
  coq_prop (interrupt_saved_value mask saved /\
    sem_pend_clear_status_phase_restore_pre phase environment critical sg call mask checkpoint) &&
  sem_pend_fields_masked environment local critical sg call saved acquired checkpoint.

Definition sem_pend_clear_status_phase_restore_output phase environment local critical sg call mask checkpoint : Assertion :=
  EX returned current,
    coq_prop (sem_pend_client_return_source environment critical sg call checkpoint returned current /\
      sem_pend_clear_status_phase_restore_observation phase environment critical sg call checkpoint returned current) &&
    sem_pend_fields_closed environment local sg returned mask current.

Lemma sem_pend_clear_status_phase_save_observations : forall phase environment critical sg call returned mask saved before acquired,
  sem_pend_clear_status_phase_save_pre phase environment critical sg call mask before ->
  sem_pend_client_return_source environment critical sg call before returned acquired ->
  interrupt_saved_value mask saved -> sem_pend_save_rely sg before acquired ->
  interrupt_in_range acquired.(IntrState) ->
  sem_pend_clear_status_phase_save_observation phase environment critical sg call returned mask saved before acquired.
Proof.
  intros phase environment critical sg call returned mask saved before acquired [Hcontext Hpre]
    Hreturn Hsaved Hrely Hrange.
  pose proof (sem_pend_client_phase_context_return _ _ _ _ _ _ _ Hreturn Hcontext) as Hafter.
  split; [exact Hafter|]. destruct phase as [pevent eid observed|original initial_mask initial observed eid timeout waiting|].
  - destruct Hpre as [Hinput [Hnonnull [Hclear [Hfields Hstatus]]]].
    destruct (sem_pend_client_acquire_observation_from_input environment critical sg call returned pevent eid observed
      mask saved before acquired Hreturn (proj1 Hcontext) Hinput Hnonnull Hclear Hsaved) as [current Hobservation].
    exists current; split; [exact Hobservation|]. split.
    + eapply sem_pend_clear_status_call_entry_return; [exact Hreturn|exact (conj Hcontext (conj Hfields Hstatus))].
    + assert (Hguards : before.(IntrState).(intNesting) <= 0 /\ before.(IntrState).(lockNesting) <= 0).
      { change ((if negb (Z.eqb (event_slot_type_value before.(EventState) eid) 3)
          then Some OS_ERR_EVENT_TYPE else
          if Z.ltb 0 before.(IntrState).(intNesting) then Some OS_ERR_PEND_ISR else
          if Z.ltb 0 before.(IntrState).(lockNesting) then Some OS_ERR_PEND_LOCKED else None) = None) in Hclear.
        destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 3) in Hclear;
          cbn [negb] in Hclear; [|discriminate].
        destruct (Z.ltb 0 before.(IntrState).(intNesting)) eqn:Hint in Hclear; [discriminate|].
        destruct (Z.ltb 0 before.(IntrState).(lockNesting)) eqn:Hlock in Hclear; [discriminate|].
        apply Z.ltb_ge in Hint; apply Z.ltb_ge in Hlock; auto. }
      destruct Hafter as [_ [_ [Hrunning [Hidle [Havailable Hcache]]]]].
      destruct Hrely as [[Hrunning_eq Hcounters] Hrest].
      unfold sem_pend_blocking_call_stage; split; [exact (Hidle Hrunning)|].
      split; [exact Havailable|]. unfold interrupt_in_range in Hrange; rewrite Hcounters in Hrange.
      rewrite Hcounters; lia.
  - destruct Hpre as [Hmask [Hwait [old Hentry]]]. split; [exact Hmask|].
    pose proof (sem_pend_clear_status_phase_wait_at_return environment critical sg original initial_mask initial observed
      eid timeout waiting call before returned acquired Hwait (proj1 Hcontext) Hreturn
      (proj1 (proj2 Hcontext)) (proj1 (proj2 Hafter))) as Hwait'.
    pose proof Hentry as [_ [Hcurrent [_ [_ Hmember]]]].
    eapply sem_pend_clear_status_phase_selected_from_member; [exact Hwait'|exact Hafter|].
    exact (proj2 (proj2 (proj2 Hrely)) _ Hcurrent Hmember).
  - contradiction.
Qed.

Lemma sem_pend_clear_status_call_entry_from_stage : forall sg call state,
  UCOS2_state_inv sg state -> sem_pend_task_call_stage sg call state ->
  kernel_running_idle_ready sg state -> kernel_call_stack_available call state ->
  sem_pend_clear_status_call_entry sg call state.
Proof.
  intros sg call state Hvalid Hstage Hidle Havailable.
  pose proof (sem_pend_client_phase_context_from_task_stage _ _ _ Hvalid Hstage Hidle Havailable) as Hcontext.
  destruct Hstage as [Hsource [Hrunning [old [Hready [Hgeneration [Hnonidle Hnone]]]]]].
  pose proof (proj1 Hready) as Hold.
  split; [exact Hcontext|]. split.
  - split; [exact Hrunning|]. split.
    + exists old; exact (conj Hold (conj Hgeneration Hnonidle)).
    + exists old; exact (conj Hold Hnone).
  - intros node Hnode; assert (node = old) by congruence; subst node.
    apply task_effectively_ready_has_no_pending; exact (proj2 (proj2 (proj2 (proj2 Hready)))).
Qed.

Lemma sem_pend_clear_status_immediate_checkpoint : forall sg call before eid event fields timeout checkpoint,
  sem_pend_clear_status_call_entry sg call before ->
  before.(EventState).(inUsedEventStates) eid = Some event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  event.(semFields) = Some fields -> sem_pend_first_critical sg eid timeout before SemPendAcquired checkpoint ->
  sem_pend_clear_status_call_entry sg call checkpoint.
Proof.
  intros sg call before eid event fields timeout checkpoint [[Hvalid Hcontext] Hfields] Hevent Htype Hpayload Hstep.
  pose proof (sem_pend_immediate_preserves_validity sg before eid event fields timeout checkpoint
    Hvalid Hevent Htype Hpayload Hstep) as Hvalid'.
  destruct (sem_pend_immediate_count_update sg before eid event fields timeout checkpoint Hevent Hpayload Hstep)
    as [Hpositive ->].
  exact (conj (conj Hvalid' Hcontext) Hfields).
Qed.

Lemma sem_pend_clear_status_cleanup_checkpoint : forall sg call resumed eid old result checkpoint,
  sem_pend_resume_entry sg resumed eid call.(os_sched_call_stack).(stackLeaseSlot) old ->
  sem_pend_client_phase_context sg call resumed -> old.(curPrio) <> sg.(osLowestPrio) ->
  sem_pend_resume_critical sg eid resumed result checkpoint ->
  sem_pend_clear_status_call_entry sg call checkpoint.
Proof.
  intros * Hentry [Hvalid [Hsource [Hrunning [Hidle [Havailable Hcache]]]]] Hnonidle Hstep.
  destruct (sem_pend_client_cleanup_checkpoint sg call resumed eid old result checkpoint
    Hentry Hsource Hrunning Hnonidle Hcache Hidle Havailable Hstep)
    as [Hvalid' [Hnormal [Hstage' [Hidle' Havailable']]]].
  eapply sem_pend_clear_status_call_entry_from_stage; eassumption.
Qed.

Lemma sem_pend_clear_status_phase_return_restore_observation : forall environment critical sg call mask checkpoint returned current,
  sem_pend_clear_status_phase_restore_pre SemPendReturnPhase environment critical sg call mask checkpoint ->
  sem_pend_client_return_source environment critical sg call checkpoint returned current ->
  sem_pend_clear_status_phase_restore_observation SemPendReturnPhase environment critical sg call checkpoint returned current.
Proof. intros; eapply sem_pend_clear_status_call_entry_return; eassumption. Qed.

Lemma sem_pend_clear_status_phase_save_output_intro : forall phase environment local critical sg call returned
  mask saved before acquired,
  sem_pend_clear_status_phase_save_pre phase environment critical sg call mask before ->
  sem_pend_client_return_source environment critical sg call before returned acquired ->
  interrupt_saved_value mask saved -> sem_pend_save_rely sg before acquired ->
  sem_pend_fields_masked environment local critical sg returned saved acquired acquired |--
  sem_pend_clear_status_phase_save_output phase environment local critical sg call mask saved before.
Proof.
  intros * Hpre Hreturn Hsaved Hrely heap Howner.
  pose proof (sem_pend_fields_masked_observations environment local critical sg returned saved acquired acquired
    heap Howner) as [Hvalid Hrange].
  pose proof (sem_pend_clear_status_phase_save_observations _ _ _ _ _ _ _ _ _ _ Hpre Hreturn Hsaved Hrely Hrange) as Hphase.
  exists returned, acquired; split; [exact (conj Hreturn (conj Hsaved (conj Hrely Hphase)))|exact Howner].
Qed.

Lemma sem_pend_clear_status_phase_uninterrupted_save : forall phase environment local critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external) environment.(task_stack_call_platform) critical arch)
  sg call state mask registers before final_registers acquired after (frame : Assertion),
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (sem_pend_clear_status_phase_save_input phase environment local critical sg call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before final_registers acquired after ->
  acquired = state /\ final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired after /\
  (sem_pend_clear_status_phase_save_output phase environment local critical sg call mask final_registers.(kernel_save_r0)
    state ** frame) after.
Proof.
  intros phase environment local critical arch save sg call state mask registers before final_registers acquired after
    frame Hcursor Hvalid Hmask Hinput Hactual.
  assert (Hpre : sem_pend_clear_status_phase_save_pre phase environment critical sg call mask state).
  { assert (Hobserve : sem_pend_clear_status_phase_save_input phase environment local critical sg call mask state ** frame |--
      coq_prop (sem_pend_clear_status_phase_save_pre phase environment critical sg call mask state)).
    { intros heap [owned [rest [Hjoin [[Hfact Howner] Hframe]]]]; exact Hfact. } exact (Hobserve before Hinput). }
  assert (Hclosed : (sem_pend_fields_closed environment local sg call mask state ** frame) before).
  { assert (Hforget : sem_pend_clear_status_phase_save_input phase environment local critical sg call mask state ** frame |--
      sem_pend_fields_closed environment local sg call mask state ** frame).
    { intros heap [owned [rest [Hjoin [[Hfact Howner] Hframe]]]]; exists owned, rest; exact (conj Hjoin (conj Howner Hframe)). } exact (Hforget before Hinput). }
  destruct (kernel_continuation_call_uninterrupted_save _ _ _ _ arch environment.(task_stack_call_continuations)
    save kernel_program_fields_inv local sg (task_stack_call_active_key call) call state mask registers before
    final_registers acquired after frame Hcursor Hvalid Hmask Hclosed Hactual)
    as [Hstate [Hvalue [Hexecution Howner]]].
  assert (Hsaved : interrupt_saved_value mask final_registers.(kernel_save_r0)).
  { rewrite Hvalue; split; assumption. }
  assert (Hrely : sem_pend_save_rely sg state state).
  { unfold sem_pend_save_rely, kernel_call_control_rely; auto. }
  pose proof (sem_pend_clear_status_phase_save_output_intro phase environment local critical sg call call mask
    final_registers.(kernel_save_r0) state state Hpre
    (sem_pend_client_return_source_refl environment critical sg call state) Hsaved Hrely) as Hpack.
  assert (Hframe : sem_pend_fields_masked environment local critical sg call final_registers.(kernel_save_r0)
      state state ** frame |--
    sem_pend_clear_status_phase_save_output phase environment local critical sg call mask final_registers.(kernel_save_r0)
      state ** frame).
  { sep_apply Hpack; entailer!. }
  exact (conj Hstate (conj Hvalue (conj Hexecution (Hframe after Howner)))).
Qed.

Lemma sem_pend_clear_status_phase_uninterrupted_restore : forall phase environment local critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg call mask saved acquired checkpoint cursor before written middle final_cursor after (frame : Assertion),
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (sem_pend_clear_status_phase_restore_input phase environment local critical sg call mask saved acquired checkpoint ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (sem_pend_clear_status_phase_restore_output phase environment local critical sg call mask checkpoint ** frame) after.
Proof.
  intros phase environment local critical arch restore sg call mask saved acquired checkpoint cursor before written middle
    final_cursor after frame Hr0 Hmask Hinput Hprefix Hsuffix.
  assert (Hpure : interrupt_saved_value mask saved /\
      sem_pend_clear_status_phase_restore_pre phase environment critical sg call mask checkpoint).
  { assert (Hobserve : sem_pend_clear_status_phase_restore_input phase environment local critical sg call mask saved acquired
      checkpoint ** frame |-- coq_prop (interrupt_saved_value mask saved /\
        sem_pend_clear_status_phase_restore_pre phase environment critical sg call mask checkpoint)).
    { intros heap [owned [rest [Hjoin [[Hfact Howner] Hframe]]]]; exact Hfact. } exact (Hobserve before Hinput). }
  destruct Hpure as [Hsaved Hpre].
  assert (Hmasked : (sem_pend_fields_masked environment local critical sg call saved acquired checkpoint ** frame) before).
  { assert (Hforget : sem_pend_clear_status_phase_restore_input phase environment local critical sg call mask saved acquired
      checkpoint ** frame |-- sem_pend_fields_masked environment local critical sg call saved acquired checkpoint ** frame).
    { intros heap [owned [rest [Hjoin [[Hfact Howner] Hframe]]]]; exists owned, rest; exact (conj Hjoin (conj Howner Hframe)). } exact (Hforget before Hinput). }
  destruct (kernel_continuation_call_uninterrupted_restore _ _ _ _ arch environment.(task_stack_call_continuations)
    restore kernel_program_fields_inv local sg (task_stack_call_active_key call) call saved acquired checkpoint
    cursor before written middle final_cursor after frame Hr0 Hmask Hmasked Hprefix Hsuffix)
    as [Hexecution [Hvalue Hclosed]].
  rewrite (proj2 Hsaved) in Hclosed.
  assert (Hsource : sem_pend_client_return_source environment critical sg call checkpoint call checkpoint)
    by apply sem_pend_client_return_source_refl.
  assert (Hphase : sem_pend_clear_status_phase_restore_observation phase environment critical sg call checkpoint call checkpoint).
  { destruct phase; simpl in *; [contradiction|tauto|].
    exact Hpre. }
  assert (Hpack : sem_pend_fields_closed environment local sg call mask checkpoint |--
    sem_pend_clear_status_phase_restore_output phase environment local critical sg call mask checkpoint).
  { intros heap Howner; exists call, checkpoint; exact (conj (conj Hsource Hphase) Howner). }
  assert (Hframe : sem_pend_fields_closed environment local sg call mask checkpoint ** frame |--
    sem_pend_clear_status_phase_restore_output phase environment local critical sg call mask checkpoint ** frame).
  { sep_apply Hpack; entailer!. }
  exact (conj Hexecution (conj Hvalue (Hframe after Hclosed))).
Qed.

Lemma sem_pend_clear_status_phase_wait_restore_observation : forall environment critical sg original initial_mask initial
  observed eid timeout waiting call checkpoint returned current,
  sem_pend_client_phase_context sg call checkpoint ->
  sem_pend_clear_status_phase_wait_at environment critical sg original initial_mask initial observed
    eid timeout waiting call checkpoint ->
  sem_pend_client_return_source environment critical sg call checkpoint returned current ->
  sem_pend_clear_status_phase_restore_observation (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment critical sg call checkpoint returned current.
Proof.
  intros * Hcontext Hwait Hreturn.
  pose proof (sem_pend_client_phase_context_return _ _ _ _ _ _ _ Hreturn Hcontext) as Hafter.
  split; [exact Hafter|].
  eapply sem_pend_clear_status_phase_wait_at_return;
    [exact Hwait|exact (proj1 Hcontext)|exact Hreturn|
     exact (proj1 (proj2 Hcontext))|exact (proj1 (proj2 Hafter))].
Qed.

Lemma sem_pend_clear_status_phase_wait_restore_pre : forall environment critical sg original returned mask saved
  before observed entry eid event tid old timeout,
  sem_pend_clear_status_wait_origin environment critical sg original returned mask saved before observed
    entry eid event tid old ->
  entry.(SchedState).(isRunning) = true -> kernel_running_idle_ready sg entry ->
  kernel_call_stack_available original entry ->
  sem_pend_clear_status_phase_restore_pre
    (SemPendWaitPhase original mask before observed eid timeout
      (event_pend_state sg entry eid event tid old PendSem timeout))
    environment critical sg original mask (event_pend_state sg entry eid event tid old PendSem timeout).
Proof.
  intros * Horigin Hrunning Hidle Havailable.
  pose proof (sem_pend_clear_status_wait_origin_history environment critical sg original returned mask saved
    before observed entry eid event tid old timeout Horigin) as Hhistory.
  pose proof Hhistory as [Hvalid [Hsource [Hcache Hrest]]].
  pose proof Horigin as [_ [Hentry [Horigin_call Hentry_rest]]].
  pose proof Hentry as [_ [_ [_ [Hold [_ [_ [Hnonidle Hentry_tail]]]]]]].
  split; [reflexivity|]. split.
  - split; [exact Hvalid|]. split; [exact Hsource|]. split; [exact Hrunning|].
    split.
    + intros _; change (task_idle_ready sg
        (glob_task_set_usedtask entry.(TskState) tid
          (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)))).
      eapply task_update_non_idle_preserves_idle_ready; [exact Hold|exact Hnonidle|exact (Hidle Hrunning)].
    + split; [exact Havailable|exact Hcache].
  - eapply sem_pend_clear_status_phase_wait_at_initial; [unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call; auto|exact Hhistory].
Qed.

Lemma sem_pend_clear_status_phase_wait_restore_returned_pre : forall environment critical sg original returned mask saved
  before observed entry eid event tid old timeout,
  sem_pend_clear_status_wait_origin environment critical sg original returned mask saved before observed
    entry eid event tid old ->
  entry.(SchedState).(isRunning) = true -> kernel_running_idle_ready sg entry ->
  kernel_call_stack_available original entry ->
  sem_pend_clear_status_phase_restore_pre
    (SemPendWaitPhase original mask before observed eid timeout
      (event_pend_state sg entry eid event tid old PendSem timeout))
    environment critical sg returned mask (event_pend_state sg entry eid event tid old PendSem timeout).
Proof.
  intros * Horigin Hrunning Hidle Havailable.
  pose proof (sem_pend_clear_status_phase_wait_restore_pre environment critical sg original returned mask saved
    before observed entry eid event tid old timeout Horigin Hrunning Hidle Havailable) as Hpre.
  pose proof (proj1 (proj2 (proj1 Horigin))) as Hsame.
  destruct Hpre as [Hmask [[Hvalid [Hsource [Hrunning' [Hidle' [Havailable' Hcache]]]]] Hwait]].
  split; [exact Hmask|]. split.
  - split; [exact Hvalid|]. split.
    + apply (proj2 (task_tcb_init_stack_same_call_source_iff returned original _ Hsame)); exact Hsource.
    + split; [exact Hrunning'|]. split; [exact Hidle'|]. split; [|exact Hcache].
      unfold kernel_call_stack_available; rewrite (proj1 (proj2 Hsame)); exact Havailable'.
  - destruct Hwait as [_ Hrest]; exact (conj Hsame Hrest).
Qed.

Lemma sem_pend_clear_status_phase_return_output : forall environment local critical sg call mask checkpoint,
  sem_pend_clear_status_phase_restore_output SemPendReturnPhase environment local critical sg call mask checkpoint |--
  sem_pend_client_fields_restore_output environment local critical sg call mask checkpoint.
Proof.
  intros environment local critical sg call mask checkpoint heap [returned [current [[Hsource Hphase] Howner]]].
  exists returned, current; split; assumption.
Qed.

Lemma sem_pend_clear_status_phase_return_same_postcondition : forall environment local critical sg context call mask
  pevent timeout perr before checkpoint error X,
  sem_pend_client_checkpoint_result environment critical sg context pevent timeout before error checkpoint ->
  kernel_stack_call_same_call call context ->
  sem_pend_client_fields_call_safe environment critical sg context pevent timeout before X ->
  TT ** sem_pend_clear_status_phase_restore_output SemPendReturnPhase environment local critical sg call mask checkpoint **
    perr # UChar |-> error |--
  sem_pend_client_fields_call_post environment critical sg context mask pevent timeout perr before X.
Proof.
  intros * Hcheckpoint Hsame Hsafe.
  sep_apply (sem_pend_clear_status_phase_return_output environment local critical sg call mask checkpoint).
  sep_apply (sem_pend_client_fields_call_post_from_restore environment local critical sg context call mask
    pevent timeout perr before checkpoint error X Hcheckpoint Hsame Hsafe); entailer!.
Qed.

Lemma sem_pend_clear_status_phase_irq_restored_save :
  forall phase environment local critical arch
    (suffix : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg original mask before origin irq_entry handler transfer action
    (prefix : kernel_client_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None original.(os_sched_call_origin)
      before false origin irq_entry)
    selected registers heap restored final_registers final_state after (frame : Assertion),
  let acquired := os_int_exit_installed_state transfer in
  let returned := armv7a_continuation_resumed_call selected original in
  sem_pend_client_source_calls environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    before false origin irq_entry prefix ->
  critical.(critical_region_clients) action ->
  kernel_client_actor action <> Some original.(os_sched_call_invocation) ->
  kernel_client_stops action original.(os_sched_call_invocation) = false ->
  kernel_client_step action sg irq_entry acquired ->
  tmr_task_source_call_receipt environment.(task_stack_call_external) action sg irq_entry acquired ->
  os_int_exit_transfer_source environment.(task_stack_call_external) environment.(task_stack_call_port)
    sg handler irq_entry transfer ->
  selected.(armv7a_continuation_stack) = transfer.(os_int_exit_incoming_stack) ->
  selected.(armv7a_continuation_sp) = transfer.(os_int_exit_incoming_sp) ->
  selected.(armv7a_continuation_fragments) = transfer.(os_int_exit_incoming_fragments) ->
  selected.(armv7a_continuation_call) = Some original ->
  original.(os_sched_call_origin) = RunningInvocation
    transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
    transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration) ->
  selected.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 ->
  registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
  registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
  registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
  interrupt_saved_value mask registers.(kernel_save_r0) ->
  interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
  armv7a_continuation_restore_reads selected heap ->
  (interrupt_platform_running environment.(task_stack_call_platform)
     handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
   os_int_exit_context_resources environment.(task_stack_call_port) handler **
   task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
     selected.(armv7a_continuation_fragments) **
   armv7a_dormant_continuation environment.(task_stack_call_continuations) selected **
   (kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv
      local sg (task_stack_call_active_key returned) acquired ** frame)) heap ->
  armv7a_restore_transition environment.(task_stack_call_continuations) handler selected heap restored ->
  armv7a_save_suffix_transition suffix registers acquired restored final_registers final_state after ->
  sem_pend_clear_status_phase_save_pre phase environment critical sg original mask before ->
  kernel_call_normal_return original before returned acquired ->
  sem_pend_save_rely sg before acquired ->
  final_state = acquired /\ after.(ConAssertion.s_mem) = heap.(ConAssertion.s_mem) /\
  final_registers.(kernel_save_return_word) = Some selected.(armv7a_continuation_lr) /\
  final_registers.(kernel_save_r0) = registers.(kernel_save_r0) /\
  (sem_pend_clear_status_phase_save_output phase environment local critical sg original mask
     final_registers.(kernel_save_r0) before **
   (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) ** frame)) after.
Proof.
  intros phase environment local critical arch suffix sg original mask before origin irq_entry handler
    transfer action prefix selected registers heap restored final_registers final_state after frame
    acquired returned Hprefix Hin Hforeign Hstop Hstep Hreceipt Htransfer
    Hlease Hsp Hfragments Hcall Horigin Hcursor Hcpsr Hr0 Hlr Hsaved Hrestored_saved Hreads Hpre
    Hrestore Hsuffix Hphase_pre Hnormal Hrely.
  destruct (sem_pend_fields_irq_restored_save_resources environment local critical arch suffix sg handler
    selected original acquired registers heap restored final_registers final_state after frame
    Hcall Hcursor Hcpsr Hr0 Hlr Hrestored_saved Hreads Hpre Hrestore Hsuffix)
    as [Hstate [Hmemory [Hreturn [Hvalue Howner]]]].
  pose proof (proj2 (proj1 Hreads)) as Hselected_stack.
  rewrite Hcall in Hselected_stack.
  assert (Hi : returned.(os_sched_call_invocation) = original.(os_sched_call_invocation)) by reflexivity.
  assert (Ho : returned.(os_sched_call_origin) = original.(os_sched_call_origin)) by reflexivity.
  assert (Hstack : returned.(os_sched_call_stack) = original.(os_sched_call_stack)).
  { change (selected.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
    symmetry; exact Hselected_stack. }
  assert (Hreturned : returned.(os_sched_call_origin) = RunningInvocation
      transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
      transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration)).
  { exact Horigin. }
  assert (Hexecution : task_execution_source_step environment.(task_stack_call_external)
      environment.(task_stack_call_port) sg origin irq_entry returned.(os_sched_call_origin) acquired).
  { rewrite Hreturned; eapply TaskExecutionInterruptTransfer; exact Htransfer. }
  pose proof (sem_pend_client_phase_return_last_step environment critical sg original returned before
    origin irq_entry acquired action prefix Hprefix Hin Hforeign Hstop Hstep Hexecution Hreceipt Hnormal) as Hsource.
  pose proof (sem_pend_clear_status_phase_save_output_intro phase environment local critical sg
    original returned mask registers.(kernel_save_r0) before acquired Hphase_pre Hsource Hsaved Hrely) as Hphase.
  rewrite Hstate, Hvalue in Howner.
  assert (Hframe : sem_pend_fields_masked environment local critical sg returned
      registers.(kernel_save_r0) acquired acquired **
      (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
        handler.(os_int_exit_handler_fragments) ** frame) |--
    sem_pend_clear_status_phase_save_output phase environment local critical sg original mask
      registers.(kernel_save_r0) before **
      (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
        handler.(os_int_exit_handler_fragments) ** frame)).
  { sep_apply Hphase; entailer!. }
  split; [exact Hstate|]. split; [exact Hmemory|]. split; [exact Hreturn|].
  split; [exact Hvalue|]. rewrite Hvalue; exact (Hframe after Howner).
Qed.

Lemma sem_pend_clear_status_phase_task_installed_save :
  forall phase environment local critical arch
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (suffix : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg original mask before context outgoing hooked incoming resumed action
    (prefix : kernel_client_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None original.(os_sched_call_origin)
      before false context.(os_sched_call_origin) hooked)
    heap (frame : Assertion),
  let resource := kernel_saved_continuation_entry environment.(task_stack_call_continuations)
    hooked.(TskState) local in
  let acquired := os_sched_install_context context outgoing incoming hooked in
  sem_pend_client_source_calls environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    before false context.(os_sched_call_origin) hooked prefix ->
  critical.(critical_region_clients) action ->
  kernel_client_actor action <> Some original.(os_sched_call_invocation) ->
  kernel_client_stops action original.(os_sched_call_invocation) = false ->
  kernel_client_step action sg hooked acquired ->
  tmr_task_source_call_receipt environment.(task_stack_call_external) action sg hooked acquired ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding environment.(task_stack_call_external)
    context outgoing hooked incoming resumed ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_fields_inv sg hooked **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame)) heap ->
  sem_pend_clear_status_phase_save_pre phase environment critical sg original mask before ->
  exists installed selected,
    sched_install_heap_fragment sg heap installed (task_slot_addr sg incoming.(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    armv7a_continuation_binding selected /\
    selected.(armv7a_continuation_stack) = incoming /\
    selected.(armv7a_continuation_fragments) = resumed /\
    task_current_at acquired incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
    task_stack_live_coverage acquired.(TskState) (Some (task_stack_key incoming)) /\
    (forall registers restored final_registers final_state after,
      selected.(armv7a_continuation_call) = Some original ->
      original.(os_sched_call_origin) = RunningInvocation incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) ->
      selected.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 ->
      registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
      registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
      registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
      interrupt_saved_value mask registers.(kernel_save_r0) ->
      interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
      armv7a_task_restore_transition task_abi context selected installed restored ->
      armv7a_save_suffix_transition suffix registers acquired restored final_registers final_state after ->
      kernel_call_normal_return original before (armv7a_continuation_resumed_call selected original) acquired ->
      sem_pend_save_rely sg before acquired ->
      armv7a_task_restored_source environment.(task_stack_call_external) selected /\
      final_state = acquired /\ after.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
      final_registers.(kernel_save_return_word) = Some selected.(armv7a_continuation_lr) /\
      final_registers.(kernel_save_r0) = registers.(kernel_save_r0) /\
      (sem_pend_clear_status_phase_save_output phase environment local critical sg original mask
         final_registers.(kernel_save_r0) before ** (local selected ** frame)) after).
Proof.
  intros phase environment local critical arch task_abi suffix sg original mask before context outgoing
    hooked incoming resumed action prefix heap frame resource acquired Hprefix Hin Hforeign Hstop
    Hstep Hreceipt Hsaved_stack Hdestination Haddress Hcoverage Hpre Hphase_pre.
  destruct (sem_pend_fields_task_installed_save_resources environment local critical arch task_abi suffix
    sg context outgoing hooked incoming resumed heap frame Hsaved_stack Hdestination Haddress Hcoverage Hpre)
    as [installed [selected [Hinstall [Hreads [Hbinding [Hlease [Hfragments
      [Hcurrent [Hcovered Hrestore]]]]]]]]].
  fold acquired in Hcurrent, Hcovered, Hrestore.
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  split; [exact Hbinding|]. split; [exact Hlease|]. split; [exact Hfragments|].
  split; [exact Hcurrent|]. split; [exact Hcovered|].
  intros registers restored final_registers final_state after Hcall Horigin Hcursor Hcpsr Hr0 Hlr
    Hsaved Hrestored_saved Hactual Hsuffix Hnormal Hrely.
  destruct (Hrestore original registers restored final_registers final_state after Hcall Horigin
    Hcursor Hcpsr Hr0 Hlr Hrestored_saved Hactual Hsuffix)
    as [Hsource [Hstate [Hmemory [Hreturn [Hvalue Howner]]]]].
  pose (returned := armv7a_continuation_resumed_call selected original).
  pose proof (proj2 Hbinding) as Hselected_stack.
  rewrite Hcall in Hselected_stack.
  assert (Hi : returned.(os_sched_call_invocation) = original.(os_sched_call_invocation)) by reflexivity.
  assert (Ho : returned.(os_sched_call_origin) = original.(os_sched_call_origin)) by reflexivity.
  assert (Hstack : returned.(os_sched_call_stack) = original.(os_sched_call_stack)).
  { change (selected.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
    symmetry; exact Hselected_stack. }
  assert (Hreturned : returned.(os_sched_call_origin) = RunningInvocation
      incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration)).
  { exact Horigin. }
  assert (Hexecution : task_execution_source_step environment.(task_stack_call_external)
      environment.(task_stack_call_port) sg context.(os_sched_call_origin) hooked returned.(os_sched_call_origin) acquired).
  { rewrite Hreturned; eapply TaskExecutionSchedulerInstall; eassumption. }
  pose proof (sem_pend_client_phase_return_last_step environment critical sg original returned before
    context.(os_sched_call_origin) hooked acquired action prefix Hprefix Hin Hforeign Hstop Hstep
    Hexecution Hreceipt Hnormal) as Hreturn_source.
  pose proof (sem_pend_clear_status_phase_save_output_intro phase environment local critical sg
    original returned mask registers.(kernel_save_r0) before acquired Hphase_pre Hreturn_source Hsaved Hrely) as Hphase.
  rewrite Hstate, Hvalue in Howner.
  assert (Hframe : sem_pend_fields_masked environment local critical sg returned
      registers.(kernel_save_r0) acquired acquired ** (local selected ** frame) |--
    sem_pend_clear_status_phase_save_output phase environment local critical sg original mask
      registers.(kernel_save_r0) before ** (local selected ** frame)).
  { sep_apply Hphase; entailer!. }
  split; [exact Hsource|]. split; [exact Hstate|]. split; [exact Hmemory|].
  split; [exact Hreturn|]. split; [exact Hvalue|].
  rewrite Hvalue; exact (Hframe after Howner).
Qed.

Lemma sem_pend_clear_status_wait_entry_row_in_range : forall sg entry eid current tid old,
  sem_pend_clear_status_wait_entry sg entry eid current tid old -> 0 <= old.(curPrio) / 8 < 8.
Proof.
  intros * [Hvalid [_ [_ [Hold _]]]].
  pose proof Hvalid as [Hprofile [Htasks _]].
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  destruct Htasks as [_ [_ [_ [_ [_ [_ [_ [Hpriority _]]]]]]]].
  specialize (Hpriority tid old Hold); unfold task_priority_in_range in Hpriority.
  split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia].
Qed.

Lemma sem_pend_clear_status_fields_wait_prefix_split_call : forall sg entry eid current tid old timeout,
  sem_pend_clear_status_wait_entry sg entry eid current tid old ->
  tcb_cell (task_slot_addr sg tid) TCBStat (Some (Z.lor (encode_task_status old.(stat)) 1)) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBDly (Some timeout) **
  sem_pend_fields_prefix_frame sg entry tid old |--
  tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBY (Some (old.(curPrio) / 8)) **
  tcb_cell (task_slot_addr sg tid) TCBBitX (Some (tcb_bit_x_of_prio old.(curPrio))) **
  tcb_cell (task_slot_addr sg tid) TCBBitY (Some (tcb_bit_y_of_prio old.(curPrio))) **
  (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl") + old.(curPrio) / 8 * sizeof(UCHAR))
    # UChar |-> encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8) **
  &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
    # UChar |-> encode_event_wait_grp current.(waitList) entry.(TskState) **
  (sg.(g_OSRdyTbl) + old.(curPrio) / 8 * sizeof(UCHAR))
    # UChar |-> encode_ready_tbl_at_or entry.(SchedState).(readyList) entry.(TskState) (old.(curPrio) / 8) **
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp entry.(SchedState).(readyList) entry.(TskState) **
  sem_pend_fields_wait_call_frame sg entry eid current tid old timeout.
Proof.
  intros * Hentry.
  pose proof (sem_pend_clear_status_wait_entry_row_in_range _ _ _ _ _ _ Hentry) as Hrow.
  destruct Hentry as [Hvalid [_ [_ [Hold [He [Htype [Hnonidle [Hnone [Hmulti [Hflag [Hready Hlayout]]]]]]]]]]].
  unfold sem_pend_fields_prefix_frame.
  sepcon_assoc_change.
  pose proof (sem_pend_tcb_merge_wait_prefix sg tid old timeout) as Hmerge.
  lazymatch type of Hmerge with
  | ?prefix |-- _ =>
      lazymatch goal with
      | |- ?whole |-- _ =>
          lazymatch whole with
          | ?a ** (?b ** (?c ** (?d ** ?frame))) =>
              assert (Hpacked : whole |-- prefix ** frame) by entailer!;
              rewrite Hpacked, Hmerge
          end
      end
  end.
  sepcon_assoc_change.
  sep_apply_l_atomic (event_task_wait_tcb_split (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendSem timeout))).
  unfold sem_pend_sched_without_current, sem_pend_fields_task_sched_frame,
    UCOS2_raw_rep_missing_task_storage_sched_flag.
  sep_apply_l_atomic (sched_rows_split_cell sg entry.(TskState) entry.(SchedState).(readyList)
    (old.(curPrio) / 8) Hrow).
  sep_apply_l_atomic (event_raw_rep_split_eid sg entry.(TskState) entry.(EventState) eid current He).
  unfold used_event_rep.
  sep_apply_l_atomic (event_task_wait_event_split_c_fields sg eid
    (event_image sg entry.(TskState) current) (old.(curPrio) / 8)
    (encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) entry.(TskState)) Hlayout Hrow
    (event_table_image_eq sg entry.(TskState) current (old.(curPrio) / 8) Hrow) eq_refl).
  unfold sem_pend_fields_wait_call_frame, sem_pend_fields_task_sched_event_frame.
  cbn [task_tcb64_image task_prepare_event_wait].
  try rewrite Hnone; cbn [encode_event_link].
  repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
  cbn [task_prepare_event_wait eventPtr curPrio tcb_y_of_prio].
  rewrite Hnone; reflexivity.
Qed.

Lemma sem_pend_clear_status_fields_event_pend_storage_merge : forall sg s eid e tid old kind timeout,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> valid_task_prio sg old.(curPrio) ->
  old.(eventPtr) = None -> old.(eventMultiWaitEvents) = nil -> old.(tcbFlagNode) = 0 ->
  task_non_suspension_bits old.(stat) = 0 ->
  event_type_to_pend_type e.(eventType) = Some kind -> event_wait_resource_unavailable e ->
  (forall m, e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) ->
  let post := event_pend_state sg s eid e tid old kind timeout in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_mark_waiter (event_image sg s.(TskState) e)
      (old.(curPrio) / 8) (encode_event_wait_tbl_at_or e.(waitList) s.(TskState) (old.(curPrio) / 8))
      (encode_event_wait_grp e.(waitList) s.(TskState))
      (Z.shiftl 1 (old.(curPrio) mod 8)) (Z.shiftl 1 (old.(curPrio) / 8))) **
    event_raw_rep_no_eid sg s.(TskState) s.(EventState) eid) **
  sem_pend_fields_task_sched_event_frame sg s |-- UCOS2_fields_inv sg post.
Proof.
  intros sg s eid e tid old kind timeout Hvalid He Hold Hprio Hnull Hmulti Hflagnull
    Hready Hkind Hunavailable Hnotowner post.
  assert (Hsg : valid_stable_glob_vars sg).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile in Hvalid; tauto. }
  assert (Hrow : 0 <= old.(curPrio) / 8 < 8).
  { destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]].
    unfold valid_task_prio in Hprio.
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  assert (Hevent : post.(EventState) =
    update_event_field_raw s.(EventState) eid (event_insert_waiter sg s.(TskState) e tid)).
  { unfold post, event_pend_state, event_wait_state; cbn zeta.
    change (update_event_field_raw s.(EventState) eid
      (event_insert_waiter sg (glob_task_set_usedtask s.(TskState) tid
        (task_set_event_ptr (task_prepare_event_wait old kind timeout) (Some eid))) e tid) =
      update_event_field_raw s.(EventState) eid (event_insert_waiter sg s.(TskState) e tid)).
    rewrite (event_insert_waiter_update_task_eq sg s.(TskState) tid old
      (task_set_event_ptr (task_prepare_event_wait old kind timeout) (Some eid)) e tid Hold eq_refl).
    reflexivity. }
  rewrite (event_insert_waiter_reconstructs_raw_rep
    sg s.(TskState) s.(EventState) eid e tid old Hold Hrow).
  rewrite <- Hevent.
  assert (Hvalid_after : UCOS2_state_inv sg post).
  { apply (event_pend_preserves_validity_from_clear_status sg s eid e tid old kind timeout
      Hvalid He Hold Hprio Hnull Hmulti Hflagnull Hready Hkind Hunavailable Hnotowner). }
  assert (Hindex : event_raw_rep sg s.(TskState) post.(EventState) =
    event_raw_rep sg post.(TskState) post.(EventState)).
  { apply event_raw_rep_change_task_index; apply event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hold|reflexivity]. }
  rewrite Hindex.
  sep_apply_l_atomic (sem_pend_fields_event_pend_preserves_residual sg s eid e tid old kind timeout He).
  fold post; rewrite sem_pend_fields_inv_split_task_sched_event; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_clear_status_fields_wait_call_merge : forall sg entry eid current tid old timeout,
  sem_pend_clear_status_wait_entry sg entry eid current tid old ->
  sem_pend_fields_wait_call_post sg entry eid current tid old timeout |--
  UCOS2_fields_inv sg (event_pend_state sg entry eid current tid old PendSem timeout).
Proof.
  intros * Hentry.
  pose proof (sem_pend_clear_status_wait_entry_row_in_range _ _ _ _ _ _ Hentry) as Hrow.
  destruct Hentry as [Hvalid [Hcount [Hcur [Hold [He [Htype [Hnonidle [Hnone [Hmulti0 [Hflag [Hready Hlayout]]]]]]]]]]].
  pose proof Hvalid as [Hprofile [Htasks [[Hrdy Hmeta] [Hevents _]]]].
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  pose proof Htasks as [_ [_ [_ [_ [_ [_ [Hunique [Hpriorities _]]]]]]]].
  pose proof (Hpriorities tid old Hold) as Hrange.
  assert (Hprio : valid_task_prio sg old.(curPrio))
    by (unfold valid_task_prio, task_priority_in_range in *; lia).
  assert (Hkind : event_type_to_pend_type current.(eventType) = Some PendSem) by (rewrite Htype; reflexivity).
  assert (Hunavailable : event_wait_resource_unavailable current).
  { pose proof Hevents as [_ [_ [_ [_ [Hpayload _]]]]].
    specialize (Hpayload eid current He); unfold event_payload_consistency in Hpayload.
    unfold event_wait_resource_unavailable; rewrite Htype in Hpayload |- *.
    destruct current.(semFields) as [fields|] eqn:Hfields; [|contradiction].
    unfold encode_event_cnt_value in Hcount; rewrite Htype, Hfields in Hcount; exact Hcount. }
  assert (Hnotowner : forall m, current.(eventType) = OS_EVENT_TYPE_MUTEX ->
    current.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) by (intros; congruence).
  pose proof (sched_ready_in_range_implies_structure sg entry.(TskState) entry.(SchedState) Hrdy) as Hstructure.
  unfold sem_pend_fields_wait_call_post, sem_pend_fields_wait_call_frame, event_task_wait_post.
  pose proof (event_task_wait_tcb_merge_event_ptr (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendSem timeout)) (event_addr sg eid)) as Htcb.
  change (tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some (event_addr sg eid)) **
    tcb_cell (task_slot_addr sg tid) TCBY (Some (old.(curPrio) / 8)) **
    tcb_cell (task_slot_addr sg tid) TCBBitX (Some (tcb_bit_x_of_prio old.(curPrio))) **
    tcb_cell (task_slot_addr sg tid) TCBBitY (Some (tcb_bit_y_of_prio old.(curPrio))) **
    event_task_wait_tcb_rest (task_slot_addr sg tid)
      (task_tcb64_image sg (task_prepare_event_wait old PendSem timeout)) |--
    tcb64_storage_rep (task_slot_addr sg tid)
      (tcb_write (task_tcb64_image sg (task_prepare_event_wait old PendSem timeout))
        TCBEventPtr (Some (event_addr sg eid)))) in Htcb.
  cbn [tcb_cell tcb_field_address] in Htcb.
  unfold tcb_y_of_prio in Htcb.
  sepcon_assoc_change.
  sep_apply_l_atomic Htcb.
  assert (Himage : tcb_write (task_tcb64_image sg (task_prepare_event_wait old PendSem timeout))
    TCBEventPtr (Some (event_addr sg eid)) =
    task_tcb64_image sg (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)))
    by (symmetry; apply task_set_event_ptr_image_eq).
  rewrite Himage.
  sep_apply_l_atomic (sem_post_task_storage_merge sg entry.(TskState) tid
    (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)) Hmulti Hprofiling).
  sep_apply_l_atomic (event_task_wait_event_merge_c_fields sg eid (event_image sg entry.(TskState) current)
    (old.(curPrio) / 8)
    (encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) entry.(TskState))
    (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio)) Hlayout Hrow).
  pose proof (event_task_wait_ready_merge_removed_task sg entry.(TskState) entry.(SchedState)
    tid old Hsg Hunique Hold Hrange Hstructure Hrow) as Hready_merge.
  lazymatch type of Hready_merge with
  | ?ready_fields |-- _ =>
      lazymatch goal with
      | |- ?whole |-- _ =>
          lazymatch whole with
          | ?event ** (?tasks ** (?current_cell ** (?row ** (?group ** (?missing ** ?frame))))) =>
              assert (Hpacked_ready : whole |--
                ready_fields ** (event ** (tasks ** (current_cell ** frame)))) by entailer!;
              rewrite Hpacked_ready, Hready_merge
          end
      end
  end.
  sepcon_assoc_change.
  assert (Hindex : forall s, sched_raw_rep sg entry.(TskState) s =
    sched_raw_rep sg (glob_task_set_usedtask entry.(TskState) tid
      (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid))) s).
  { intro s; apply sched_raw_rep_priority_ext; intros slot Hin.
    change (option_map curPrio (entry.(TskState).(inUsedTaskStates) slot) =
      option_map curPrio (if Z.eqb slot tid then
        Some (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid))
        else entry.(TskState).(inUsedTaskStates) slot)).
    destruct (Z.eqb slot tid) eqn:E;
      [apply Z.eqb_eq in E; subst slot; rewrite Hold|]; reflexivity. }
  pose proof (sem_pend_clear_status_fields_event_pend_storage_merge sg entry eid current tid old PendSem timeout
    Hvalid He Hold Hprio Hnone Hmulti0 Hflag Hready Hkind Hunavailable Hnotowner) as Hmerge_storage.
  let merge_type := type of Hmerge_storage in
  let merge_type := eval cbv zeta in merge_type in
  lazymatch merge_type with
  | ?pre |-- _ =>
      lazymatch goal with
      | |- ?left |-- _ =>
          assert (Hresources : left |-- pre);
          [ | intros heap Hheap; exact (Hmerge_storage heap (Hresources heap Hheap)) ]
      end
  end.
  cbn [event_pend_state event_wait_state replace_SchedS replace_EventS replace_TskS TskState SchedState].
  rewrite <- Hindex; unfold sched_raw_rep, sched_physical_rep.
  cbn [sched_remove_ready_task curSchedPrio highRdyPrio curTaskID highRdyTid ctxSwCtr isRunning].
  try rewrite Hcur; cbn [encode_task_link].
  repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
  unfold sched_remove_ready_task, tcb_bit_x_of_prio, tcb_bit_y_of_prio.
  cbn; rewrite Hcur; cbn [encode_task_link]; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_clear_status_fields_wait_call_continuation_merge_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local
  critical sg active context saved acquired entry eid current tid old timeout,
  sem_pend_clear_status_wait_entry sg entry eid current tid old ->
  kernel_call_task_source context entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  task_stack_live_coverage entry.(TskState) active ->
  critical_region_masked platform critical sg context.(os_sched_call_invocation)
    context.(os_sched_call_origin) saved acquired ** os_sched_context_resources external context **
  sem_pend_fields_wait_call_post sg entry eid current tid old timeout ** unmap_table_rep sg **
  store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
    entry.(TskState).(parkedTaskStacks) |--
  coq_prop (let waiting := event_pend_state sg entry eid current tid old PendSem timeout in
    UCOS2_state_inv sg waiting /\ kernel_call_task_source context waiting /\
    sched_current_consistency waiting.(TskState) waiting.(SchedState)) &&
  kernel_continuation_call_masked abi kernel_program_fields_inv local critical sg active context saved acquired
    (event_pend_state sg entry eid current tid old PendSem timeout).
Proof.
  intros external platform port abi local critical sg active context saved acquired entry
    eid current tid old timeout Hentry Hsource Hcache Hcoverage.
  pose proof Hentry as [_ [_ [_ [Hold _]]]].
  set (waiting := event_pend_state sg entry eid current tid old PendSem timeout).
  assert (Hcovered : task_stack_live_coverage waiting.(TskState) active).
  { apply (sem_pend_fields_task_update_preserves_coverage entry.(TskState) active tid old
      (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid))
      Hold eq_refl Hcoverage). }
  pose proof (sem_pend_clear_status_wait_preserves_call_source sg context entry eid current tid old timeout
    Hentry Hsource Hcache) as Hwaiting.
  sep_apply_l_atomic (sem_pend_clear_status_fields_wait_call_merge sg entry eid current tid old timeout Hentry).
  sep_apply_l_atomic (sem_pend_fields_task_update_continuations external platform port abi local
    entry.(TskState) tid old (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid))
    Hold eq_refl eq_refl).
  unfold kernel_continuation_call_masked, kernel_continuation_inv.
  rewrite kernel_program_fields_inv_split_unmap; fold waiting; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.


Lemma sem_pend_clear_status_call_entry_wait_entry : forall sg call entry eid current,
  sem_pend_clear_status_call_entry sg call entry -> mutex_query_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_SEM -> encode_event_cnt_value current = 0 ->
  event_object_layout_prop sg eid ->
  exists node,
    sem_pend_clear_status_wait_entry sg entry eid current call.(os_sched_call_stack).(stackLeaseSlot) node /\
    call.(os_sched_call_origin) = RunningInvocation call.(os_sched_call_stack).(stackLeaseSlot) node.(taskGeneration) /\
    kernel_call_task_source call entry /\ sched_current_consistency entry.(TskState) entry.(SchedState).
Proof.
  intros sg call entry eid current [Hcontext [Hfields Hclear]] Hlookup Htype Hzero Hlayout.
  destruct Hcontext as [Hvalid [Hsource [Hrunning [Hidle [Havailable Hcache]]]]].
  destruct Hfields as [_ [[nonidle [Hnonidle [Hgen Hprio]]] [node [Hnode Hnone]]]].
  destruct (kernel_call_task_source_current_at call entry Hsource) as [Hcurrent [found [Hfound Hgeneration]]].
  assert (found = node) by congruence; subst found.
  assert (nonidle = node) by congruence; subst nonidle.
  destruct Hnone as [Hevent [Hmulti Hflag]].
  exists node; split.
  - unfold sem_pend_clear_status_wait_entry.
    exact (conj Hvalid (conj Hzero (conj Hcurrent (conj Hnode (conj Hlookup (conj Htype
      (conj Hprio (conj Hevent (conj Hmulti (conj Hflag (conj (Hclear node Hnode) Hlayout))))))))))).
  - split; [rewrite Hgeneration; exact (proj1 Hsource)|exact (conj Hsource Hcache)].
Qed.

Lemma sem_pend_clear_status_fields_acquired_wait_prefix : forall sg context entry eid current,
  sem_pend_clear_status_call_entry sg context entry ->
  UCOS2_state_inv sg entry -> mutex_query_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_SEM ->
  encode_event_cnt_value current = 0 -> event_object_layout_prop sg eid ->
  (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value current **
    sem_pend_fields_count_frame sg entry eid current |--
  EX node,
    coq_prop (sem_pend_clear_status_wait_entry sg entry eid current context.(os_sched_call_stack).(stackLeaseSlot) node /\
      context.(os_sched_call_origin) = RunningInvocation
        context.(os_sched_call_stack).(stackLeaseSlot) node.(taskGeneration) /\
      kernel_call_task_source context entry /\
      sched_current_consistency entry.(TskState) entry.(SchedState) /\
      0 <= encode_task_status node.(stat) <= 255) &&
    (sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot) **
     tcb_cell (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
       TCBStat (Some (encode_task_status node.(stat))) **
     tcb_cell (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
       TCBStatPend (Some (encode_pend_status node.(statPend))) **
     tcb_cell (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) TCBDly (Some node.(dly)) **
     sem_pend_fields_prefix_frame sg entry context.(os_sched_call_stack).(stackLeaseSlot) node).
Proof.
  intros sg context entry eid current Hstage Hvalid Hlookup Htype Hzero Hlayout.
  destruct (sem_pend_clear_status_call_entry_wait_entry sg context entry eid current
    Hstage Hlookup Htype Hzero Hlayout) as [node [Hentry [Horigin [Hsource Hcache]]]].
  pose proof Hentry as [_ [_ [Hcurrent [Hnode _]]]].
  sep_apply_l_atomic (sem_pend_fields_count_merge_unchanged sg entry eid current Hvalid Hlookup Htype).
  sep_apply_l_atomic (sem_pend_fields_wait_prefix_split sg entry context.(os_sched_call_stack).(stackLeaseSlot)
    node Hvalid Hcurrent Hnode).
  pose proof (encode_task_status_in_range node.(stat)) as Hrange.
  assert (Hbyte_range : 0 <= encode_task_status node.(stat) <= 255).
  { unfold task.encode_task_status; lia. }
  Exists node; entailer!; try (match goal with
    | |- ?left |-- coq_prop ?fact && ?right =>
        let Hspatial := fresh "Hspatial" in
        assert (Hspatial : left |-- right) by entailer!;
        let heap := fresh "heap" in let Hheap := fresh "Hheap" in
        intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
    end).
Qed.

