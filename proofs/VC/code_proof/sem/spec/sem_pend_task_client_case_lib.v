Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_retirement.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.kernel_runtime_inv.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_history_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_pend_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_return_fields_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_multi_pointer_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_sched_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_clear_status_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Import TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Only this live invocation's slot and generation are retained. Other
    tasks may be deleted by the original complete Scheduler source. *)
Definition sem_pend_task_client_multi_zero call state : Prop :=
  exists node, state.(TskState).(inUsedTaskStates)
      call.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
    node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) /\
    node.(tcbEventMultiPtr) = 0.

Lemma sem_pend_task_client_entry_multi_zero : forall sg call state,
  tmr_task_client_pend_entry sg call state -> sem_pend_task_client_multi_zero call state.
Proof.
  intros sg call state [[Hsource [Hrunning [node [Hready [Hg Hrest]]]]] [Hidle [Havailable Hzero]]].
  exists node; exact (conj (proj1 Hready) (conj Hg (Hzero node (proj1 Hready)))).
Qed.

Lemma sem_pend_task_client_multi_zero_same_call : forall original returned state,
  kernel_stack_call_same_call returned original ->
  sem_pend_task_client_multi_zero original state -> sem_pend_task_client_multi_zero returned state.
Proof.
  intros original returned state Hsame Hzero.
  unfold sem_pend_task_client_multi_zero in *; rewrite (proj2 (proj2 Hsame)); exact Hzero.
Qed.

Lemma sem_pend_task_client_transport_multi_zero : forall call before after,
  tmr_task_multi_pointer_transport before after ->
  sem_pend_task_client_multi_zero call before -> sem_pend_task_client_multi_zero call after.
Proof.
  intros call before after Htransport [old [Hold [Hg Hzero]]].
  destruct (Htransport _ old Hold) as [node [Hnode [Hg' Hptr]]].
  exists node; split; [exact Hnode|]; split; congruence.
Qed.

Lemma sem_pend_task_client_return_multi_zero : forall environment critical sg call before returned after observer,
  sem_pend_client_return_source environment critical sg call before returned after ->
  UCOS2_state_inv sg before -> kernel_call_task_source call before ->
  kernel_stack_call_same_call call observer ->
  sem_pend_task_client_multi_zero observer before ->
  sem_pend_task_client_multi_zero observer after.
Proof.
  intros * Hsource Hvalid Htask Hsame Hzero.
  pose proof (sem_pend_task_client_multi_zero_same_call observer call before Hsame Hzero)
    as [old [Hold [Hgen Hpointer]]].
  destruct (tmr_task_client_return_multi_zero environment critical sg call before returned after old
    Hsource Hvalid Htask Hold Hgen Hpointer) as [node [Hnode [Hg [Hptr Hall]]]].
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hsource) as Hreturned.
  unfold sem_pend_task_client_multi_zero.
  rewrite (proj2 (proj2 Hreturned)), (proj2 (proj2 Hsame)) in Hnode, Hg.
  exists node; exact (conj Hnode (conj Hg Hptr)).
Qed.

Lemma sem_pend_task_client_scheduler_multi_zero :
  forall environment critical sg entry call returned current
    (body : SchedulerPhaseCandidate.os_sched_task_body_source environment critical sg entry call returned current),
  sem_pend_sched_body_receipt environment critical sg entry call returned current body ->
  task_sw_hook_source_binding environment.(task_stack_call_external) ->
  task_in_range sg entry.(TskState) -> kernel_call_task_source call entry ->
  kernel_stack_call_same_call returned call -> kernel_call_task_source returned current ->
  sem_pend_task_client_multi_zero call entry -> sem_pend_task_client_multi_zero returned current.
Proof.
  intros environment critical sg entry call returned current body Hreceipt Hhook Htasks Hsource Hsame Hreturned
    [old [Hold [Hg Hzero]]].
  assert (Hlife : task_observer_lifetime entry.(TskState) call.(os_sched_call_invocation)
    (RunningInvocation call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration))).
  { rewrite <- (proj1 Hsource); apply task_observer_lifetime_from_active with sg;
      [exact Htasks|exact (proj1 (proj2 Hsource))]. }
  assert (Hactive : task_invocation_active current.(TskState) call.(os_sched_call_invocation)
    (RunningInvocation call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration))).
  { rewrite <- (proj1 Hsource); eapply kernel_call_same_return_observer_active; eassumption. }
  destruct (sem_pend_sched_body_multi_pointer environment critical sg entry call returned current body
    Hreceipt Hhook _ old _ Hlife Hactive Hold) as [node [Hnode [Hg' Hptr]]].
  unfold sem_pend_task_client_multi_zero; rewrite (proj2 (proj2 Hsame)).
  exists node; split; [exact Hnode|]; split; congruence.
Qed.

Lemma sem_pend_task_client_resume_local_fields : forall sg original returned resumed tid old,
  sem_pend_task_client_multi_zero original resumed -> kernel_stack_call_same_call returned original ->
  sem_pend_client_phase_context sg returned resumed -> flag_pend_non_idle_at sg original resumed ->
  resumed.(SchedState).(curTaskID) = Some tid -> resumed.(TskState).(inUsedTaskStates) tid = Some old ->
  old.(tcbEventMultiPtr) = 0 /\ old.(curPrio) <> sg.(osLowestPrio).
Proof.
  intros sg original returned resumed tid old [zero_node [Hzero [Hg Hptr]]]
    Hsame [_ [Hsource Hrest]] [nonidle [Hnonidle [Hg' Hp]]] Hcurrent Hold.
  destruct (kernel_call_task_source_current_at returned resumed Hsource) as [Hcurrent' Hnode].
  assert (Htid : tid = original.(os_sched_call_stack).(stackLeaseSlot)).
  { rewrite (proj2 (proj2 Hsame)) in Hcurrent'; congruence. }
  subst tid; assert (zero_node = old) by congruence; assert (nonidle = old) by congruence.
  subst zero_node nonidle; exact (conj Hptr Hp).
Qed.

(** Pack the existing wait-reassembly result with the enabled fact derived
    from the actual acquire observation and the actual event_pend update. *)
Lemma sem_pend_task_client_wait_sched_entry : forall environment critical sg original mask initial observed
  eid timeout waiting call current,
  sem_pend_clear_status_phase_restore_pre
    (SemPendWaitPhase original mask initial observed eid timeout waiting)
    environment critical sg call mask current ->
  os_sched_selection_enabled current = true ->
  flag_pend_non_idle_at sg original current -> sem_pend_task_client_multi_zero original current ->
  sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting call current.
Proof.
  intros environment critical sg original mask initial observed eid timeout waiting call current
    [_ [Hcontext Hwait]] Henabled Hnonidle Hzero.
  exact (conj Hcontext (conj Hwait (conj Henabled (conj Hnonidle Hzero)))).
Qed.

Lemma sem_pend_task_client_sched_input_same_call : forall environment local critical sg original mask initial
  observed eid timeout waiting call current,
  sem_pend_client_sched_input environment local critical sg original mask initial observed eid timeout waiting
    call current |--
  coq_prop (kernel_stack_call_same_call call original) &&
  sem_pend_client_sched_input environment local critical sg original mask initial observed eid timeout waiting
    call current.
Proof.
  intros environment local critical sg original mask initial observed eid timeout waiting call current heap
    [Hentry Hclosed].
  split; [exact (proj1 (proj1 (proj2 Hentry)))|exact (conj Hentry Hclosed)].
Qed.

(** Open the one actual returned/current/local packet and feed the existing
    second-Save precondition. The caller's X remains in the surrounding frame. *)
Lemma sem_pend_task_client_sched_output_second_save : forall environment critical sg original mask initial
  observed eid timeout waiting call before,
  kernel_stack_call_same_call call original ->
  sem_pend_client_sched_output environment critical sg original mask initial observed eid timeout waiting call before |--
  EX returned current next_local,
    coq_prop (sem_pend_task_client_multi_zero original current /\ flag_pend_non_idle_at sg original current /\
      kernel_stack_call_same_call returned original /\ sem_pend_client_phase_context sg returned current /\
      UCOS2_state_inv sg current) &&
    sem_pend_clear_status_phase_save_input (SemPendWaitPhase original mask initial observed eid timeout waiting)
      environment next_local critical sg returned mask current.
Proof.
  intros environment critical sg original mask initial observed eid timeout waiting call before Hsame heap
    [returned [current [next_local [[Hreturned [Hcontrol [Hnonidle Hzero]]] [Hpre Hclosed]]]]].
  assert (Hsame_original : kernel_stack_call_same_call returned original).
  { unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence. }
  pose proof (proj1 Hpre) as Hcontext.
  exists returned, current, next_local; split.
  - exact (conj Hzero (conj Hnonidle (conj Hsame_original (conj Hcontext (proj1 Hcontext))))).
  - exact (conj Hpre Hclosed).
Qed.
