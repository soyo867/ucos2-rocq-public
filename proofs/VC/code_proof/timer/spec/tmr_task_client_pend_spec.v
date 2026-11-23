Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare safeexec_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.kernel_runtime_inv.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_program_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_restore_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_callback_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_unlock_fields_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_scan_unlock_entry_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_return_fields_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This is the existing Timer task's actual entry observation. It neither
    assumes a successful Pend nor excludes NULL or early-error returns.
    The generic Sem contract remains separate. *)
Definition tmr_task_client_pend_entry sg call state : Prop :=
  sem_pend_task_call_stage sg call state /\ kernel_running_idle_ready sg state /\
  kernel_call_stack_available call state /\
  forall node, state.(TskState).(inUsedTaskStates)
    call.(os_sched_call_stack).(stackLeaseSlot) = Some node -> node.(tcbEventMultiPtr) = 0.

Lemma tmr_task_client_pend_entry_from_unlock : forall sg call state,
  tmr_task_unlock_entry sg call state -> os_sched_task_current_ready call state ->
  tmr_task_client_pend_entry sg call state.
Proof.
  intros sg call state [Hsource [Havailable [Hrunning [Hcache [Hidle Hclear]]]]] Hready.
  split.
  - eapply tmr_task_fields_caller_clear_pend_stage; eassumption.
  - split; [intros _; exact Hidle|]. split; [exact Havailable|].
    intros node Hnode; destruct (Hclear node Hnode) as [_ [[_ [_ Hpointer]] _]].
    exact Hpointer.
Qed.

Lemma tmr_task_client_pend_entry_unlock : forall sg call state,
  tmr_task_client_pend_entry sg call state -> tmr_task_unlock_entry sg call state.
Proof.
  intros sg call state [Hstage [Hidle [Havailable Hzero]]].
  eapply (tmr_task_pend_return_unlock_entry sg call state call state).
  - exact Havailable.
  - apply kernel_call_normal_return_refl.
  - exact Hstage.
  - exact Hidle.
  - exact Hzero.
Qed.

Lemma tmr_task_client_pend_entry_from_restore : forall environment critical sg call checkpoint returned current,
  UCOS2_state_inv sg checkpoint -> tmr_task_client_pend_entry sg call checkpoint ->
  sem_pend_client_return_source environment critical sg call checkpoint returned current ->
  sem_pend_client_task_return_observation sg call checkpoint returned current ->
  tmr_task_client_pend_entry sg returned current.
Proof.
  intros environment critical sg call checkpoint returned current Hvalid
    [Hstage [Hidle [Havailable Hzero]]] Hsource [Hnormal [Hstage' [Hidle' Havailable']]].
  pose proof Hstage as [_ [_ [old [Hold [Hgeneration Hrest]]]]].
  destruct (tmr_task_client_return_multi_zero environment critical sg call checkpoint returned current old
    Hsource Hvalid (proj1 Hstage) (proj1 Hold) Hgeneration (Hzero old (proj1 Hold)))
    as [node [Hnode [Hgen [Hpointer Hall]]]].
  exact (conj Hstage' (conj Hidle' (conj Havailable' Hall))).
Qed.

Definition tmr_task_client_pend_pre environment local critical sg call mask pevent timeout perr
  before eid observed X : Assertion :=
  coq_prop (sem_pend_fields_call_domain environment critical sg call pevent before eid observed /\
    tmr_task_client_pend_entry sg call before /\
    sem_pend_client_fields_call_safe environment critical sg call pevent timeout before X) &&
  (sem_pend_error_cell perr ** sem_pend_fields_closed environment local sg call mask before).

Definition tmr_task_client_pend_post environment critical sg call mask pevent timeout perr before X : Assertion :=
  EX returned current next_local error,
    coq_prop (sem_pend_client_runtime_program environment critical sg call pevent timeout before error current /\
      safeExec (LastSeen current) (StateRelMonad.ret error) X /\
      kernel_stack_call_same_call returned call /\
      tmr_task_client_pend_entry sg returned current) **
    (perr # UChar |-> error ** sem_pend_fields_closed environment next_local sg returned mask current).

(** This is consumed only after the real ordered precritical tests. *)
Lemma tmr_task_client_pend_acquire_pre : forall environment critical sg call mask pevent before eid observed,
  UCOS2_state_inv sg before ->
  sem_pend_fields_call_domain environment critical sg call pevent before eid observed ->
  tmr_task_client_pend_entry sg call before -> pevent <> 0 ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  sem_pend_client_phase_save_pre (SemPendAcquirePhase pevent eid observed)
    environment critical sg call mask before.
Proof.
  intros environment critical sg call mask pevent before eid observed Hvalid
    [_ [_ [Hinput Hrest]]] [Hstage [Hidle [Havailable Hzero]]] Hnonzero Hcontext.
  split.
  - eapply sem_pend_client_phase_context_from_task_stage; eassumption.
  - exact (conj Hinput (conj Hnonzero (conj Hcontext Hstage))).
Qed.

Lemma tmr_task_client_pend_post_from_result : forall environment local critical sg call returned mask
  pevent timeout perr before current error X,
  sem_pend_client_runtime_program environment critical sg call pevent timeout before error current ->
  sem_pend_client_fields_call_safe environment critical sg call pevent timeout before X ->
  kernel_stack_call_same_call returned call -> tmr_task_client_pend_entry sg returned current ->
  TT ** perr # UChar |-> error ** sem_pend_fields_closed environment local sg returned mask current |--
  tmr_task_client_pend_post environment critical sg call mask pevent timeout perr before X.
Proof.
  intros * Hresult Hsafe Hsame Hentry.
  pose proof (sem_query_safe_return _ _ _ _ _ Hresult Hsafe) as Hreturn.
  unfold tmr_task_client_pend_post; Exists returned current local error; entailer!;
    intros heap Hheap; exact (conj Hresult (conj Hreturn (conj Hsame Hentry))).
Qed.

Lemma tmr_task_client_pend_post_null : forall environment local critical sg call mask timeout perr before X,
  sem_pend_client_fields_call_safe environment critical sg call 0 timeout before X ->
  tmr_task_client_pend_entry sg call before ->
  TT ** perr # UChar |-> 4 ** sem_pend_fields_closed environment local sg call mask before |--
  tmr_task_client_pend_post environment critical sg call mask 0 timeout perr before X.
Proof.
  intros * Hsafe Hentry; apply tmr_task_client_pend_post_from_result.
  - apply sem_pend_client_program_null.
  - exact Hsafe.
  - unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call; auto.
  - exact Hentry.
Qed.

Lemma tmr_task_client_pend_post_context_error : forall environment local critical sg call mask
  pevent timeout perr before eid observed code X,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = Some code ->
  sem_pend_client_fields_call_safe environment critical sg call pevent timeout before X ->
  tmr_task_client_pend_entry sg call before ->
  TT ** perr # UChar |-> encode_os_err_code code **
    sem_pend_fields_closed environment local sg call mask before |--
  tmr_task_client_pend_post environment critical sg call mask pevent timeout perr before X.
Proof.
  intros * Hnonzero Haddr Hid Hslot Herror Hsafe Hentry.
  apply tmr_task_client_pend_post_from_result.
  - eapply sem_pend_client_program_context_error; eassumption.
  - exact Hsafe.
  - unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call; auto.
  - exact Hentry.
Qed.

(** The phase result is opened once. Its actual returned descriptor,
    state, local family and error are retained in the same result packet.
    Checkpoint zero must be established by the real count/wait/cleanup
    path before this lemma is used; it is not inferred from cfgMulti. *)
Lemma tmr_task_client_pend_post_from_restore : forall environment local critical sg context call mask
  pevent timeout perr before checkpoint error X,
  UCOS2_state_inv sg checkpoint -> tmr_task_client_pend_entry sg call checkpoint ->
  sem_pend_client_checkpoint_result environment critical sg context pevent timeout before error checkpoint ->
  kernel_stack_call_same_call call context ->
  sem_pend_client_fields_call_safe environment critical sg context pevent timeout before X ->
  TT ** sem_pend_client_phase_restore_output SemPendReturnPhase environment local critical sg call mask checkpoint **
    perr # UChar |-> error |--
  tmr_task_client_pend_post environment critical sg context mask pevent timeout perr before X.
Proof.
  intros * Hvalid Hentry Hcheckpoint Hcall Hsafe.
  unfold sem_pend_client_phase_restore_output; Intros returned current.
  assert (Hsource : sem_pend_client_return_source environment critical sg call checkpoint returned current) by tauto.
  assert (Hphase : sem_pend_client_task_return_observation sg call checkpoint returned current) by tauto.
  pose proof (tmr_task_client_pend_entry_from_restore environment critical sg call checkpoint returned current
    Hvalid Hentry Hsource Hphase) as Hafter.
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hsource) as Hreturned.
  assert (Hsame : kernel_stack_call_same_call returned context).
  { unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence. }
  pose proof (sem_pend_client_program_restore environment critical sg context call returned
    pevent timeout before checkpoint error current Hcheckpoint Hcall Hsource) as Hresult.
  pose proof (sem_query_safe_return _ _ _ _ _ Hresult Hsafe) as Hreturn.
  unfold tmr_task_client_pend_post; Exists returned current local error; entailer!;
    intros heap Hheap; exact (conj Hresult (conj Hreturn (conj Hsame Hafter))).
Qed.

Lemma tmr_task_client_pend_post_forget_entry : forall environment critical sg call mask
  pevent timeout perr before X,
  tmr_task_client_pend_post environment critical sg call mask pevent timeout perr before X |--
  sem_pend_client_fields_call_post environment critical sg call mask pevent timeout perr before X.
Proof.
  intros; unfold tmr_task_client_pend_post, sem_pend_client_fields_call_post.
  Intros returned current local error; Exists returned current local error; entailer!.
Qed.
