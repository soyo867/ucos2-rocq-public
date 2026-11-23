Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare safeexec_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.kernel_runtime_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.mutex_query_spec Ucos2Verify.lib.sem.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_program_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_clear_status_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_clear_status_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_acquire_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_client_annotation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_callback_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_unlock_fields_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_return_fields_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_callback_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The six established caller facts are retained without a ready-list
    premise. Status excludes pending bits and permits suspension. *)
Definition tmr_task_client_clear_status_pend_entry sg call state : Prop :=
  tmr_task_unlock_entry sg call state /\ tmr_task_caller_wait_status_clear call state.

Lemma tmr_task_client_clear_status_pend_status_iff : forall call state,
  tmr_task_caller_wait_status_clear call state <-> sem_pend_caller_status_clear call state.
Proof. intros; reflexivity. Qed.

Definition tmr_task_client_clear_status_pend_domain critical sg call pevent before eid observed : Prop :=
  sem_pend_profile sg /\ kernel_tcb_stack_field_layout sg /\
  sem_pend_call_input critical sg call.(os_sched_call_invocation) pevent before eid observed.

(** The C declaration additionally consumes its ordered physical address
    guard, derived from the actual input and Task global addresses. No old
    observed-admission or future ready-state quantifier is imported. *)
Definition tmr_task_client_clear_status_pend_pre environment local critical sg call mask pevent timeout perr
  before eid observed X : Assertion :=
  coq_prop (tmr_task_client_clear_status_pend_domain critical sg call pevent before eid observed /\
    tmr_task_client_clear_status_pend_entry sg call before /\
    sem_pend_client_fields_call_safe environment critical sg call pevent timeout before X) &&
  (sem_pend_error_cell perr ** sem_pend_fields_closed environment local sg call mask before).

Definition tmr_task_client_clear_status_pend_post environment critical sg call mask pevent timeout perr before X : Assertion :=
  EX returned current next_local error,
    coq_prop (sem_pend_client_runtime_program environment critical sg call pevent timeout before error current /\
      safeExec (LastSeen current) (StateRelMonad.ret error) X /\
      kernel_stack_call_same_call returned call /\
      tmr_task_client_clear_status_pend_entry sg returned current) **
    (perr # UChar |-> error ** sem_pend_fields_closed environment next_local sg returned mask current).

Lemma tmr_task_client_clear_status_pend_entry_sem : forall sg call state,
  UCOS2_state_inv sg state -> tmr_task_client_clear_status_pend_entry sg call state ->
  sem_pend_clear_status_call_entry sg call state.
Proof.
  intros sg call state Hvalid [[Hsource [Havailable [Hrunning [Hcache [Hidle Hclear]]]]] Hstatus].
  destruct (kernel_call_task_source_current_at call state Hsource) as [Hcurrent [old [Hold Hgeneration]]].
  destruct (Hclear old Hold) as [Hnonidle [[Hevent [Hmulti Hpointer]] Hflag]].
  split.
  - exact (conj Hvalid (conj Hsource (conj Hrunning (conj (fun _ => Hidle) (conj Havailable Hcache))))).
  - split.
    + split; [exact Hrunning|]. split.
      * exists old; exact (conj Hold (conj Hgeneration Hnonidle)).
      * exists old; exact (conj Hold (conj Hevent (conj Hmulti Hflag))).
    + exact Hstatus.
Qed.

Lemma tmr_task_client_clear_status_pend_entry_from_sem : forall sg call state,
  sem_pend_clear_status_call_entry sg call state ->
  (forall node, state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
    node.(tcbEventMultiPtr) = 0) ->
  tmr_task_client_clear_status_pend_entry sg call state.
Proof.
  intros sg call state [[Hvalid [Hsource [Hrunning [Hidle [Havailable Hcache]]]]]
    [[_ [[old [Hold [Hgeneration Hnonidle]]] [node [Hnode [Hevent [Hmulti Hflag]]]]]] Hstatus]] Hzero.
  assert (node = old) by congruence; subst node.
  split; [|exact Hstatus].
  split; [exact Hsource|]. split; [exact Havailable|].
  split; [exact Hrunning|]. split; [exact Hcache|].
  split; [exact (Hidle Hrunning)|].
  intros actual Hactual; assert (actual = old) by congruence; subst actual.
  exact (conj Hnonidle (conj (conj Hevent (conj Hmulti (Hzero old Hold))) Hflag)).
Qed.

Lemma tmr_task_client_clear_status_pend_entry_return : forall environment critical sg call before returned after,
  UCOS2_state_inv sg before -> tmr_task_client_clear_status_pend_entry sg call before ->
  sem_pend_client_return_source environment critical sg call before returned after ->
  tmr_task_client_clear_status_pend_entry sg returned after.
Proof.
  intros * Hvalid Hentry Hreturn.
  pose proof (tmr_task_client_clear_status_pend_entry_sem _ _ _ Hvalid Hentry) as Hsem.
  pose proof (sem_pend_clear_status_call_entry_return _ _ _ _ _ _ _ Hreturn Hsem) as Hsem'.
  destruct Hentry as [[Hsource [Havailable [Hrunning [Hcache [Hidle Hclear]]]]] Hstatus].
  destruct (kernel_call_task_source_current_at call before Hsource) as [Hcurrent [old [Hold Hgeneration]]].
  destruct (Hclear old Hold) as [Hnonidle [[Hevent [Hmulti Hpointer]] Hflag]].
  destruct (tmr_task_client_return_multi_zero environment critical sg call before returned after old
    Hreturn Hvalid Hsource Hold Hgeneration Hpointer) as [node [Hnode [Hgen [Hzero Hall]]]].
  apply tmr_task_client_clear_status_pend_entry_from_sem; assumption.
Qed.

Lemma tmr_task_client_clear_status_pend_acquire_pre : forall environment critical sg call mask pevent before eid observed,
  UCOS2_state_inv sg before ->
  tmr_task_client_clear_status_pend_domain critical sg call pevent before eid observed ->
  tmr_task_client_clear_status_pend_entry sg call before -> pevent <> 0 ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  sem_pend_clear_status_phase_save_pre (SemPendAcquirePhase pevent eid observed)
    environment critical sg call mask before.
Proof.
  intros * Hvalid [_ [_ Hinput]] Hentry Hnonnull Hguard.
  destruct (tmr_task_client_clear_status_pend_entry_sem _ _ _ Hvalid Hentry) as [Hcontext [Hfields Hstatus]].
  exact (conj Hcontext (conj Hinput (conj Hnonnull (conj Hguard (conj Hfields Hstatus))))).
Qed.

Lemma tmr_task_client_clear_status_pend_entry_from_ready : forall sg call state,
  tmr_task_unlock_entry sg call state -> os_sched_task_current_ready call state ->
  tmr_task_client_clear_status_pend_entry sg call state.
Proof.
  intros sg call state Hentry Hready; split; [exact Hentry|].
  apply tmr_task_caller_wait_status_clear_from_ready; exact Hready.
Qed.

Lemma tmr_task_client_clear_status_pend_count_checkpoint : forall sg call entry eid current,
  UCOS2_state_inv sg entry -> tmr_task_client_clear_status_pend_entry sg call entry ->
  mutex_query_lookup entry eid current -> current.(eventType) = OS_EVENT_TYPE_SEM ->
  0 < encode_event_cnt_value current ->
  tmr_task_client_clear_status_pend_entry sg call
    (sem_count_update_state entry eid current (encode_event_cnt_value current - 1)).
Proof.
  intros sg call entry eid current Hvalid Hentry Hlookup Htype Hpositive.
  pose proof (tmr_task_client_clear_status_pend_entry_sem _ _ _ Hvalid Hentry) as Hsem.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  specialize (Hpayload eid current Hlookup); unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload; destruct current.(semFields) as [fields|] eqn:Hfields; [|contradiction].
  assert (Hcount : encode_event_cnt_value current = fields.(semCount)).
  { unfold encode_event_cnt_value; rewrite Htype, Hfields; reflexivity. }
  assert (Hstep : sem_pend_first_critical sg eid 0 entry SemPendAcquired
    (sem_count_update_state entry eid current (encode_event_cnt_value current - 1))).
  { rewrite Hcount; eapply sem_pend_immediate_first_critical; eauto; lia. }
  apply tmr_task_client_clear_status_pend_entry_from_sem.
  - eapply sem_pend_clear_status_immediate_checkpoint; eassumption.
  - destruct Hentry as [[_ [_ [_ [_ [_ Hclear]]]]] Hstatus].
    intros node Hnode; exact (proj2 (proj2 (proj1 (proj2 (Hclear node Hnode))))).
Qed.

Lemma tmr_task_client_clear_status_pend_cleanup_checkpoint : forall sg call resumed eid old result checkpoint,
  sem_pend_resume_entry sg resumed eid call.(os_sched_call_stack).(stackLeaseSlot) old ->
  sem_pend_client_phase_context sg call resumed -> old.(curPrio) <> sg.(osLowestPrio) ->
  old.(tcbEventMultiPtr) = 0 -> sem_pend_resume_critical sg eid resumed result checkpoint ->
  tmr_task_client_clear_status_pend_entry sg call checkpoint.
Proof.
  intros * Hentry Hcontext Hnonidle Hzero Hstep.
  apply tmr_task_client_clear_status_pend_entry_from_sem.
  - eapply sem_pend_clear_status_cleanup_checkpoint; eassumption.
  - pose proof Hentry as [_ [Hcurrent [Hold Hrest]]].
    pose proof (tmr_task_pend_cleanup_multi_pointer_transport sg eid resumed _ old result checkpoint
      Hcurrent Hold Hzero Hstep) as Htransport.
    exact (tmr_task_multi_pointer_transport_slot_zero resumed checkpoint _ old Htransport Hold Hzero).
Qed.

Lemma tmr_task_client_clear_status_pend_cleanup_stores : forall sg call cleaning tid node,
  sem_pend_cleanup_entry sg cleaning tid node -> sem_pend_client_phase_context sg call cleaning ->
  node.(curPrio) <> sg.(osLowestPrio) -> node.(tcbEventMultiPtr) = 0 ->
  UCOS2_state_inv sg (event_pend_cleanup_state sg false cleaning tid node) /\
  tmr_task_client_clear_status_pend_entry sg call (event_pend_cleanup_state sg false cleaning tid node).
Proof.
  intros * Hcleanup Hcontext Hnonidle Hzero.
  destruct (sem_pend_task_client_cleanup_checkpoint sg call cleaning tid node
    Hcleanup Hcontext Hnonidle Hzero) as [Hvalid [Hstage [Hidle [Havailable Hall]]]].
  split; [exact Hvalid|]. apply tmr_task_client_clear_status_pend_entry_from_sem; [|exact Hall].
  eapply sem_pend_clear_status_call_entry_from_stage; eassumption.
Qed.

Lemma tmr_task_client_clear_status_pend_post_from_result : forall environment local critical sg call returned mask
  pevent timeout perr before current error X,
  sem_pend_client_runtime_program environment critical sg call pevent timeout before error current ->
  sem_pend_client_fields_call_safe environment critical sg call pevent timeout before X ->
  kernel_stack_call_same_call returned call -> tmr_task_client_clear_status_pend_entry sg returned current ->
  TT ** perr # UChar |-> error ** sem_pend_fields_closed environment local sg returned mask current |--
  tmr_task_client_clear_status_pend_post environment critical sg call mask pevent timeout perr before X.
Proof.
  intros * Hresult Hsafe Hsame Hentry.
  pose proof (sem_query_safe_return _ _ _ _ _ Hresult Hsafe) as Hreturn.
  unfold tmr_task_client_clear_status_pend_post; Exists returned current local error; entailer!;
    intros heap Hheap; exact (conj Hresult (conj Hreturn (conj Hsame Hentry))).
Qed.

Lemma tmr_task_client_clear_status_pend_post_null : forall environment local critical sg call mask timeout perr before X,
  sem_pend_client_fields_call_safe environment critical sg call 0 timeout before X ->
  tmr_task_client_clear_status_pend_entry sg call before ->
  TT ** perr # UChar |-> 4 ** sem_pend_fields_closed environment local sg call mask before |--
  tmr_task_client_clear_status_pend_post environment critical sg call mask 0 timeout perr before X.
Proof.
  intros * Hsafe Hentry; apply tmr_task_client_clear_status_pend_post_from_result.
  - apply sem_pend_client_program_null.
  - exact Hsafe.
  - unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call; auto.
  - exact Hentry.
Qed.

Lemma tmr_task_client_clear_status_pend_post_context_error : forall environment local critical sg call mask
  pevent timeout perr before eid observed code X,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = Some code ->
  sem_pend_client_fields_call_safe environment critical sg call pevent timeout before X ->
  tmr_task_client_clear_status_pend_entry sg call before ->
  TT ** perr # UChar |-> encode_os_err_code code **
    sem_pend_fields_closed environment local sg call mask before |--
  tmr_task_client_clear_status_pend_post environment critical sg call mask pevent timeout perr before X.
Proof.
  intros * Hnonnull Haddress Hid Hslot Hguard Hsafe Hentry.
  apply tmr_task_client_clear_status_pend_post_from_result.
  - eapply sem_pend_client_program_context_error; eassumption.
  - exact Hsafe.
  - unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call; auto.
  - exact Hentry.
Qed.

(** The actual source packet and owner are opened once. The old checkpoint
    fields and status come from the real count/cleanup path. No ready state
    or replacement returned descriptor is assumed. *)
Lemma tmr_task_client_clear_status_pend_post_from_restore : forall environment local critical sg context call mask
  pevent timeout perr before checkpoint error X,
  UCOS2_state_inv sg checkpoint -> tmr_task_client_clear_status_pend_entry sg call checkpoint ->
  sem_pend_client_checkpoint_result environment critical sg context pevent timeout before error checkpoint ->
  kernel_stack_call_same_call call context ->
  sem_pend_client_fields_call_safe environment critical sg context pevent timeout before X ->
  TT ** sem_pend_clear_status_phase_restore_output SemPendReturnPhase environment local critical sg call mask checkpoint **
    perr # UChar |-> error |--
  tmr_task_client_clear_status_pend_post environment critical sg context mask pevent timeout perr before X.
Proof.
  intros * Hvalid Hentry Hcheckpoint Hcall Hsafe.
  unfold sem_pend_clear_status_phase_restore_output; Intros returned current.
  assert (Hsource : sem_pend_client_return_source environment critical sg call checkpoint returned current) by tauto.
  pose proof (tmr_task_client_clear_status_pend_entry_return _ _ _ _ _ _ _ Hvalid Hentry Hsource) as Hafter.
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hsource) as Hreturned.
  assert (Hsame : kernel_stack_call_same_call returned context).
  { unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence. }
  pose proof (sem_pend_client_program_restore environment critical sg context call returned
    pevent timeout before checkpoint error current Hcheckpoint Hcall Hsource) as Hresult.
  pose proof (sem_query_safe_return _ _ _ _ _ Hresult Hsafe) as Hreturn.
  unfold tmr_task_client_clear_status_pend_post; Exists returned current local error; entailer!;
    intros heap Hheap; exact (conj Hresult (conj Hreturn (conj Hsame Hafter))).
Qed.

Lemma tmr_task_client_clear_status_pend_post_forget_entry : forall environment critical sg call mask
  pevent timeout perr before X,
  tmr_task_client_clear_status_pend_post environment critical sg call mask pevent timeout perr before X |--
  sem_pend_client_fields_call_post environment critical sg call mask pevent timeout perr before X.
Proof.
  intros; unfold tmr_task_client_clear_status_pend_post, sem_pend_client_fields_call_post.
  Intros returned current local error; Exists returned current local error; entailer!.
Qed.
