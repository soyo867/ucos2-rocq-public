Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_acquire_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_fields_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_checkpoint_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source provenance for waiting, before its property-specific receipts
    are erased. The Scheduler constructor keeps the original C body union,
    including its legacy prefixes and IRQ return. It asks for no waiter
    projection, opaque Task ABI resume, or public Timer image frame.
    The actual caller receipts must separately establish the observations
    used by the C continuation; this definition alone does not do so. *)
Inductive sem_pend_client_wait_source environment critical sg original eid generation :
  UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| SemPendClientWaitLegacy : forall before after,
    sem_pend_source_history environment critical sg original eid generation before after ->
    sem_pend_client_wait_source environment critical sg original eid generation before after
| SemPendClientWaitReturn : forall before call returned after,
    kernel_stack_call_same_call call original ->
    sem_pend_client_return_source environment critical sg call before returned after ->
    sem_pend_client_wait_source environment critical sg original eid generation before after
| SemPendClientWaitScheduler : forall before call returned after,
    kernel_stack_call_same_call call original ->
    SchedulerPhaseCandidate.os_sched_task_body_source environment critical sg before call returned after ->
    sem_pend_client_wait_source environment critical sg original eid generation before after
| SemPendClientWaitTrans : forall before middle after,
    sem_pend_client_wait_source environment critical sg original eid generation before middle ->
    sem_pend_client_wait_source environment critical sg original eid generation middle after ->
    sem_pend_client_wait_source environment critical sg original eid generation before after.

Lemma sem_pend_client_wait_source_refl : forall environment critical sg original eid generation state,
  sem_pend_client_wait_source environment critical sg original eid generation state state.
Proof. intros; apply SemPendClientWaitLegacy, sem_pend_source_history_refl. Qed.

Definition sem_pend_client_wait_origin environment critical sg context returned mask saved before observed
  entry eid current tid old : Prop :=
  sem_pend_client_acquire_observation environment critical sg context returned mask saved
    before entry eid observed current /\
  sem_pend_wait_entry sg entry eid current tid old /\
  context.(os_sched_call_origin) = RunningInvocation tid old.(taskGeneration) /\
  kernel_call_task_source context entry /\
  sched_current_consistency entry.(TskState) entry.(SchedState).

Definition sem_pend_client_wait_history environment critical sg context mask before observed
  eid timeout waiting : Prop :=
  UCOS2_state_inv sg waiting /\ kernel_call_task_source context waiting /\
  sched_current_consistency waiting.(TskState) waiting.(SchedState) /\
  exists saved returned entry current tid old,
    sem_pend_client_wait_origin environment critical sg context returned mask saved before observed
      entry eid current tid old /\
    waiting = event_pend_state sg entry eid current tid old PendSem timeout.

Lemma sem_pend_client_wait_origin_history : forall environment critical sg context returned mask saved
  before observed entry eid current tid old timeout,
  sem_pend_client_wait_origin environment critical sg context returned mask saved before observed
    entry eid current tid old ->
  sem_pend_client_wait_history environment critical sg context mask before observed eid timeout
    (event_pend_state sg entry eid current tid old PendSem timeout).
Proof.
  intros * Horigin.
  pose proof Horigin as [Hacquire [Hentry [Horiginal [Hsource Hcache]]]].
  destruct (sem_pend_wait_preserves_call_source sg context entry eid current tid old timeout
    Hentry Hsource Hcache) as [Hvalid [Hwaiting Hwaiting_cache]].
  split; [exact Hvalid|]. split; [exact Hwaiting|]. split; [exact Hwaiting_cache|].
  exists saved, returned, entry, current, tid, old; split; [exact Horigin|reflexivity].
Qed.

Lemma sem_pend_client_wait_history_waiter : forall environment critical sg context mask before observed
  eid timeout waiting,
  sem_pend_client_wait_history environment critical sg context mask before observed eid timeout waiting ->
  exists node,
    waiting.(TskState).(inUsedTaskStates) context.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
    sem_pend_wait_continuation eid context.(os_sched_call_stack).(stackLeaseGeneration) node.
Proof.
  intros * [_ [Hsource [_ [saved [returned [entry [current [tid [old [Horigin ->]]]]]]]]]].
  destruct Horigin as [_ [Hentry [Horiginal [Hentry_source Hcache]]]].
  pose proof (proj1 Hentry_source) as Hlease; rewrite Horiginal in Hlease.
  assert (Htid : tid = context.(os_sched_call_stack).(stackLeaseSlot)) by congruence.
  assert (Hgeneration : old.(taskGeneration) = context.(os_sched_call_stack).(stackLeaseGeneration))
    by congruence.
  subst tid.
  pose proof Hentry as [Hvalid [_ [_ [Hold [_ [_ [_ [_ [Hmulti [Hflag [Hready _]]]]]]]]]]].
  pose proof Hvalid as [_ [_ [[Hrdy Hmeta] _]]].
  destruct (proj1 Hrdy _ Hready) as [found [Hfound [_ Heffective]]].
  assert (found = old) by congruence; subst found.
  exists (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)); split.
  - cbn [event_pend_state event_wait_state replace_TskS replace_SchedS replace_EventS
      TskState glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
  - rewrite <- Hgeneration. apply sem_pend_wait_establishes_continuation; assumption.
Qed.

Definition sem_pend_client_resume_origin environment critical sg context mask before observed
  eid timeout resumed tid old : Prop :=
  sem_pend_resume_entry sg resumed eid tid old /\
  context.(os_sched_call_origin) = RunningInvocation tid old.(taskGeneration) /\
  exists waiting,
    sem_pend_client_wait_history environment critical sg context mask before observed eid timeout waiting /\
    sem_pend_client_wait_source environment critical sg context eid old.(taskGeneration) waiting resumed.

Definition sem_pend_client_cleanup_origin environment critical sg context mask before observed
  eid timeout error cleaning tid node : Prop :=
  sem_pend_cleanup_entry sg cleaning tid node /\
  exists resumed old code,
    sem_pend_client_resume_origin environment critical sg context mask before observed
      eid timeout resumed tid old /\
    error = encode_os_err_code code /\
    sem_pend_resume_critical sg eid resumed code (event_pend_cleanup_state sg false cleaning tid node).

Definition sem_pend_client_checkpoint_result environment critical sg context pevent timeout before error checkpoint : Prop :=
  exists eid observed returned mask saved entry current start waiting,
    pevent <> 0 /\ pevent = event_addr sg eid /\ valid_event_id sg eid /\
    sem_query_public_slot before eid observed /\
    sem_pend_context_error (event_slot_type_value before.(EventState) eid)
      before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None /\
    sem_pend_client_acquire_observation environment critical sg context returned
      mask saved before entry eid observed current /\
    sem_pend_first_critical sg eid timeout entry start waiting /\
    match start with
    | SemPendAcquired => error = 0 /\ checkpoint = waiting
    | SemPendWaiting tid generation =>
        context.(os_sched_call_origin) = RunningInvocation tid generation /\
        exists resumed node code,
          sem_pend_client_wait_source environment critical sg context eid generation waiting resumed /\
          sem_pend_resume_entry sg resumed eid tid node /\ node.(taskGeneration) = generation /\
          error = encode_os_err_code code /\ sem_pend_resume_critical sg eid resumed code checkpoint
    end.

Lemma sem_pend_client_immediate_result : forall environment critical sg context returned pevent timeout
  before eid observed mask saved entry current,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  sem_pend_client_acquire_observation environment critical sg context returned mask saved
    before entry eid observed current ->
  0 < encode_event_cnt_value current ->
  sem_pend_client_checkpoint_result environment critical sg context pevent timeout before 0
    (sem_count_update_state entry eid current (encode_event_cnt_value current - 1)).
Proof.
  intros * Hnonnull Haddr Hid Hslot Hcontext Hacquire Hpositive.
  pose proof Hacquire as [_ [_ [_ [Hvalid [_ [Hlookup [_ [Htype _]]]]]]]].
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  specialize (Hpayload eid current Hlookup); unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload; destruct current.(semFields) as [fields|] eqn:Hfields; [|contradiction].
  assert (Hcount : encode_event_cnt_value current = fields.(semCount)).
  { unfold encode_event_cnt_value; rewrite Htype, Hfields; reflexivity. }
  exists eid, observed, returned, mask, saved, entry, current, SemPendAcquired,
    (sem_count_update_state entry eid current (encode_event_cnt_value current - 1)).
  split; [exact Hnonnull|]. split; [exact Haddr|]. split; [exact Hid|]. split; [exact Hslot|].
  split; [exact Hcontext|]. split; [exact Hacquire|]. split.
  - rewrite Hcount; eapply sem_pend_immediate_first_critical; eauto; lia.
  - auto.
Qed.

Lemma sem_pend_client_cleanup_result : forall environment critical sg context mask before observed eid
  pevent timeout error cleaning tid node,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  sem_pend_client_cleanup_origin environment critical sg context mask before observed eid timeout
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
  - rewrite HwaitingEq; apply sem_pend_wait_entry_first_critical; exact Hentry.
  - split; [exact HfirstOrigin|]. exists resumed, old, code.
    split; [rewrite Hgeneration; exact Hpath|].
    split; [exact Hresume|]. split; [symmetry; exact Hgeneration|]. split; assumption.
Qed.

Lemma sem_pend_client_resume_cleanup_without_timeout : forall environment critical sg context mask
  before observed eid timeout resumed tid old,
  sem_pend_client_resume_origin environment critical sg context mask before observed eid timeout resumed tid old ->
  old.(statPend) <> PendTimeout ->
  sem_pend_client_cleanup_origin environment critical sg context mask before observed eid timeout
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

Lemma sem_pend_client_resume_cleanup_timeout : forall environment critical sg context mask
  before observed eid timeout resumed tid old current,
  sem_pend_client_resume_origin environment critical sg context mask before observed eid timeout resumed tid old ->
  old.(statPend) = PendTimeout -> mutex_query_lookup resumed eid current ->
  sem_pend_client_cleanup_origin environment critical sg context mask before observed eid timeout 10
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

(** The old runtime is retained as a whole, not replaced by a selected
    subcase. The added branch covers acquired private Timer cuts and a
    final client-level Restore. Its source and exact count/cleanup effect
    remain distinct. No equivalence with the old narrower source is used. *)
Definition sem_pend_client_runtime_program environment critical sg context pevent timeout
  : program UCOS2_Verify_State Z :=
  fun before error current =>
    sem_pend_source_fields_program environment critical sg context pevent timeout before error current \/
    exists checkpoint call returned,
      sem_pend_client_checkpoint_result environment critical sg context pevent timeout before error checkpoint /\
      kernel_stack_call_same_call call context /\
      sem_pend_client_return_source environment critical sg call checkpoint returned current.

Lemma sem_pend_source_program_implies_client_program : forall environment critical sg call pevent timeout
  before error current,
  sem_pend_source_fields_program environment critical sg call pevent timeout before error current ->
  sem_pend_client_runtime_program environment critical sg call pevent timeout before error current.
Proof. intros; left; exact H. Qed.

Lemma sem_pend_client_program_null : forall environment critical sg call timeout before,
  sem_pend_client_runtime_program environment critical sg call 0 timeout before 4 before.
Proof. intros; left; apply sem_pend_source_fields_program_null. Qed.

Lemma sem_pend_client_program_context_error : forall environment critical sg call pevent timeout before
  eid observed code,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = Some code ->
  sem_pend_client_runtime_program environment critical sg call pevent timeout
    before (encode_os_err_code code) before.
Proof. intros; left; eapply sem_pend_source_fields_program_context_error; eassumption. Qed.

Lemma sem_pend_client_program_restore : forall environment critical sg context call returned
  pevent timeout before checkpoint error current,
  sem_pend_client_checkpoint_result environment critical sg context pevent timeout before error checkpoint ->
  kernel_stack_call_same_call call context ->
  sem_pend_client_return_source environment critical sg call checkpoint returned current ->
  sem_pend_client_runtime_program environment critical sg context pevent timeout before error current.
Proof. intros; right; exists checkpoint, call, returned; auto. Qed.

Definition sem_pend_client_fields_call_safe environment critical sg call pevent timeout before
  (X : Z -> (UCOS2_Verify_State -> Prop) -> Prop) : Prop :=
  safeExec (LastSeen before)
    (StateRelMonad.bind (atomic_cmd (sem_pend_client_runtime_program environment critical sg call pevent timeout))
      sem_query_observe_error) X.

Definition sem_pend_client_fields_call_post environment critical sg call mask pevent timeout perr before X : Assertion :=
  EX returned current next_local error,
    coq_prop (sem_pend_client_runtime_program environment critical sg call pevent timeout before error current /\
      safeExec (LastSeen current) (StateRelMonad.ret error) X /\
      kernel_stack_call_same_call returned call) **
    (perr # UChar |-> error ** sem_pend_fields_closed environment next_local sg returned mask current).

Lemma sem_pend_client_fields_call_post_from_result : forall environment local critical sg call returned mask
  pevent timeout perr before current error X,
  sem_pend_client_runtime_program environment critical sg call pevent timeout before error current ->
  sem_pend_client_fields_call_safe environment critical sg call pevent timeout before X ->
  kernel_stack_call_same_call returned call ->
  TT ** perr # UChar |-> error ** sem_pend_fields_closed environment local sg returned mask current |--
  sem_pend_client_fields_call_post environment critical sg call mask pevent timeout perr before X.
Proof.
  intros * Hresult Hsafe Hsame.
  pose proof (sem_query_safe_return _ _ _ _ _ Hresult Hsafe) as Hreturn.
  unfold sem_pend_client_fields_call_post; Exists returned current local error; entailer!;
    intros heap Hheap; exact (conj Hresult (conj Hreturn Hsame)).
Qed.

Definition sem_pend_client_fields_restore_output environment local critical sg call mask checkpoint : Assertion :=
  EX returned current,
    coq_prop (sem_pend_client_return_source environment critical sg call checkpoint returned current) &&
    sem_pend_fields_closed environment local sg returned mask current.

(** For an interpreted actual C run, the owner is obtained from the run's
    resource theorem. It is not an assumed final heap. The certificate
    remains indexed by this exact run; coverage of its concrete leaves is
    a separate obligation, with no universal coverage claim here. *)
Lemma sem_pend_client_fields_restore_output_from_c_sequence : forall environment critical sg call
  (leaf : forall state before input stopped returned after output,
    kernel_program_c_step environment critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin)
      state before input stopped returned after output ->
    TaskInvocationOrigin -> TaskInvocationOrigin -> Prop),
  (forall state before input stopped returned after output
    (step : kernel_program_c_step environment critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) state before input stopped returned after output) first last,
    leaf state before input stopped returned after output step first last ->
    exists trace : kernel_client_task_source_trace environment.(task_stack_call_external)
        environment.(task_stack_call_port) critical.(critical_region_clients) sg
        call.(os_sched_call_invocation) None first state stopped last returned,
      sem_pend_client_source_calls environment.(task_stack_call_external) environment.(task_stack_call_port)
        critical.(critical_region_clients) sg call.(os_sched_call_invocation) None
        first state stopped last returned trace) ->
  forall checkpoint before input current after returned local mask
    (run : kernel_c_sequence
      (kernel_program_c_step environment critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin))
      checkpoint before input false current after (sem_pend_fields_closed environment local sg returned mask current)),
  sem_pend_c_sequence_call_certificate
    (kernel_program_c_step environment critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin))
    leaf checkpoint before input false current after (sem_pend_fields_closed environment local sg returned mask current)
    run call.(os_sched_call_origin) returned.(os_sched_call_origin) ->
  kernel_call_normal_return call checkpoint returned current ->
  sem_pend_client_fields_restore_output environment local critical sg call mask checkpoint after.
Proof.
  intros environment critical sg call leaf Hleaf checkpoint before input current after returned local mask
    run Hcalls Hnormal.
  destruct (sem_pend_client_return_source_from_c_sequence environment critical sg call leaf Hleaf
    checkpoint before input current after (sem_pend_fields_closed environment local sg returned mask current)
    returned run Hcalls Hnormal) as [Hsource Howner].
  unfold sem_pend_client_fields_restore_output.
  exists returned, current; split; assumption.
Qed.

(** This consumes the actual Restore result once. The local family, heap,
    returned descriptor, current state, exact error and arbitrary X all
    refer to that one result; no output is chosen by endpoint coincidence. *)
Lemma sem_pend_client_fields_call_post_from_restore : forall environment local critical sg context call mask
  pevent timeout perr before checkpoint error X,
  sem_pend_client_checkpoint_result environment critical sg context pevent timeout before error checkpoint ->
  kernel_stack_call_same_call call context ->
  sem_pend_client_fields_call_safe environment critical sg context pevent timeout before X ->
  TT ** sem_pend_client_fields_restore_output environment local critical sg call mask checkpoint **
    perr # UChar |-> error |--
  sem_pend_client_fields_call_post environment critical sg context mask pevent timeout perr before X.
Proof.
  intros * Hcheckpoint Hcall Hsafe.
  unfold sem_pend_client_fields_restore_output; Intros returned current.
  assert (Hsource : sem_pend_client_return_source environment critical sg call checkpoint returned current) by tauto.
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hsource) as Hreturned.
  assert (Hsame : kernel_stack_call_same_call returned context).
  { unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence. }
  assert (Hresult : sem_pend_client_runtime_program environment critical sg context pevent timeout before error current).
  { exact (sem_pend_client_program_restore environment critical sg context call returned
      pevent timeout before checkpoint error current Hcheckpoint Hcall Hsource). }
  pose proof (sem_query_safe_return _ _ _ _ _ Hresult Hsafe) as Hreturn.
  unfold sem_pend_client_fields_call_post; Exists returned current local error; entailer!;
    intros heap Hheap; exact (conj Hresult (conj Hreturn Hsame)).
Qed.
