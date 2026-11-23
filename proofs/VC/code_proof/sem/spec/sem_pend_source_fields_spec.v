Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_source_program_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_acquire_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_wait_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_cleanup_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_sched_source_spec.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

Definition sem_pend_source_fields_program environment critical sg call pevent timeout :=
  sem_pend_source_runtime_program environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (Some environment) critical sg call pevent timeout.

Definition sem_pend_source_fields_call_safe environment critical sg call pevent timeout before
  (X : Z -> (UCOS2_Verify_State -> Prop) -> Prop) : Prop :=
  safeExec (LastSeen before)
    (StateRelMonad.bind (atomic_cmd (sem_pend_source_fields_program environment critical sg call pevent timeout))
      sem_query_observe_error) X.

(** The public input domain and heap ownership are the existing fields
    domain.  The semantic program is explicitly the actual-source program;
    it is not claimed to be equal to the old runtime program. *)
Definition sem_pend_source_fields_call_pre environment local critical sg call mask pevent timeout
  perr before eid observed X : Assertion :=
  coq_prop (sem_pend_fields_call_domain environment critical sg call pevent before eid observed /\
    sem_pend_source_fields_call_safe environment critical sg call pevent timeout before X) &&
  (sem_pend_error_cell perr ** sem_pend_fields_closed environment local sg call mask before).

Definition sem_pend_source_fields_call_post environment critical sg call mask pevent timeout perr before X : Assertion :=
  EX returned current next_local error,
    coq_prop (sem_pend_source_fields_program environment critical sg call pevent timeout before error current /\
      safeExec (LastSeen current) (StateRelMonad.ret error) X /\
      kernel_stack_call_same_call returned call) **
    (perr # UChar |-> error ** sem_pend_fields_closed environment next_local sg returned mask current).

Lemma sem_pend_fields_program_implies_source_fields_program :
  forall environment critical sg call pevent timeout before error current,
  sem_pend_fields_program environment critical sg call pevent timeout before error current ->
  sem_pend_source_fields_program environment critical sg call pevent timeout before error current.
Proof. intros; eapply sem_pend_runtime_program_implies_source_runtime_program; exact H. Qed.

Lemma sem_pend_source_fields_program_null : forall environment critical sg call timeout before,
  sem_pend_source_fields_program environment critical sg call 0 timeout before 4 before.
Proof.
  intros; apply sem_pend_fields_program_implies_source_fields_program.
  apply sem_pend_fields_program_null.
Qed.

Lemma sem_pend_source_fields_program_context_error : forall environment critical sg call pevent timeout before
  eid observed code,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = Some code ->
  sem_pend_source_fields_program environment critical sg call pevent timeout
    before (encode_os_err_code code) before.
Proof.
  intros; apply sem_pend_fields_program_implies_source_fields_program.
  eapply sem_pend_fields_program_context_error; eassumption.
Qed.

Lemma sem_pend_source_fields_call_post_from_result : forall environment local critical sg call returned mask
  pevent timeout perr before current error X,
  sem_pend_source_fields_program environment critical sg call pevent timeout before error current ->
  sem_pend_source_fields_call_safe environment critical sg call pevent timeout before X ->
  kernel_stack_call_same_call returned call ->
  TT ** perr # UChar |-> error ** sem_pend_fields_closed environment local sg returned mask current |--
  sem_pend_source_fields_call_post environment critical sg call mask pevent timeout perr before X.
Proof.
  intros * Hresult Hsafe Hsame.
  pose proof (sem_query_safe_return _ _ _ _ _ Hresult Hsafe) as Hreturn.
  unfold sem_pend_source_fields_call_post; Exists returned current local error; entailer!;
    intros heap Hheap; exact (conj Hresult (conj Hreturn Hsame)).
Qed.

(** Immediate and cleanup checkpoints end before the actual final Restore.
    Its returned world is the state observed by the same arbitrary X. *)
Lemma sem_pend_source_fields_call_post_from_restore : forall environment local critical sg context call mask
  pevent timeout perr before checkpoint error eid X,
  sem_pend_source_checkpoint_result (Some environment) critical sg context pevent timeout before error checkpoint ->
  pevent <> 0 -> pevent = event_addr sg eid ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  kernel_stack_call_same_call call context ->
  sem_pend_source_fields_call_safe environment critical sg context pevent timeout before X ->
  TT ** sem_pend_fields_phase_restore_output SemPendReturnPhase environment local critical sg call mask checkpoint **
    perr # UChar |-> error |--
  sem_pend_source_fields_call_post environment critical sg context mask pevent timeout perr before X.
Proof.
  intros * Hcheckpoint Hnonzero Haddress Hclear Hcall Hsafe.
  unfold sem_pend_fields_phase_restore_output; Intros returned current.
  repeat rewrite logic_equiv_coq_prop_andp_sepcon.
  repeat rewrite logic_equiv_sepcon_coq_prop_andp.
  repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end).
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call checkpoint returned current) by tauto.
  assert (Hreturned : kernel_stack_call_same_call returned call) by
    (unfold sem_pend_stack_restore_observation in *; tauto).
  assert (Hoptional : sem_pend_optional_restore_history environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (Some environment) critical sg call checkpoint returned current).
  { right; exact Hhistory. }
  assert (Hresult : sem_pend_source_fields_program environment critical sg context pevent timeout before error current).
  { unfold sem_pend_source_fields_program, sem_pend_source_runtime_program.
    right; exists checkpoint, call, returned, eid; tauto. }
  assert (Hsame : kernel_stack_call_same_call returned context).
  { unfold kernel_stack_call_same_call in *; intuition congruence. }
  pose proof (sem_query_safe_return _ _ _ _ _ Hresult Hsafe) as Hreturn.
  unfold sem_pend_source_fields_call_post; Exists returned current local error; entailer!;
    intros heap Hheap; exact (conj Hresult (conj Hreturn Hsame)).
Qed.

Definition sem_pend_source_save_phase_pre phase environment critical sg call mask before : Prop :=
  match phase with
  | SemPendAcquirePhase _ _ _ => sem_pend_save_phase_pre phase environment critical sg call mask before
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      mask = initial_mask /\
      sem_pend_source_wait_selected_at environment critical sg original initial_mask initial observed eid timeout
        waiting call before
  | SemPendReturnPhase => False
  end.

Definition sem_pend_source_save_phase_observation phase environment critical sg call returned mask saved before acquired : Prop :=
  match phase with
  | SemPendAcquirePhase _ _ _ =>
      sem_pend_save_phase_observation phase environment critical sg call returned mask saved before acquired
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      sem_pend_source_wait_selected_at environment critical sg original initial_mask initial observed eid timeout
        waiting returned acquired
  | SemPendReturnPhase => False
  end.

Definition sem_pend_source_restore_phase_pre phase environment critical sg call mask checkpoint : Prop :=
  match phase with
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      mask = initial_mask /\
      sem_pend_source_wait_at environment critical sg original initial_mask initial observed eid timeout
        waiting call checkpoint /\ sem_pend_wait_sched_entry sg call checkpoint
  | SemPendReturnPhase => True
  | SemPendAcquirePhase _ _ _ => False
  end.

Definition sem_pend_source_fields_phase_save_input phase environment local critical sg call mask before : Assertion :=
  coq_prop (sem_pend_source_save_phase_pre phase (Some environment) critical sg call mask before) &&
  sem_pend_fields_closed environment local sg call mask before.

Definition sem_pend_source_fields_phase_save_output phase environment local critical sg call mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (kernel_call_save_source environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical sg call returned mask saved before acquired /\
      kernel_call_normal_return call before returned acquired /\
      sem_pend_save_rely sg before acquired /\
      sem_pend_stack_save_observation critical sg call returned (Some environment) mask saved before acquired /\
      sem_pend_source_save_phase_observation phase (Some environment) critical sg call returned mask saved before acquired) &&
    sem_pend_fields_masked environment local critical sg returned saved acquired acquired.

Definition sem_pend_source_fields_phase_restore_input phase environment local critical
  sg call mask saved acquired checkpoint : Assertion :=
  coq_prop (interrupt_saved_value mask saved /\
    sem_pend_source_restore_phase_pre phase (Some environment) critical sg call mask checkpoint) &&
  sem_pend_fields_masked environment local critical sg call saved acquired checkpoint.

Definition sem_pend_source_fields_phase_restore_output phase environment local critical
  sg call mask checkpoint : Assertion :=
  EX returned current,
    coq_prop (sem_pend_modular_call_history environment critical sg call checkpoint returned current /\
      sem_pend_stack_restore_observation sg call returned (Some environment) checkpoint current /\
      sem_pend_source_restore_phase_pre phase (Some environment) critical sg returned mask current) &&
    sem_pend_fields_closed environment local sg returned mask current.

Definition sem_pend_source_fields_phase_sched_input phase environment local critical sg call mask before : Assertion :=
  match phase with
  | SemPendWaitPhase _ _ _ _ _ _ _ =>
      coq_prop (sem_pend_source_restore_phase_pre phase (Some environment) critical sg call mask before) &&
      sem_pend_fields_closed environment local sg call mask before
  | _ => coq_prop False && emp
  end.

Definition sem_pend_source_fields_phase_sched_output phase environment critical sg call mask before : Assertion :=
  match phase with
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      EX returned current next_local,
        coq_prop (os_sched_continuation_call_history environment critical sg call mask before returned current /\
          kernel_stack_call_same_call returned call /\
          sem_pend_source_wait_selected_at (Some environment) critical sg original initial_mask initial observed
            eid timeout waiting returned current) &&
        sem_pend_fields_closed environment next_local sg returned mask current
  | _ => coq_prop False && emp
  end.

(** Source consumers take one observed call and its returned owner.  The
    receipt is produced together with that call's source trace; these
    lemmas do not strengthen the generic CPU callee's Ensure. *)
Lemma sem_pend_source_fields_save_acquire_from_source : forall environment local critical sg call returned
  pevent eid observed mask saved before acquired,
  UCOS2_state_inv sg before ->
  sem_pend_source_save_phase_pre (SemPendAcquirePhase pevent eid observed)
    (Some environment) critical sg call mask before ->
  kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned mask saved before acquired ->
  sem_pend_source_modular_call_history environment critical sg call before returned acquired ->
  sem_pend_save_rely sg before acquired ->
  sem_pend_fields_masked environment local critical sg returned saved acquired acquired |--
  sem_pend_source_fields_phase_save_output (SemPendAcquirePhase pevent eid observed)
    environment local critical sg call mask saved before.
Proof.
  intros * Hvalid Hpre Hsave Hsource Hrely heap Howned.
  pose proof (sem_pend_source_modular_call_history_forgets _ _ _ _ _ _ _ Hsource)
    as [Htrace Hnormal].
  pose proof (sem_pend_fields_masked_observations environment local critical sg
    returned saved acquired acquired heap Howned) as [Hvalid' Hrange].
  pose proof (sem_pend_source_acquire_phase_observation environment critical sg call returned
    pevent eid observed mask saved before acquired Hsource Hvalid Hrange Hpre Hsave Hnormal Hrely)
    as Hphase.
  pose proof Hsave as [_ [Hi [Ho [Hs Hsaved]]]].
  exists returned, acquired; split; [|exact Howned].
  split; [exact Hsave|]. split; [exact Hnormal|]. split; [exact Hrely|]. split.
  - unfold sem_pend_stack_save_observation; split; [exact (proj1 Hnormal)|].
    split; [exact Hsaved|discriminate].
  - exact Hphase.
Qed.

Lemma sem_pend_source_fields_save_wait_from_source : forall environment local critical sg original
  initial_mask initial observed eid timeout waiting call returned mask saved before acquired,
  sem_pend_source_save_phase_pre
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    (Some environment) critical sg call mask before ->
  kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned mask saved before acquired ->
  sem_pend_source_modular_call_history environment critical sg call before returned acquired ->
  sem_pend_save_rely sg before acquired ->
  sem_pend_fields_masked environment local critical sg returned saved acquired acquired |--
  sem_pend_source_fields_phase_save_output
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment local critical sg call mask saved before.
Proof.
  intros * [Hmask Hselected] Hsave Hsource Hrely heap Howned.
  pose proof (sem_pend_source_modular_call_history_forgets _ _ _ _ _ _ _ Hsource)
    as [Htrace Hnormal].
  pose proof (sem_pend_source_wait_selected_modular_return environment critical sg original initial_mask
    initial observed eid timeout waiting call before returned acquired Hselected Hsource Hrely) as Hselected'.
  pose proof Hsave as [_ [Hi [Ho [Hs Hsaved]]]].
  exists returned, acquired; split; [|exact Howned].
  split; [exact Hsave|]. split; [exact Hnormal|]. split; [exact Hrely|]. split.
  - unfold sem_pend_stack_save_observation; split; [exact (proj1 Hnormal)|].
    split; [exact Hsaved|discriminate].
  - exact Hselected'.
Qed.

Lemma sem_pend_source_fields_restore_wait_from_source : forall environment local critical sg original
  initial_mask initial observed eid timeout waiting call returned mask checkpoint current,
  kernel_tcb_stack_field_layout sg -> UCOS2_state_inv sg checkpoint ->
  sem_pend_source_restore_phase_pre
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    (Some environment) critical sg call mask checkpoint ->
  sem_pend_source_modular_call_history environment critical sg call checkpoint returned current ->
  sem_pend_blocking_rely sg checkpoint current ->
  sem_pend_fields_closed environment local sg returned mask current |--
  sem_pend_source_fields_phase_restore_output
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment local critical sg call mask checkpoint.
Proof.
  intros * Hlayout Hvalid [Hmask [Hwait Hentry]] Hsource Hrely heap Howned.
  pose proof (sem_pend_source_modular_call_history_forgets _ _ _ _ _ _ _ Hsource) as Hhistory.
  pose proof (sem_pend_source_wait_at_modular_return environment critical sg original initial_mask
    initial observed eid timeout waiting call checkpoint returned current Hvalid Hwait Hsource) as Hwait'.
  pose proof (sem_pend_wait_sched_entry_modular_return environment critical sg call checkpoint
    returned current Hlayout Hvalid (proj1 (proj2 (proj2 Hentry))) Hentry Hhistory Hrely) as Hentry'.
  exists returned, current; split; [|exact Howned].
  split; [exact Hhistory|]. split.
  - unfold sem_pend_stack_restore_observation; split; [exact (proj1 (proj2 Hhistory))|].
    intros Hvalid0 Hcall0.
    apply (proj2 (task_tcb_init_stack_same_call_source_iff returned call current
      (proj1 (proj2 Hhistory)))).
    exact (task_tcb_init_stack_registered_source_preserved
      environment.(task_stack_call_external) environment.(task_stack_call_port) critical
      sg call returned checkpoint current Hvalid0 (proj1 (proj2 Hhistory)) (proj1 Hhistory) Hcall0).
  - split; [exact Hmask|]. split; assumption.
Qed.

Definition sem_pend_source_fields_sched_save_output phase environment local critical sg call mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (kernel_call_save_source environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical sg call returned mask saved before acquired /\
      kernel_call_normal_return call before returned acquired /\
      sem_pend_blocking_rely sg before acquired /\
      sem_pend_source_restore_phase_pre phase (Some environment) critical sg returned mask acquired) &&
    sem_pend_fields_masked environment local critical sg returned saved acquired acquired.

Lemma sem_pend_source_fields_sched_save_from_source : forall environment local critical sg original
  initial_mask initial observed eid timeout waiting call returned mask saved before acquired,
  kernel_tcb_stack_field_layout sg -> UCOS2_state_inv sg before ->
  sem_pend_source_restore_phase_pre
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    (Some environment) critical sg call mask before ->
  kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned mask saved before acquired ->
  sem_pend_source_modular_call_history environment critical sg call before returned acquired ->
  sem_pend_blocking_rely sg before acquired ->
  sem_pend_fields_masked environment local critical sg returned saved acquired acquired |--
  sem_pend_source_fields_sched_save_output
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment local critical sg call mask saved before.
Proof.
  intros * Hlayout Hvalid [Hmask [Hwait Hentry]] Hsave Hsource Hrely heap Howned.
  pose proof (sem_pend_source_modular_call_history_forgets _ _ _ _ _ _ _ Hsource) as Hhistory.
  pose proof (sem_pend_source_wait_at_modular_return environment critical sg original initial_mask
    initial observed eid timeout waiting call before returned acquired Hvalid Hwait Hsource) as Hwait'.
  pose proof (sem_pend_wait_sched_entry_modular_return environment critical sg call before
    returned acquired Hlayout Hvalid (proj1 (proj2 (proj2 Hentry))) Hentry Hhistory Hrely) as Hentry'.
  exists returned, acquired; split; [|exact Howned].
  split; [exact Hsave|]. split; [exact (proj2 Hhistory)|]. split; [exact Hrely|].
  split; [exact Hmask|]. split; assumption.
Qed.

Lemma sem_pend_source_fields_sched_selected_from_source : forall environment local critical sg
  original initial_mask initial observed eid timeout waiting entered entry returned released saved acquired,
  UCOS2_state_inv sg entry ->
  sem_pend_source_wait_at (Some (task_sw_hook_call_environment environment)) critical sg
    original initial_mask initial observed eid timeout waiting entered entry ->
  sem_pend_wait_sched_entry sg entered entry ->
  os_sched_c_return (task_sw_hook_call_environment environment).(task_stack_call_external)
    critical sg entry entered returned released ->
  SchedulerPhaseCandidate.os_sched_task_body_source
    (task_sw_hook_call_environment environment) critical sg entry entered returned released ->
  (forall previous,
    entry.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some previous ->
    sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) previous ->
    sem_pend_task_projection entry.(TskState) released.(TskState)
      original.(os_sched_call_stack).(stackLeaseSlot) previous) ->
  sem_pend_fields_masked (task_sw_hook_call_environment environment) local critical sg
    returned saved acquired released |--
  coq_prop (sem_pend_source_wait_selected_at (Some (task_sw_hook_call_environment environment))
    critical sg original initial_mask initial observed eid timeout waiting returned released) &&
    sem_pend_fields_masked (task_sw_hook_call_environment environment) local critical sg
      returned saved acquired released.
Proof.
  intros * Hvalid Hwait Hentry Hbody Hsource Hprojection heap Howned.
  pose proof (sem_pend_fields_sched_ready_from_source environment local critical sg
    entered entry returned released saved acquired Hvalid Hentry Hsource heap Howned)
    as [Hready Hretained].
  pose proof (sem_pend_fields_masked_observations (task_sw_hook_call_environment environment)
    local critical sg returned saved acquired released heap Hretained) as [Hvalid' Hrange].
  pose proof (sem_pend_source_wait_at_c_scheduler (task_sw_hook_call_environment environment)
    critical sg original initial_mask initial observed eid timeout waiting entered entry returned released
    Hwait Hbody Hprojection) as Hwait'.
  pose proof Hwait' as [owned [Howned' [Hsame Hrest]]].
  destruct Hready as [node [[Hnode [Hcurrent [Hcache [Hmember Heffective]]]] Hgeneration]].
  rewrite (proj2 (proj2 Hsame)) in Hcurrent, Hmember.
  split; [|exact Hretained].
  eapply sem_pend_source_selected_from_ready_current; eassumption.
Qed.

Lemma sem_pend_source_fields_sched_selected_from_receipt : forall environment local critical sg
  original initial_mask initial observed eid timeout waiting entered entry returned released saved acquired,
  UCOS2_state_inv sg entry ->
  sem_pend_source_wait_at (Some (task_sw_hook_call_environment environment)) critical sg
    original initial_mask initial observed eid timeout waiting entered entry ->
  sem_pend_wait_sched_entry sg entered entry ->
  sem_pend_projected_source_client
    (task_sw_hook_call_environment environment).(task_stack_call_external).(os_sched_hook_action) ->
  sem_pend_source_scheduler_return (task_sw_hook_call_environment environment).(task_stack_call_external)
    critical sg entry entered returned released ->
  SchedulerPhaseCandidate.os_sched_task_body_source
    (task_sw_hook_call_environment environment) critical sg entry entered returned released ->
  sem_pend_fields_masked (task_sw_hook_call_environment environment) local critical sg
    returned saved acquired released |--
  coq_prop (sem_pend_source_wait_selected_at (Some (task_sw_hook_call_environment environment))
    critical sg original initial_mask initial observed eid timeout waiting returned released) &&
    sem_pend_fields_masked (task_sw_hook_call_environment environment) local critical sg
      returned saved acquired released.
Proof.
  intros * Hvalid Hwait Hentry Hhook Hreceipt Hsource.
  eapply sem_pend_source_fields_sched_selected_from_source; try eassumption.
  - eapply sem_pend_source_scheduler_return_forgets; exact Hreceipt.
  - intros previous Hprevious Hcontinue.
    eapply sem_pend_source_scheduler_return_projection; eassumption.
Qed.

Lemma sem_pend_source_fields_sched_restore_from_source : forall environment local critical sg original
  initial_mask initial observed eid timeout waiting call scheduled resumed returned mask saved
  before entry released current,
  kernel_call_save_source environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical sg call scheduled mask saved before entry ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry scheduled resumed released ->
  sem_pend_source_wait_selected_at (Some environment) critical sg original initial_mask initial observed
    eid timeout waiting resumed released ->
  sem_pend_source_modular_call_history environment critical sg resumed released returned current ->
  sem_pend_save_rely sg released current ->
  sem_pend_fields_closed environment local sg returned mask current |--
  sem_pend_source_fields_phase_sched_output
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment critical sg call mask before.
Proof.
  intros * Hsave Hbody Hselected Hsource Hrely heap Howned.
  pose proof (sem_pend_source_modular_call_history_forgets _ _ _ _ _ _ _ Hsource) as Hrestore.
  pose proof (sem_pend_source_wait_selected_modular_return environment critical sg original initial_mask
    initial observed eid timeout waiting resumed released returned current Hselected Hsource Hrely)
    as Hselected'.
  assert (Hhistory : os_sched_continuation_call_history environment critical sg call mask before returned current).
  { exists scheduled, entry, resumed, released, saved.
    split; [left; exact Hsave|]. split; [exact Hbody|].
    left; split; [exact (proj1 Hrestore)|exact (proj1 (proj2 Hrestore))]. }
  pose proof (os_sched_continuation_call_history_same_call environment critical sg
    call mask before returned current Hhistory) as Hsame.
  exists returned, current, local; split; [|exact Howned].
  split; [exact Hhistory|]. split; assumption.
Qed.

Lemma sem_pend_source_fields_sched_return_save_input : forall environment critical sg original initial_mask
  initial observed eid timeout waiting call mask before,
  mask = initial_mask ->
  sem_pend_source_fields_phase_sched_output
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment critical sg call mask before |--
  EX returned current next_local,
    coq_prop (os_sched_continuation_call_history environment critical sg call mask before returned current /\
      kernel_stack_call_same_call returned call) &&
    sem_pend_source_fields_phase_save_input
      (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
      environment next_local critical sg returned mask current.
Proof.
  intros * Hmask heap [returned [current [next_local [[Hhistory [Hsame Hselected]] Howned]]]].
  exists returned, current, next_local; split; [split; assumption|].
  split; [split; assumption|exact Howned].
Qed.

Lemma sem_pend_source_fields_return_restore_output : forall environment local critical sg call mask checkpoint,
  sem_pend_source_fields_phase_restore_output SemPendReturnPhase environment local critical sg
    call mask checkpoint =
  sem_pend_fields_phase_restore_output SemPendReturnPhase environment local critical sg
    call mask checkpoint.
Proof. reflexivity. Qed.

(** Reuse the existing byte-level Remove/cleanup producers and their
    continuation merge.  Only the pure source history at the checkpoint
    changes; the returned local map and Task generation/SP stay actual. *)
Lemma sem_pend_source_fields_timeout_remove_cleanup : forall environment critical sg context mask before observed eid
  timeout resumed tid old current,
  sem_pend_source_resume_origin environment critical sg context mask before observed eid timeout resumed tid old ->
  old.(statPend) = PendTimeout -> mutex_query_lookup resumed eid current -> event_object_layout_prop sg eid ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  event_task_remove_post (task_slot_addr sg tid)
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl")
    (old.(curPrio) / 8) (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) resumed.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) resumed.(TskState)) **
  sem_pend_fields_remove_call_frame sg resumed eid current tid old |--
  coq_prop (sem_pend_source_cleanup_origin environment critical sg context mask before observed eid timeout 10
    (event_task_remove_state resumed eid current tid old) tid (task_set_event_ptr old None)) &&
  UCOS2_fields_inv sg (event_task_remove_state resumed eid current tid old).
Proof.
  intros * Horigin Htimeout Hlookup Hlayout.
  pose proof (sem_pend_source_resume_cleanup_timeout environment critical sg context mask before observed eid
    timeout resumed tid old current Horigin Htimeout Hlookup) as Hcleanup.
  sep_apply_l_atomic (sem_pend_fields_remove_call_merge sg resumed eid current tid old
    (proj1 Horigin) Htimeout Hlookup Hlayout); repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.


Lemma sem_pend_source_fields_timeout_remove_continuation_merge : forall environment local critical sg
  original mask initial observed eid timeout resumed tid old current call saved acquired,
  sem_pend_source_resume_origin (Some environment) critical sg original mask initial observed eid
    timeout resumed tid old ->
  old.(statPend) = PendTimeout -> mutex_query_lookup resumed eid current -> event_object_layout_prop sg eid ->
  kernel_call_task_source call resumed ->
  task_stack_live_coverage resumed.(TskState) (task_stack_call_active_key call) ->
  critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) saved acquired **
  os_sched_context_resources environment.(task_stack_call_external) call **
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  event_task_remove_post (task_slot_addr sg tid)
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl")
    (old.(curPrio) / 8) (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) resumed.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) resumed.(TskState)) **
  sem_pend_fields_remove_call_frame sg resumed eid current tid old ** unmap_table_rep sg **
  store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations) resumed.(TskState) local)
    resumed.(TskState).(parkedTaskStacks) |--
  coq_prop (sem_pend_source_cleanup_origin (Some environment) critical sg original mask initial observed eid
      timeout 10 (event_task_remove_state resumed eid current tid old) tid (task_set_event_ptr old None) /\
    kernel_call_task_source call (event_task_remove_state resumed eid current tid old)) &&
  sem_pend_fields_masked environment local critical sg call saved acquired
    (event_task_remove_state resumed eid current tid old).
Proof.
  intros environment local critical sg original mask initial observed eid timeout resumed tid old current
    call saved acquired Horigin Htimeout Hlookup Hlayout Hsource Hcoverage.
  pose proof (proj1 Horigin) as [_ [_ [Hold _]]].
  pose proof (sem_pend_fields_remove_preserves_call_source call resumed eid current tid old Hold Hsource)
    as Hsource_after.
  assert (Hcovered : task_stack_live_coverage (event_task_remove_state resumed eid current tid old).(TskState)
    (task_stack_call_active_key call)).
  { apply (sem_pend_fields_task_update_preserves_coverage resumed.(TskState) (task_stack_call_active_key call)
      tid old (task_set_event_ptr old None) Hold eq_refl Hcoverage). }
  sep_apply_l_atomic (sem_pend_source_fields_timeout_remove_cleanup (Some environment) critical sg original
    mask initial observed eid timeout resumed tid old current Horigin Htimeout Hlookup Hlayout).
  sep_apply_l_atomic (sem_pend_fields_task_update_continuations environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) local resumed.(TskState) tid old
    (task_set_event_ptr old None) Hold eq_refl eq_refl).
  repeat rewrite logic_equiv_coq_prop_andp_sepcon.
  repeat rewrite logic_equiv_sepcon_coq_prop_andp.
  unfold sem_pend_fields_masked, kernel_continuation_call_masked, kernel_continuation_inv.
  rewrite kernel_program_fields_inv_split_unmap; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.


Lemma sem_pend_source_fields_cleanup_restore_input : forall environment local critical sg original initial_mask
  initial observed eid pevent timeout error cleaning tid node call mask saved acquired,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot initial eid observed ->
  sem_pend_context_error (event_slot_type_value initial.(EventState) eid)
    initial.(IntrState).(intNesting) initial.(IntrState).(lockNesting) = None ->
  sem_pend_source_cleanup_origin (Some environment) critical sg original initial_mask initial observed eid
    timeout error cleaning tid node ->
  interrupt_saved_value mask saved -> kernel_call_task_source call cleaning ->
  task_stack_live_coverage cleaning.(TskState) (task_stack_call_active_key call) ->
  critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) saved acquired **
  os_sched_context_resources environment.(task_stack_call_external) call **
  sem_pend_fields_cleanup_cells sg cleaning tid node ** unmap_table_rep sg **
  store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations) cleaning.(TskState) local)
    cleaning.(TskState).(parkedTaskStacks) |--
  coq_prop (sem_pend_source_checkpoint_result (Some environment) critical sg original pevent timeout initial error
      (event_pend_cleanup_state sg false cleaning tid node)) &&
  sem_pend_source_fields_phase_restore_input SemPendReturnPhase environment local critical sg call mask saved acquired
    (event_pend_cleanup_state sg false cleaning tid node).
Proof.
  intros environment local critical sg original initial_mask initial observed eid pevent timeout error cleaning
    tid node call mask saved acquired Hnonnull Haddress Hid Hslot Hordered Horigin Hsaved Hsource Hcoverage.
  pose proof (sem_pend_source_cleanup_result (Some environment) critical sg original initial_mask initial observed
    eid pevent timeout error cleaning tid node Hnonnull Haddress Hid Hslot Hordered Horigin) as Hresult.
  sep_apply_l_atomic (sem_pend_fields_cleanup_continuation_merge environment local critical sg call saved acquired
    cleaning tid node (proj1 Horigin) Hsource Hcoverage).
  unfold sem_pend_source_fields_phase_restore_input; cbn [sem_pend_source_restore_phase_pre];
    repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end);
    intros heap Hheap; exact (conj Hresult (conj (conj Hsaved I) Hheap)).
Qed.
