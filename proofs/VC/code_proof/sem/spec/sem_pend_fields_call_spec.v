Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_fields_sched_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Exactly the old owned-call source program, including its ordered early
    errors, positive-count return, waiting/selection/cleanup and final Restore.
    The resource migration does not define a new abstract Pend operation. *)
Definition sem_pend_fields_program environment critical sg call pevent timeout :=
  sem_pend_runtime_program environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (Some environment) critical sg call pevent timeout.

Definition sem_pend_fields_call_safe environment critical sg call pevent timeout before
  (X : Z -> (UCOS2_Verify_State -> Prop) -> Prop) : Prop :=
  safeExec (LastSeen before)
    (StateRelMonad.bind (atomic_cmd (sem_pend_fields_program environment critical sg call pevent timeout))
      sem_query_observe_error) X.

(** The old pure admission and layout guards are retained. Blocking layout
    is demanded only after the actual precritical guards have succeeded;
    NULL, free/wrong type, ISR and locked inputs are still represented. *)
Definition sem_pend_fields_call_domain environment critical sg call pevent before eid observed : Prop :=
  sem_pend_profile sg /\ kernel_tcb_stack_field_layout sg /\
  sem_pend_call_input critical sg call.(os_sched_call_invocation) pevent before eid observed /\
  sem_pend_runtime_nonblocking critical sg call (Some environment) pevent before eid /\
  sem_pend_observed_admission (Some environment) critical sg call pevent before eid /\
  (pevent <> 0 ->
    sem_pend_context_error (event_slot_type_value before.(EventState) eid)
      before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
    sem_pend_observed_blocking_layout (Some environment) critical sg call before eid
      sg.(g_OSTCBCur) sg.(g_OSRdyGrp) sg.(g_OSRdyTbl)).

Definition sem_pend_fields_call_pre environment local critical sg call mask pevent timeout
  perr before eid observed X : Assertion :=
  coq_prop (sem_pend_fields_call_domain environment critical sg call pevent before eid observed /\
    sem_pend_fields_call_safe environment critical sg call pevent timeout before X) &&
  (sem_pend_error_cell perr ** sem_pend_fields_closed environment local sg call mask before).

(** Existential local is the actual returned map interpretation, not a
    promise to reconstruct the entry family. The separated pure carrier is
    retained as in the existing SemPend post; no TT-to-emp step is used. *)
Definition sem_pend_fields_call_post environment critical sg call mask pevent timeout perr before X : Assertion :=
  EX returned current next_local error,
    coq_prop (sem_pend_fields_program environment critical sg call pevent timeout before error current /\
      safeExec (LastSeen current) (StateRelMonad.ret error) X /\
      kernel_stack_call_same_call returned call) **
    (perr # UChar |-> error ** sem_pend_fields_closed environment next_local sg returned mask current).

Lemma sem_pend_fields_program_null : forall environment critical sg call timeout before,
  sem_pend_fields_program environment critical sg call 0 timeout before 4 before.
Proof.
  intros; unfold sem_pend_fields_program, sem_pend_runtime_program.
  left; split; [apply sem_pend_c_null_return|]. split; [left; reflexivity|reflexivity].
Qed.

Lemma sem_pend_fields_program_context_error : forall environment critical sg call pevent timeout before
  eid observed code,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = Some code ->
  sem_pend_fields_program environment critical sg call pevent timeout
    before (encode_os_err_code code) before.
Proof.
  intros * Hnonzero Haddress Hid Hslot Herror.
  unfold sem_pend_fields_program, sem_pend_runtime_program.
  left; split.
  - eapply sem_pend_c_context_return; eassumption.
  - split; [right; exists eid; split; [exact Haddress|congruence]|reflexivity].
Qed.

Lemma sem_pend_fields_call_post_from_result : forall environment local critical sg call returned mask
  pevent timeout perr before current error X,
  sem_pend_fields_program environment critical sg call pevent timeout before error current ->
  sem_pend_fields_call_safe environment critical sg call pevent timeout before X ->
  kernel_stack_call_same_call returned call ->
  TT ** perr # UChar |-> error ** sem_pend_fields_closed environment local sg returned mask current |--
  sem_pend_fields_call_post environment critical sg call mask pevent timeout perr before X.
Proof.
  intros * Hresult Hsafe Hsame.
  pose proof (sem_query_safe_return _ _ _ _ _ Hresult Hsafe) as Hreturn.
  unfold sem_pend_fields_call_post; Exists returned current local error; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end);
  intros heap Hheap; exact (conj Hresult (conj Hreturn Hsame)).
Qed.

(** This covers both the positive-count and all real cleanup return codes.
    Their existing checkpoint producer is consumed unchanged, and the final
    current world comes from the actual generic Restore source/resources. *)
Lemma sem_pend_fields_call_post_from_restore : forall environment local critical sg context call mask
  pevent timeout perr before checkpoint error eid X,
  sem_pend_checkpoint_result (Some environment) critical sg context pevent timeout before error checkpoint ->
  pevent <> 0 -> pevent = event_addr sg eid ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  kernel_stack_call_same_call call context ->
  sem_pend_fields_call_safe environment critical sg context pevent timeout before X ->
  TT ** sem_pend_fields_phase_restore_output SemPendReturnPhase environment local critical sg call mask checkpoint **
    perr # UChar |-> error |--
  sem_pend_fields_call_post environment critical sg context mask pevent timeout perr before X.
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
  assert (Hresult : sem_pend_fields_program environment critical sg context pevent timeout before error current).
  { unfold sem_pend_fields_program, sem_pend_runtime_program.
    right; exists checkpoint, call, returned, eid; tauto. }
  assert (Hsame : kernel_stack_call_same_call returned context).
  { unfold kernel_stack_call_same_call in *; intuition congruence. }
  pose proof (sem_query_safe_return _ _ _ _ _ Hresult Hsafe) as Hreturn.
  unfold sem_pend_fields_call_post; Exists returned current local error; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end);
  intros heap Hheap; exact (conj Hresult (conj Hreturn Hsame)).
Qed.
