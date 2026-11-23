Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The private ECB's CURRENT initialized/undefined image is owned, not
    recovered from an existential lookup in the logical state. The two
    immutable indices are the Event allocation invocation and generation;
    neither is silently identified with a Task invocation. This predicate
    does not own a Queue's separate QCB or message array. Those resources
    must be carried by their own actual source owner.

    No selected/full profile is hard-coded: the concrete Event image and
    header configuration already parameterize event_private_storage_rep. *)
Definition event_creator_private_rep sg eid invocation generation state : Assertion :=
  EX allocation,
    coq_prop (state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
      allocation.(eventPrivateInvocation) = invocation /\
      allocation.(eventPrivateGeneration) = generation) &&
    event_private_storage_rep sg eid allocation.

Lemma event_creator_private_rep_from_allocation : forall sg eid allocation state,
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_private_storage_rep sg eid allocation |--
    event_creator_private_rep sg eid allocation.(eventPrivateInvocation)
      allocation.(eventPrivateGeneration) state.
Proof. intros; unfold event_creator_private_rep; Exists allocation; entailer!. Qed.

Lemma event_creator_private_rep_same_allocation : forall sg eid invocation generation state allocation,
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_creator_private_rep sg eid invocation generation state |--
    coq_prop (allocation.(eventPrivateInvocation) = invocation /\
      allocation.(eventPrivateGeneration) = generation) && event_private_storage_rep sg eid allocation.
Proof.
  intros sg eid invocation generation state allocation Hget heap
    [current [[Hcurrent [Hinvocation Hgeneration]] Hbytes]].
  assert (current = allocation) by congruence; subst current.
  split; [split; assumption|exact Hbytes].
Qed.

Lemma event_creator_private_rep_event_eq : forall sg eid invocation generation before after,
  before.(EventState) = after.(EventState) ->
  event_creator_private_rep sg eid invocation generation before =
    event_creator_private_rep sg eid invocation generation after.
Proof. intros; unfold event_creator_private_rep; rewrite H; reflexivity. Qed.

(** This split/merge is at one real heap cut only. It supplies no frame
    rule across OS_CPU_SR_Restore, OS_Sched, or an arbitrary client body. *)
Lemma event_creator_stack_inv_split_private : forall external platform port
  (abi : Armv7aContinuationABI external platform port) resources sg active state eid invocation generation,
  kernel_stack_inv abi
    (fun sg state => resources sg state ** event_creator_private_rep sg eid invocation generation state)
    sg active state --||--
  kernel_stack_inv abi resources sg active state **
    event_creator_private_rep sg eid invocation generation state.
Proof. intros; apply kernel_stack_inv_split_resources. Qed.

(** Exact last CPU exchange AFTER the real source has taken the selected
    continuation and established [resources] at [restored]. Only that
    already-existing ABI instruction is framed here; an intervening
    creator may not be replaced by this theorem. The current image is
    reindexed across the actual parked-map take, which changes Task only.
    Its Event invocation/generation and bytes are retained exactly once.
    The producer of the full strong map and of this selected descriptor
    is still required; this consumer does not upgrade weak capsules. *)
Lemma event_creator_wrapper_return_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) resources sg active state incoming
  eid invocation generation handler saved call before after (frame : Assertion),
  let restored := os_int_exit_wrapper_restored_state state incoming in
  saved.(armv7a_continuation_call) = Some call ->
  armv7a_continuation_restore_reads saved before ->
  (interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi saved **
    (kernel_stack_inv abi resources sg active restored **
      event_creator_private_rep sg eid invocation generation state ** frame)) before ->
  armv7a_restore_transition abi handler saved before after ->
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (kernel_call_execution_owned external platform (armv7a_continuation_resumed_call saved call)
      (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
    (kernel_stack_inv abi
      (fun sg state => resources sg state ** event_creator_private_rep sg eid invocation generation state)
      sg active restored ** frame)) after.
Proof.
  intros external platform port abi resources sg active state incoming eid invocation generation
    handler saved call before after frame restored Hcall Hreads Hpre Hrun.
  destruct (armv7a_restore_call_resources external platform port abi handler saved call _ before after
    Hcall Hreads Hpre Hrun) as [Hmemory Hpost].
  split; [exact Hmemory|].
  assert (Hsame : event_creator_private_rep sg eid invocation generation state =
    event_creator_private_rep sg eid invocation generation restored).
  { apply event_creator_private_rep_event_eq; reflexivity. }
  rewrite Hsame in Hpost.
  match type of Hpost with ?P after =>
    match goal with |- ?Q after => assert (Hclose : P |-- Q) end
  end.
  { unfold kernel_stack_inv; entailer!. }
  exact (Hclose after Hpost).
Qed.
