Require Import Coq.ZArith.ZArith.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_execution.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.

From SimpleC.SL Require Import SeparationLogic.
Local Open Scope sac_scope.

(** An owned caller has the existing CPU resource and the existing actual
    stack/architecture resource under ONE invocation/origin.  This does not
    manufacture either resource, does not identify OSTCBCur, and is not a
    new interpretation law for an arbitrary InterruptPlatformResources. *)
Definition kernel_call_execution_context (call : OsSchedCallContext)
  : KernelExecutionContext :=
  KernelCaller call.(os_sched_call_invocation) call.(os_sched_call_origin).

Definition kernel_execution_view_owned (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (call : OsExecutionView) (mask : Z)
  : Assertion :=
  interrupt_platform_running platform call.(os_execution_invocation)
    call.(os_execution_origin) mask ** os_execution_view_resources external call.

Definition kernel_call_execution_owned (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (call : OsSchedCallContext) (mask : Z)
  : Assertion :=
  interrupt_platform_running platform call.(os_sched_call_invocation)
    call.(os_sched_call_origin) mask ** os_sched_context_resources external call.

Lemma kernel_call_execution_owned_view_eq : forall external platform call mask,
  kernel_call_execution_owned external platform call mask =
  kernel_execution_view_owned external platform (os_sched_execution_view call) mask.
Proof. reflexivity. Qed.

(** Re-express the existing OSIntExit entry at the selected SAME execution
    interpretation. This is an equivalence of its original resource bundle,
    not a proof that SemPost or any Save/Restore call produces the bundle.
    The old acquire-safety obligation remains exactly where it was. *)
Lemma os_int_exit_pre_shared_execution_equiv :
  forall external platform source critical sg context mask before,
  os_int_exit_pre external platform (os_int_exit_shared_execution_port external source)
    critical sg context mask before --||--
  coq_prop (UCOS2_state_inv sg before /\
    os_int_exit_acquire_safety external (os_int_exit_shared_execution_port external source)
      critical sg context before) &&
  (kernel_execution_view_owned external platform (os_int_exit_execution_view context) mask **
   critical_region_outside critical sg context.(os_int_exit_invocation) before **
   unmap_table_rep sg).
Proof.
  intros; rewrite os_int_exit_pre_closed_equiv, os_int_exit_shared_context_resources_eq.
  unfold kernel_execution_view_owned.
  cbn [os_int_exit_execution_view os_execution_invocation os_execution_origin].
  split; entailer!.
Qed.

Lemma os_sched_c_return_execution_identity :
  forall external critical sg entry original returned final,
  os_sched_c_return external critical sg entry original returned final ->
  returned.(os_sched_call_invocation) = original.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = original.(os_sched_call_origin) /\
  returned.(os_sched_call_stack) = original.(os_sched_call_stack).
Proof.
  intros external critical sg entry original returned final Hreturn.
  unfold os_sched_c_return in Hreturn.
  destruct (os_sched_requests_switch entry).
  - destruct Hreturn as [installed [Hsource [Htrace [Harch [Hi [Ho [Hs Hrest]]]]]]].
    repeat split; assumption.
  - destruct Hreturn as [-> Hstate]; repeat split; reflexivity.
Qed.

(** Actual consumer/producer boundary: OS_Sched's checked ordinary Ensure
    supplies these resources together.  The returned stack is NOT inferred
    from a saved integer or an arbitrary resource trace.  Both the switch
    and no-switch C-return clauses preserve this source caller identity. *)
Lemma os_sched_post_returns_owned_execution :
  forall external platform critical sg original mask before,
  os_sched_post external platform critical sg original mask before |--
  EX entry returned final,
    coq_prop (critical_region_interval critical sg original.(os_sched_call_invocation)
        before entry /\ os_sched_c_return external critical sg entry original returned final /\
      kernel_call_execution_context returned = kernel_call_execution_context original) &&
    (kernel_call_execution_owned external platform returned mask **
     critical_region_outside critical sg returned.(os_sched_call_invocation) final **
     unmap_table_rep sg).
Proof.
  intros; unfold os_sched_post; Intros entry final returned.
  match goal with H : critical_region_interval _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hinterval Hreturn]
  end.
  destruct (os_sched_c_return_execution_identity external critical sg entry original
    returned final Hreturn) as [Hinv [Horigin Hstack]].
  Exists entry returned final.
  unfold kernel_call_execution_owned, kernel_call_execution_context.
  rewrite Hinv, Horigin; entailer!.
Qed.

(** The common Save precondition can consume the CPU/region components;
    the SAME owned continuation is retained explicitly.  This is a spatial
    rearrangement of a real OS_Sched return, not an extra Save postcondition.
    A port-specific entry/return producer is still needed to transport this
    owned frame through a switched acquisition. *)
Lemma kernel_call_execution_save_input :
  forall external platform critical sg call mask before,
  kernel_call_execution_owned external platform call mask **
    critical_region_outside critical sg call.(os_sched_call_invocation) before --||--
  interrupt_platform_running platform call.(os_sched_call_invocation)
    call.(os_sched_call_origin) mask **
    critical_region_outside critical sg call.(os_sched_call_invocation) before **
    os_sched_context_resources external call.
Proof. intros; unfold kernel_call_execution_owned; split; entailer!. Qed.

(** A restored frame retains the exact saved invocation, allocation origin
    and stack.  Only its owned byte snapshot changes to the bytes actually
    saved by the exception entry.  No resource follows from this record. *)
Definition os_int_exit_resumed_call (context : OsIntExitCallContext)
  : OsSchedCallContext :=
  {| os_sched_call_invocation :=
       context.(os_int_exit_interrupted_call).(os_sched_call_invocation);
     os_sched_call_origin :=
       context.(os_int_exit_interrupted_call).(os_sched_call_origin);
     os_sched_call_stack := context.(os_int_exit_interrupted_stack);
     os_sched_call_fragments := context.(os_int_exit_interrupted_fragments) |}.

Definition os_int_exit_interrupted_call_binding (context : OsIntExitCallContext) : Prop :=
  context.(os_int_exit_interrupted_call).(os_sched_call_stack) =
    context.(os_int_exit_interrupted_stack) /\
  context.(os_int_exit_interrupted_call).(os_sched_call_origin) =
    RunningInvocation context.(os_int_exit_interrupted_stack).(stackLeaseSlot)
      context.(os_int_exit_interrupted_stack).(stackLeaseGeneration).

Definition os_int_exit_resume_register_input (platform : InterruptPlatformResources)
  (port : OsIntExitPlatformResources) (context : OsIntExitCallContext) : Assertion :=
  interrupt_platform_running platform context.(os_int_exit_invocation)
    context.(os_int_exit_origin) 192 **
  port.(os_int_exit_handler_running) context **
  task_stack_fragments_rep context.(os_int_exit_interrupted_stack).(stackLeaseRegion)
    context.(os_int_exit_interrupted_fragments).

(** This wand is the LINEAR restoration capability emitted by the external
    exception-save segment below.  Its input is the handler's CPU/arch
    resources and the exact saved frame, not merely a slot/generation or a
    pure source label.  Applying it consumes the handler execution owner.

    The stronger architecture contract is explicit: saving the interrupted
    registers/PC/CPSR creates this capability, and restoring that same frame
    recovers its continuation and saved mask.  It says nothing about any OS
    state, current pointer, liveness, ready membership or invariant.  This
    is a modular port boundary, NOT an ARM implementation theorem. *)
Definition os_int_exit_continuation_escrow (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (port : OsIntExitPlatformResources)
  (context : OsIntExitCallContext) : Assertion :=
  ALL restored_pc,
    (coq_prop (port.(os_int_exit_frame_return_source) context restored_pc) &&
     os_int_exit_resume_register_input platform port context) -*
    (coq_prop (restored_pc = context.(os_int_exit_interrupted_pc)) &&
     kernel_call_execution_owned external platform (os_int_exit_resumed_call context)
       context.(os_int_exit_interrupted_mask)).

(** Source location: ARMv7-A exception entry, from the saved PC/CPSR pushes
    through the first-level handler-stack installation.  The pre owns the
    original CPU and real stack.  The post owns the handler CPU, the saved
    bytes, and its unique return capability; it does NOT retain the original
    running token.  The concrete SP/counter writes are separate kernel
    resource updates, subsequently parked by the proved producer below.
    Both PC observations refer to this same call-frame identity. *)
Definition os_int_exit_frame_save_pre (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (context : OsIntExitCallContext) : Assertion :=
  kernel_call_execution_owned external platform context.(os_int_exit_interrupted_call)
    context.(os_int_exit_interrupted_mask) **
  task_stack_fragments_rep context.(os_int_exit_handler_stack)
    context.(os_int_exit_handler_fragments).

Definition os_int_exit_frame_save_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (port : OsIntExitPlatformResources)
  (context : OsIntExitCallContext) : Assertion :=
  coq_prop (port.(os_int_exit_entry_source) context /\
    os_int_exit_interrupted_call_binding context) &&
  (interrupt_platform_running platform context.(os_int_exit_invocation)
     context.(os_int_exit_origin) 192 **
   os_int_exit_context_resources port context **
   task_stack_fragments_rep context.(os_int_exit_interrupted_stack).(stackLeaseRegion)
     context.(os_int_exit_interrupted_fragments) **
   os_int_exit_continuation_escrow external platform port context).

Lemma os_int_exit_resumed_call_execution_identity : forall context,
  kernel_call_execution_context (os_int_exit_resumed_call context) =
    kernel_call_execution_context context.(os_int_exit_interrupted_call).
Proof. reflexivity. Qed.

Lemma os_int_exit_consume_continuation_escrow : forall external platform port context restored_pc,
  port.(os_int_exit_frame_return_source) context restored_pc ->
  os_int_exit_resume_register_input platform port context **
    os_int_exit_continuation_escrow external platform port context |--
  coq_prop (restored_pc = context.(os_int_exit_interrupted_pc)) &&
    kernel_call_execution_owned external platform (os_int_exit_resumed_call context)
      context.(os_int_exit_interrupted_mask).
Proof.
  intros external platform port context restored_pc Hsource.
  assert (Hselect : os_int_exit_continuation_escrow external platform port context |--
    (coq_prop (port.(os_int_exit_frame_return_source) context restored_pc) &&
     os_int_exit_resume_register_input platform port context) -*
    (coq_prop (restored_pc = context.(os_int_exit_interrupted_pc)) &&
     kernel_call_execution_owned external platform (os_int_exit_resumed_call context)
       context.(os_int_exit_interrupted_mask))).
  { unfold os_int_exit_continuation_escrow; apply exp_allp_left.
    exists restored_pc; reflexivity. }
  sep_apply_l_atomic Hselect.
  eapply derivable1_trans with (y :=
    ((coq_prop (port.(os_int_exit_frame_return_source) context restored_pc) &&
      os_int_exit_resume_register_input platform port context) -*
     (coq_prop (restored_pc = context.(os_int_exit_interrupted_pc)) &&
      kernel_call_execution_owned external platform (os_int_exit_resumed_call context)
        context.(os_int_exit_interrupted_mask))) **
    (coq_prop (port.(os_int_exit_frame_return_source) context restored_pc) &&
      os_int_exit_resume_register_input platform port context));
    [|apply derivable1_wand_elim1].
  entailer!.
Qed.

(** OSIntExit's ordinary Ensure still owns the HANDLER execution resource.
    Open its exact outside representation only as a wrapper resource view;
    this theorem does not change the CPU mask or return into a task. *)
Lemma os_int_exit_post_exposes_wrapper_resources :
  forall platform port critical sg context mask before,
  os_int_exit_post platform port critical sg context mask before |--
  EX entry,
    coq_prop (os_int_exit_return_relation critical sg context before entry) &&
    (interrupt_platform_running platform context.(os_int_exit_invocation)
       context.(os_int_exit_origin) mask **
     UCOS2_inv sg (os_int_exit_ready_checkpoint before.(SchedState).(isRunning) entry) **
     os_int_exit_context_resources port context ** unmap_table_rep sg).
Proof.
  intros; unfold os_int_exit_post; Intros entry.
  Exists entry.
  unfold os_int_exit_outside_frame, os_int_exit_running, UCOS2_inv.
  rewrite critical_region_outside_without_running_rep, UCOS2_raw_rep_split_running.
  entailer!.
Qed.

(** Consume the very parked frame selected by the wrapper's pointer/SP
    reads.  Its bytes leave the global parked owner exactly once and remain
    available to the existing architecture restore contract.  In particular
    this operation does not create [os_sched_arch_running] or a task's CPU
    token from the handler's unrelated token. *)
Lemma os_int_exit_wrapper_take_destination_resources : forall sg state incoming fragments,
  state.(TskState).(parkedTaskStacks) (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), fragments) ->
  UCOS2_inv sg state |--
  UCOS2_inv sg (os_int_exit_wrapper_restored_state state incoming) **
    task_stack_fragments_rep incoming.(stackLeaseRegion) fragments.
Proof.
  intros sg state incoming fragments Hentry.
  rewrite UCOS2_inv_split_parked_stacks; Intros.
  sep_apply_l_atomic (store_parked_stacks_take_fragments _ _ _ Hentry).
  assert (Hconsistent : parked_stacks_consistent state.(TskState)
    (task_stack_take state.(TskState).(parkedTaskStacks) incoming)).
  { apply task_stack_take_preserves_consistency.
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in H; tauto. }
  unfold os_int_exit_wrapper_restored_state.
  sep_apply_l_atomic (UCOS2_inv_merge_updated_parked_stacks sg state _ H Hconsistent).
  entailer!.
Qed.

Definition os_int_exit_wrapper_restore_input (platform : InterruptPlatformResources)
  (port : OsIntExitPlatformResources) (sg : StableGlobVars)
  (context : OsIntExitCallContext) (mask : Z) (returned : UCOS2_Verify_State)
  (incoming : TaskStackLease) (fragments : TaskStackFragments) : Assertion :=
  interrupt_platform_running platform context.(os_int_exit_invocation)
    context.(os_int_exit_origin) mask **
  UCOS2_inv sg (os_int_exit_wrapper_restored_state returned incoming) **
  task_stack_fragments_rep incoming.(stackLeaseRegion) fragments **
  os_int_exit_context_resources port context ** unmap_table_rep sg.

Lemma os_int_exit_wrapper_destination_restore_input :
  forall external platform port sg context mask returned incoming sp fragments,
  os_int_exit_wrapper_destination external port context returned incoming sp fragments ->
  interrupt_platform_running platform context.(os_int_exit_invocation)
    context.(os_int_exit_origin) mask ** UCOS2_inv sg returned **
    os_int_exit_context_resources port context ** unmap_table_rep sg |--
  os_int_exit_wrapper_restore_input platform port sg context mask returned incoming fragments.
Proof.
  intros external platform port sg context mask returned incoming sp fragments
    [_ [_ [_ [Hparked Harch]]]].
  sep_apply_l_atomic (os_int_exit_wrapper_take_destination_resources sg returned
    incoming fragments Hparked).
  unfold os_int_exit_wrapper_restore_input; entailer!.
Qed.

Definition os_int_exit_wrapper_parked_state (state : UCOS2_Verify_State)
  (context : OsIntExitCallContext) : UCOS2_Verify_State :=
  replace_TskS (glob_task_set_parked_stacks state.(TskState)
    (task_stack_park_fragments state.(TskState).(parkedTaskStacks)
      context.(os_int_exit_interrupted_stack) context.(os_int_exit_interrupted_fragments))) state.

(** The external entry has already saved the frame and produced its escrow;
    the kernel's concrete TCB-SP/counter writes are at [state].  Parking now
    transfers those exact bytes into the one global map, while the escrow
    remains owned by the wrapper.  No CPU/stack token is created by this
    spatial producer. *)
Lemma os_int_exit_wrapper_entry_parks_saved_frame :
  forall external platform port sg context state,
  os_int_exit_interrupted_call_binding context ->
  os_sched_saved_stack_binding context.(os_int_exit_interrupted_call)
    context.(os_int_exit_interrupted_fragments) state ->
  os_int_exit_frame_save_post external platform port context ** UCOS2_inv sg state |--
  coq_prop (port.(os_int_exit_entry_source) context /\
    os_int_exit_interrupted_call_binding context) &&
  (interrupt_platform_running platform context.(os_int_exit_invocation)
     context.(os_int_exit_origin) 192 **
   os_int_exit_context_resources port context **
   UCOS2_inv sg (os_int_exit_wrapper_parked_state state context) **
   os_int_exit_continuation_escrow external platform port context).
Proof.
  intros external platform port sg context state Hidentity Hsaved.
  pose proof Hidentity as [Hstack Horigin].
  unfold os_int_exit_frame_save_post.
  rewrite UCOS2_inv_split_parked_stacks; Intros.
  assert (Hvalid : UCOS2_state_inv sg state) by assumption.
  assert (Hconsistent : parked_stacks_consistent state.(TskState)
    (task_stack_park_fragments state.(TskState).(parkedTaskStacks)
      context.(os_int_exit_interrupted_stack) context.(os_int_exit_interrupted_fragments))).
  { rewrite <- Hstack.
    eapply os_sched_park_saved_context_preserves_consistency; [|exact Hsaved].
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  assert (Hnone : state.(TskState).(parkedTaskStacks)
    (task_stack_key context.(os_int_exit_interrupted_stack)) = None).
  { rewrite <- Hstack; unfold os_sched_saved_stack_binding in Hsaved; tauto. }
  sep_apply_l_atomic (store_parked_stacks_park_fragments state.(TskState).(parkedTaskStacks)
    context.(os_int_exit_interrupted_stack) context.(os_int_exit_interrupted_fragments) Hnone).
  sep_apply_l_atomic (UCOS2_inv_merge_updated_parked_stacks sg state _ Hvalid Hconsistent).
  unfold os_int_exit_wrapper_parked_state; entailer!.
Qed.

Lemma os_int_exit_wrapper_parked_saved_binding : forall context state,
  (forall node,
    state.(TskState).(inUsedTaskStates) context.(os_int_exit_interrupted_stack).(stackLeaseSlot) = Some node ->
    node.(taskGeneration) = context.(os_int_exit_interrupted_stack).(stackLeaseGeneration) ->
    node.(tcbStkPtr) = context.(os_int_exit_interrupted_sp)) ->
  os_int_exit_saved_exception_binding context (os_int_exit_wrapper_parked_state state context).
Proof.
  intros context state Hsp; split.
  - apply task_stack_park_fragments_lookup.
  - exact Hsp.
Qed.

(** This uses the ordinary C Ensure, then the actual wrapper pointer/SP
    read, then a linear take, then the saved capability.  The original CPU
    owner is recovered only by consuming its entry-produced escrow.  The
    parked bytes cease to be globally owned before the same bytes become
    the running continuation's fragments.  Handler stack bytes are retained
    as a disjoint inactive frame, not discarded or called a task stack. *)
Lemma os_int_exit_post_resumes_original_owned_execution :
  forall external platform port critical sg context before restored_pc,
  port.(os_int_exit_frame_return_source) context restored_pc ->
  (forall entry,
    os_int_exit_return_relation critical sg context before entry ->
    os_int_exit_wrapper_destination external port context
      (os_int_exit_ready_checkpoint before.(SchedState).(isRunning) entry)
      context.(os_int_exit_interrupted_stack) context.(os_int_exit_interrupted_sp)
      context.(os_int_exit_interrupted_fragments)) ->
  os_int_exit_post platform port critical sg context 192 before **
    os_int_exit_continuation_escrow external platform port context |--
  EX entry,
    let returned := os_int_exit_ready_checkpoint before.(SchedState).(isRunning) entry in
    let final := os_int_exit_wrapper_restored_state returned context.(os_int_exit_interrupted_stack) in
    coq_prop (os_int_exit_wrapper_return_source external port critical sg context before
       context.(os_int_exit_interrupted_stack) context.(os_int_exit_interrupted_sp)
       context.(os_int_exit_interrupted_fragments) final /\
      kernel_call_execution_context (os_int_exit_resumed_call context) =
        kernel_call_execution_context context.(os_int_exit_interrupted_call) /\
      restored_pc = context.(os_int_exit_interrupted_pc)) &&
    (kernel_call_execution_owned external platform (os_int_exit_resumed_call context)
       context.(os_int_exit_interrupted_mask) **
     UCOS2_inv sg final **
     task_stack_fragments_rep context.(os_int_exit_handler_stack)
       context.(os_int_exit_handler_fragments) ** unmap_table_rep sg).
Proof.
  intros external platform port critical sg context before restored_pc Hpc Hdestination.
  sep_apply_l_atomic (os_int_exit_post_exposes_wrapper_resources platform port critical sg
    context 192 before); Intros entry.
  assert (Hreturn : os_int_exit_return_relation critical sg context before entry) by assumption.
  specialize (Hdestination entry Hreturn).
  sep_apply_l_atomic (os_int_exit_wrapper_destination_restore_input external platform port sg
    context 192 _ _ _ _ Hdestination).
  unfold os_int_exit_wrapper_restore_input, os_int_exit_context_resources.
  assert (Hresume : os_int_exit_resume_register_input platform port context **
    os_int_exit_continuation_escrow external platform port context |--
    coq_prop (restored_pc = context.(os_int_exit_interrupted_pc)) &&
    kernel_call_execution_owned external platform (os_int_exit_resumed_call context)
      context.(os_int_exit_interrupted_mask)).
  { apply os_int_exit_consume_continuation_escrow; exact Hpc. }
  unfold os_int_exit_resume_register_input in Hresume.
  sepcon_right_assoc.
  sep_apply_l_atomic Hresume; Intros.
  Exists entry.
  assert (Hsource : os_int_exit_wrapper_return_source external port critical sg context before
    context.(os_int_exit_interrupted_stack) context.(os_int_exit_interrupted_sp)
    context.(os_int_exit_interrupted_fragments)
    (os_int_exit_wrapper_restored_state
      (os_int_exit_ready_checkpoint before.(SchedState).(isRunning) entry)
      context.(os_int_exit_interrupted_stack))).
  { exists entry; split; [exact Hreturn|]. split; [exact Hdestination|reflexivity]. }
  entailer!.
Qed.

(** A call-stage fact about the actual OSTCBCur and a live TCB instance.
    This is neither a new kernel field nor a heap permission.  Readiness is
    deliberately absent: non-blocking MutexAccept only needs this live
    pointer, while blocking clients must separately justify their stage.
    In particular [task_invocation_active] alone does not imply this fact. *)
Definition task_current_at (state : UCOS2_Verify_State)
  (slot : TaskID) (generation : nat) : Prop :=
  state.(SchedState).(curTaskID) = Some slot /\
  exists node, state.(TskState).(inUsedTaskStates) slot = Some node /\
    node.(taskGeneration) = generation.

Lemma task_active_invocation_current_at : forall state invocation slot generation,
  task_invocation_active state.(TskState) invocation
    (RunningInvocation slot generation) ->
  state.(SchedState).(curTaskID) = Some slot ->
  task_current_at state slot generation.
Proof.
  intros state invocation slot generation [_ [_ Hlive]] Hcurrent.
  split; [exact Hcurrent|exact Hlive].
Qed.

(** The execution origin names the continuation actually running at this
    source cut.  Unlike invocation liveness, this relation follows the
    OSTCBCur writes performed by the scheduler/interrupt switch source.
    It deliberately says nothing about readiness or permanent priority. *)
Definition task_execution_current (origin : TaskInvocationOrigin)
  (state : UCOS2_Verify_State) : Prop :=
  match origin with
  | RunningInvocation slot _ => state.(SchedState).(curTaskID) = Some slot
  | _ => True
  end.

(** Source-labelled control steps, separate from the broad kernel-client
    resource trace.  A non-switching client must prove its concrete
    current-pointer frame. A switching step uses the existing ordered
    source relation and changes the executing origin to the stack it
    really installs. Thus other tasks may run in the middle of a trace;
    no requirement freezes OSTCBCur throughout the acquisition interval.

    The post-hook installation constructor is the remaining suffix when
    prefix selection, outgoing SP and the hook have already been tracked.
    It does not replay those earlier steps or assert eventual return.

    These constructors are model source steps, not additional fields in
    CriticalRegionResources or promises attached to OS_CPU_SR_Save. *)
Inductive task_execution_source_step
  (external : OsSchedExternalResources) (port : OsIntExitPlatformResources)
  (sg : StableGlobVars)
  : TaskInvocationOrigin -> UCOS2_Verify_State ->
    TaskInvocationOrigin -> UCOS2_Verify_State -> Prop :=
| TaskExecutionClientFrame : forall action origin before after,
    kernel_client_step action sg before after ->
    before.(SchedState).(curTaskID) = after.(SchedState).(curTaskID) ->
    task_execution_source_step external port sg origin before origin after
| TaskExecutionSchedulerTransfer : forall context entry sp saved hooked incoming resumed,
    os_sched_current_storage_binding sg context entry ->
    os_sched_requests_switch entry = true ->
    external.(os_sched_arch_save_source) context sp saved ->
    kernel_client_step external.(os_sched_hook_action) sg
      (os_sched_save_current_sp (os_sched_prefix_state entry)
        context.(os_sched_call_stack).(stackLeaseSlot) sp) hooked ->
    os_sched_destination_binding external context saved hooked incoming resumed ->
    task_execution_source_step external port sg
      context.(os_sched_call_origin) entry
      (RunningInvocation incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration))
      (os_sched_install_context context saved incoming hooked)
| TaskExecutionInterruptTransfer : forall origin context entry transfer,
    os_int_exit_transfer_source external port sg context entry transfer ->
    task_execution_source_step external port sg origin entry
      (RunningInvocation transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
        transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration))
      (os_int_exit_installed_state transfer)
| TaskExecutionInterruptWrapperReturn : forall critical origin context before incoming sp fragments after,
    os_int_exit_wrapper_return_source external port critical sg context before
      incoming sp fragments after ->
    task_execution_source_step external port sg origin before
      (RunningInvocation incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration)) after
| TaskExecutionSchedulerInstall : forall context saved hooked incoming resumed,
    os_sched_saved_stack_binding context saved hooked ->
    os_sched_destination_binding external context saved hooked incoming resumed ->
    task_execution_source_step external port sg
      context.(os_sched_call_origin) hooked
      (RunningInvocation incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration))
      (os_sched_install_context context saved incoming hooked).

Inductive task_execution_source_trace
  (external : OsSchedExternalResources) (port : OsIntExitPlatformResources)
  (sg : StableGlobVars)
  : TaskInvocationOrigin -> UCOS2_Verify_State ->
    TaskInvocationOrigin -> UCOS2_Verify_State -> Prop :=
| TaskExecutionTraceNil : forall origin state,
    task_execution_source_trace external port sg origin state origin state
| TaskExecutionTraceStep : forall first before middle transient last after,
    task_execution_source_step external port sg first before middle transient ->
    task_execution_source_trace external port sg middle transient last after ->
    task_execution_source_trace external port sg first before last after.

Lemma task_current_at_priority_in_range : forall sg state slot generation,
  UCOS2_state_inv sg state -> task_current_at state slot generation ->
  exists node, state.(TskState).(inUsedTaskStates) slot = Some node /\
    node.(taskGeneration) = generation /\ task_priority_in_range sg node.(curPrio).
Proof.
  intros sg state slot generation [_ [Htasks _]] [_ [node [Hnode Hgeneration]]].
  destruct Htasks as [_ [_ [_ [_ [_ [_ [_ [Hrange _]]]]]]]].
  exists node; split; [exact Hnode|]; split; [exact Hgeneration|].
  exact (Hrange slot node Hnode).
Qed.

(** The existing ghost-only call registration can obtain a fresh lifetime
    from a real current TCB; callers need not assume an arbitrary entry in
    the invocation map. UCOS2_inv_begin_task_invocation supplies the
    corresponding unchanged-physical-resource update. This lemma does NOT
    allocate, rename or reindex an opaque platform running resource. *)
Lemma task_current_at_begin_invocation : forall state slot generation,
  task_current_at state slot generation ->
  let registered := replace_TskS
    (task_begin_invocation (RunningInvocation slot generation) state.(TskState)) state in
  task_current_at registered slot generation /\
  task_invocation_active registered.(TskState)
    state.(TskState).(taskLifecycle).(taskNextInvocation)
    (RunningInvocation slot generation).
Proof.
  intros state slot generation [Hcurrent Hlive]; cbv zeta.
  split; [split; assumption|].
  apply task_begin_invocation_active; exact Hlive.
Qed.

(** The uninterrupted branch has a proved current-pointer frame for its
    actual client family.  Other task fields and all unrelated modules may
    change.  This theorem does NOT assert that arbitrary clients preserve
    OSTCBCur, and it is not a replacement for a context-switch endpoint. *)
Lemma kernel_client_trace_preserves_current_pointer :
  forall clients sg observer before stopped after,
  (forall action initial final, clients action ->
    kernel_client_step action sg initial final ->
    initial.(SchedState).(curTaskID) = final.(SchedState).(curTaskID)) ->
  kernel_client_trace clients sg observer before stopped after ->
  before.(SchedState).(curTaskID) = after.(SchedState).(curTaskID).
Proof.
  intros clients sg observer before stopped after Hframe Htrace.
  induction Htrace as
    [state|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH].
  - reflexivity.
  - rewrite (Hframe action before middle Hin Hstep); exact IH.
Qed.

Lemma task_creation_client_current_pointer_eq : forall action sg before after,
  kernel_client_step (task_creation_client action) sg before after ->
  before.(SchedState).(curTaskID) = after.(SchedState).(curTaskID).
Proof.
  intros action sg before after [_ [_ ->]]; destruct action; reflexivity.
Qed.

Lemma critical_region_uninterrupted_current_at :
  forall critical sg invocation slot generation before after,
  (forall action initial final, critical_region_clients critical action ->
    kernel_client_step action sg initial final ->
    initial.(SchedState).(curTaskID) = final.(SchedState).(curTaskID)) ->
  critical_region_interval critical sg invocation before after ->
  UCOS2_state_inv sg before ->
  task_invocation_active before.(TskState) invocation (RunningInvocation slot generation) ->
  before.(SchedState).(curTaskID) = Some slot -> task_current_at after slot generation.
Proof.
  intros critical sg invocation slot generation before after Hframe Hinterval
    Hvalid Hactive Hcurrent.
  destruct (critical_region_interval_transports_resources critical sg invocation
    before after Hinterval Hvalid) as [_ [_ Hlive]].
  apply task_active_invocation_current_at with (invocation := invocation).
  - apply Hlive; exact Hactive.
  - rewrite <- (kernel_client_trace_preserves_current_pointer
      (critical_region_clients critical) sg invocation before false after Hframe
      (critical_region_interval_raw_trace critical sg invocation before after Hinterval)).
    exact Hcurrent.
Qed.

(** A genuine later return to the original OS_Sched continuation already
    carries its source-level current-slot and lifetime binding.  Extracting
    them does not strengthen Save, filter the scheduler relation or assert
    that the task selected at the first switch is the returning task. *)
Lemma os_sched_original_resumed_current_at :
  forall external critical sg entry context returned final,
  context.(os_sched_call_origin) =
    RunningInvocation context.(os_sched_call_stack).(stackLeaseSlot)
      context.(os_sched_call_stack).(stackLeaseGeneration) ->
  os_sched_switch_outcome external critical sg entry context
    (OsSchedOriginalResumed returned final) ->
  task_current_at final context.(os_sched_call_stack).(stackLeaseSlot)
    context.(os_sched_call_stack).(stackLeaseGeneration).
Proof.
  intros external critical sg entry context returned final Horigin
    [installed [Hsource [Htrace [Harch [Hinvocation [HreturnedOrigin
      [Hstack [Hactive [Hcurrent Hparked]]]]]]]]].
  apply task_active_invocation_current_at with
    (invocation := context.(os_sched_call_invocation)); [|exact Hcurrent].
  rewrite <- Horigin; exact Hactive.
Qed.

(** OSIntCtxSw installs the TCB selected after the hook and restores its
    actual parked stack.  This is the destination's execution boundary,
    NOT a normal return to the ISR or to an arbitrary suspended caller. *)
Lemma os_int_exit_transfer_current_at : forall external port sg context entry transfer,
  os_int_exit_transfer_source external port sg context entry transfer ->
  task_current_at (os_int_exit_installed_state transfer)
    transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
    transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration).
Proof.
  intros external port sg context entry transfer
    [_ [_ [_ [_ [[Hselected [Hnode Hrest]] Hreturn]]]]].
  destruct Hnode as [node [Hnode [Hgeneration Hfields]]].
  destruct (os_int_exit_installed_current_eq transfer)
    as [Hcurrent [_ [Htasks _]]].
  split; [rewrite Hcurrent; exact Hselected|].
  exists node; split; [rewrite Htasks; exact Hnode|exact Hgeneration].
Qed.

Lemma task_execution_source_step_preserves_current :
  forall external port sg first before last after,
  task_execution_source_step external port sg first before last after ->
  task_execution_current first before -> task_execution_current last after.
Proof.
  intros external port sg first before last after Hsource.
  destruct Hsource as
    [action origin initial final Hstep Hframe
    |context entry sp saved hooked incoming resumed Hstorage Hrequest Hsave Hhook Hdestination
    |origin context entry transfer Htransfer
    |critical origin context before incoming sp fragments after Hwrapper
    |context saved hooked incoming resumed Hsaved Hdestination]; intro Hcurrent.
  - destruct origin; cbn in *; try exact I; congruence.
  - exact (proj1 Hdestination).
  - exact (proj1 (os_int_exit_transfer_current_at external port sg context
      entry transfer Htransfer)).
  - exact (proj1 (os_int_exit_wrapper_return_current external port critical sg
      context before incoming sp fragments after Hwrapper)).
  - exact (proj1 Hdestination).
Qed.

Lemma task_execution_source_trace_preserves_current :
  forall external port sg first before last after,
  task_execution_source_trace external port sg first before last after ->
  task_execution_current first before -> task_execution_current last after.
Proof.
  intros external port sg first before last after Htrace.
  induction Htrace as
    [origin state|first before middle transient last after Hstep Htail IH];
    intro Hcurrent.
  - exact Hcurrent.
  - apply IH; eapply task_execution_source_step_preserves_current; eassumption.
Qed.

Lemma task_execution_source_trace_trans :
  forall external port sg first before middle transient last after,
  task_execution_source_trace external port sg first before middle transient ->
  task_execution_source_trace external port sg middle transient last after ->
  task_execution_source_trace external port sg first before last after.
Proof.
  intros external port sg first before middle transient last after Hprefix Hsuffix.
  induction Hprefix as
    [origin state|first before middle transient next final Hstep Htail IH].
  - exact Hsuffix.
  - eapply TaskExecutionTraceStep; [exact Hstep|apply IH; exact Hsuffix].
Qed.

Lemma task_creation_client_execution_source :
  forall external port sg action origin before after,
  kernel_client_step (task_creation_client action) sg before after ->
  task_execution_source_step external port sg origin before origin after.
Proof.
  intros external port sg action origin before after Hstep.
  eapply TaskExecutionClientFrame; [exact Hstep|].
  eapply task_creation_client_current_pointer_eq; exact Hstep.
Qed.

Lemma kernel_client_current_frame_execution_source :
  forall external port clients sg observer origin before stopped after,
  (forall action initial final, clients action ->
    kernel_client_step action sg initial final ->
    initial.(SchedState).(curTaskID) = final.(SchedState).(curTaskID)) ->
  kernel_client_trace clients sg observer before stopped after ->
  task_execution_source_trace external port sg origin before origin after.
Proof.
  intros external port clients sg observer origin before stopped after Hframe Htrace.
  induction Htrace as
    [state|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH].
  - constructor.
  - eapply TaskExecutionTraceStep; [|exact IH].
    eapply TaskExecutionClientFrame; [exact Hstep|].
    eapply Hframe; eassumption.
Qed.

(** A registered action and its control source describe the SAME state
    edge.  This is stronger than independently existential resource/control
    paths with equal endpoints.  Stops, task actors and Event actors remain
    exactly those of the registered action.  No certificate claims that all
    clients frame OSTCBCur; a transfer uses its actual ordered source. *)
Inductive kernel_client_task_source_trace
  (external : OsSchedExternalResources) (port : OsIntExitPlatformResources)
  (clients : KernelClientAction -> Prop) (sg : StableGlobVars)
  (observer : nat) (event_observer : option nat)
  : TaskInvocationOrigin -> UCOS2_Verify_State -> bool ->
    TaskInvocationOrigin -> UCOS2_Verify_State -> Prop :=
| KernelClientTaskSourceNil : forall origin state,
    kernel_client_task_source_trace external port clients sg observer event_observer
      origin state false origin state
| KernelClientTaskSourceStep : forall action first before middle transient last after stopped,
    clients action -> kernel_client_actor action <> Some observer ->
    (forall invocation, event_observer = Some invocation ->
      kernel_client_event_actor action <> Some invocation) ->
    kernel_client_step action sg before transient ->
    task_execution_source_step external port sg first before middle transient ->
    kernel_client_task_source_trace external port clients sg observer event_observer
      middle transient stopped last after ->
    kernel_client_task_source_trace external port clients sg observer event_observer
      first before (orb (kernel_client_stops action observer) stopped) last after.

Lemma kernel_client_task_source_trace_erases :
  forall external port clients sg observer event_observer first before stopped last after,
  kernel_client_task_source_trace external port clients sg observer event_observer
    first before stopped last after ->
  kernel_client_resource_trace clients sg observer event_observer before stopped after /\
  task_execution_source_trace external port sg first before last after.
Proof.
  intros external port clients sg observer event_observer first before stopped last after Htrace.
  induction Htrace as [origin state|action first before middle transient last after stopped
    Hin Hforeign Hevent Hstep Hsource Htail [IHresource IHsource]].
  - split; constructor.
  - split.
    + eapply KernelClientTraceStep; eassumption.
    + eapply TaskExecutionTraceStep; eassumption.
Qed.

Inductive kernel_resumption_task_source_trace
  (external : OsSchedExternalResources) (port : OsIntExitPlatformResources)
  (clients : KernelClientAction -> Prop) (sg : StableGlobVars)
  (observer : nat) (event_observer : option nat)
  : TaskInvocationOrigin -> UCOS2_Verify_State -> bool ->
    TaskInvocationOrigin -> UCOS2_Verify_State -> Prop :=
| KernelResumptionTaskSourceNil : forall origin state,
    kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin state false origin state
| KernelResumptionTaskSourceSegment :
    forall first before stopped1 middle transient stopped2 last after,
    kernel_client_task_source_trace external port clients sg observer event_observer
      first before stopped1 middle transient ->
    timer_public_trace sg before.(TimerState) transient.(TimerState) ->
    kernel_resumption_task_source_trace external port clients sg observer event_observer
      middle transient stopped2 last after ->
    kernel_resumption_task_source_trace external port clients sg observer event_observer
      first before (orb stopped1 stopped2) last after.

Lemma kernel_resumption_task_source_trace_erases :
  forall external port clients sg observer event_observer first before stopped last after,
  kernel_resumption_task_source_trace external port clients sg observer event_observer
    first before stopped last after ->
  kernel_resumption_resource_trace clients sg observer event_observer before stopped after /\
  task_execution_source_trace external port sg first before last after.
Proof.
  intros external port clients sg observer event_observer first before stopped last after Htrace.
  induction Htrace as [origin state|first before stopped1 middle transient stopped2 last after
    Hsegment Htimer Htail [IHresource IHsource]].
  - split; constructor.
  - destruct (kernel_client_task_source_trace_erases external port clients sg observer
      event_observer first before stopped1 middle transient Hsegment) as [Hresource Hsource].
    split.
    + eapply KernelResumptionTraceSegment; eassumption.
    + eapply task_execution_source_trace_trans; eassumption.
Qed.

Lemma kernel_client_current_frame_registered_source :
  forall external port clients sg observer event_observer origin before stopped after,
  (forall action initial final, clients action ->
    kernel_client_step action sg initial final ->
    initial.(SchedState).(curTaskID) = final.(SchedState).(curTaskID)) ->
  kernel_client_resource_trace clients sg observer event_observer before stopped after ->
  kernel_client_task_source_trace external port clients sg observer event_observer
    origin before stopped origin after.
Proof.
  intros external port clients sg observer event_observer origin before stopped after Hframe Htrace.
  induction Htrace as [state|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH].
  - constructor.
  - eapply KernelClientTaskSourceStep; try eassumption.
    eapply TaskExecutionClientFrame; [exact Hstep|].
    apply (Hframe action before middle Hin Hstep).
Qed.

Lemma kernel_resumption_current_frame_registered_source :
  forall external port clients sg observer event_observer origin before stopped after,
  (forall action initial final, clients action ->
    kernel_client_step action sg initial final ->
    initial.(SchedState).(curTaskID) = final.(SchedState).(curTaskID)) ->
  kernel_resumption_resource_trace clients sg observer event_observer before stopped after ->
  kernel_resumption_task_source_trace external port clients sg observer event_observer
    origin before stopped origin after.
Proof.
  intros external port clients sg observer event_observer origin before stopped after Hframe Htrace.
  induction Htrace as
    [state|action before middle after stopped Hin Hforeign Hevent Hstep Htimer Htail IH
    |before stopped1 middle stopped2 after Hsegment Htimer Htail IH].
  - constructor.
  - eapply KernelResumptionTaskSourceSegment; [|exact Htimer|exact IH].
    replace (kernel_client_stops action observer) with
      (orb (kernel_client_stops action observer) false) by apply Bool.orb_false_r.
    eapply KernelClientTaskSourceStep; try eassumption; [|constructor].
    eapply TaskExecutionClientFrame; [exact Hstep|].
    apply (Hframe action before middle Hin Hstep).
  - eapply KernelResumptionTaskSourceSegment; [|exact Htimer|exact IH].
    eapply kernel_client_current_frame_registered_source; eassumption.
Qed.

(** A normal-return cut carries both the already registered resource trace
    and its control-flow source.  Intermediate source cuts may belong to
    different tasks. Requiring the final origin to be the invoking task
    selects a return to this continuation, not a ban on preemption.

    This relation must be supplied by an actual source/continuation binding;
    a generic critical_region_interval does NOT imply it. It is deliberately
    not installed as an extra field or an unproved universal guarantee in
    the shared CPU/CSL resources. *)
Definition critical_region_task_source_interval
  (external : OsSchedExternalResources) (port : OsIntExitPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (slot : TaskID) (generation : nat)
  (before after : UCOS2_Verify_State) : Prop :=
  kernel_resumption_task_source_trace external port critical.(critical_region_clients)
    sg invocation None (RunningInvocation slot generation) before false
    (RunningInvocation slot generation) after.

Lemma critical_region_task_source_interval_current_at :
  forall external port critical sg invocation slot generation before after,
  critical_region_task_source_interval external port critical sg invocation
    slot generation before after ->
  UCOS2_state_inv sg before ->
  task_invocation_active before.(TskState) invocation (RunningInvocation slot generation) ->
  before.(SchedState).(curTaskID) = Some slot -> task_current_at after slot generation.
Proof.
  intros external port critical sg invocation slot generation before after
    Hregistered Hvalid Hactive Hcurrent.
  destruct (kernel_resumption_task_source_trace_erases external port
    critical.(critical_region_clients) sg invocation None
    (RunningInvocation slot generation) before false
    (RunningInvocation slot generation) after Hregistered) as [Hinterval Hsource].
  destruct (critical_region_interval_transports_resources critical sg invocation
    before after Hinterval Hvalid) as [_ [_ Hlive]].
  apply task_active_invocation_current_at with (invocation := invocation).
  - apply Hlive; exact Hactive.
  - exact (task_execution_source_trace_preserves_current external port sg
      (RunningInvocation slot generation) before (RunningInvocation slot generation)
      after Hsource Hcurrent).
Qed.

Lemma critical_region_uninterrupted_task_source_interval :
  forall external port critical sg invocation slot generation before after,
  (forall action initial final, critical_region_clients critical action ->
    kernel_client_step action sg initial final ->
    initial.(SchedState).(curTaskID) = final.(SchedState).(curTaskID)) ->
  critical_region_interval critical sg invocation before after ->
  critical_region_task_source_interval external port critical sg invocation
    slot generation before after.
Proof.
  intros external port critical sg invocation slot generation before after Hframe Hinterval.
  eapply kernel_resumption_current_frame_registered_source; eassumption.
Qed.

(** A task-source cut is a fact about a real executing continuation.  It is
    not derived from an arbitrary CPU token.  The call producer supplies the
    original invocation registration; a source-labelled interval transports
    its liveness.  Suspension, delay, readiness and Idle are deliberately
    not tested here. *)
Definition kernel_call_task_source (call : OsSchedCallContext)
  (state : UCOS2_Verify_State) : Prop :=
  call.(os_sched_call_origin) =
    RunningInvocation call.(os_sched_call_stack).(stackLeaseSlot)
      call.(os_sched_call_stack).(stackLeaseGeneration) /\
  task_invocation_active state.(TskState) call.(os_sched_call_invocation)
    call.(os_sched_call_origin) /\
  task_execution_current call.(os_sched_call_origin) state.

(** Normal return of the COMMON Save execution boundary.  The saved mask is
    observed at the CPU instruction; the environment/control trace is the
    SAME registered trace, with its actor, Event-actor, timer and stop data.
    Its final continuation is the original invocation.  Intermediate cuts
    can execute other tasks and either form of interrupt return.

    This is the source-facing refinement of the old broad region interval,
    not a consequence asserted for every old interval.  Its resource post
    below must be emitted by actual source-bound entry/return producers. *)
Definition kernel_call_save_source (external : OsSchedExternalResources)
  (port : OsIntExitPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (original returned : OsSchedCallContext)
  (mask saved : Z) (before entry : UCOS2_Verify_State) : Prop :=
  kernel_resumption_task_source_trace external port critical.(critical_region_clients)
    sg original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    before false returned.(os_sched_call_origin) entry /\
  returned.(os_sched_call_invocation) = original.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = original.(os_sched_call_origin) /\
  returned.(os_sched_call_stack) = original.(os_sched_call_stack) /\
  interrupt_saved_value mask saved.

Lemma kernel_call_save_source_region_interval :
  forall external port critical sg original returned mask saved before entry,
  kernel_call_save_source external port critical sg original returned mask saved before entry ->
  critical_region_interval critical sg original.(os_sched_call_invocation) before entry.
Proof.
  intros external port critical sg original returned mask saved before entry [Htrace Hrest].
  exact (proj1 (kernel_resumption_task_source_trace_erases external port
    critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
    original.(os_sched_call_origin) before false returned.(os_sched_call_origin) entry Htrace)).
Qed.

Lemma kernel_call_save_source_preserves_task_source :
  forall external port critical sg original returned mask saved before entry,
  UCOS2_state_inv sg before -> kernel_call_task_source original before ->
  kernel_call_save_source external port critical sg original returned mask saved before entry ->
  kernel_call_task_source returned entry.
Proof.
  intros external port critical sg original returned mask saved before entry Hvalid
    [Horigin [Hactive Hcurrent]] Hsource.
  pose proof Hsource as [Htrace [Hi [Ho [Hs Hmask]]]].
  pose proof (kernel_call_save_source_region_interval external port critical sg
    original returned mask saved before entry Hsource) as Hinterval.
  destruct (critical_region_interval_transports_resources critical sg
    original.(os_sched_call_invocation) before entry Hinterval Hvalid) as [_ [_ Hlive]].
  destruct (kernel_resumption_task_source_trace_erases external port
    critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
    original.(os_sched_call_origin) before false returned.(os_sched_call_origin) entry Htrace)
    as [_ Hcontrol].
  split; [rewrite Ho, Hs; exact Horigin|].
  split.
  - rewrite Hi, Ho; apply Hlive; exact Hactive.
  - eapply task_execution_source_trace_preserves_current; eassumption.
Qed.

Lemma kernel_call_task_source_current_at : forall call state,
  kernel_call_task_source call state ->
  task_current_at state call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration).
Proof.
  intros call state [Horigin [Hactive Hcurrent]].
  rewrite Horigin in Hactive, Hcurrent.
  eapply task_active_invocation_current_at; eassumption.
Qed.

(** This is the actual switched ordinary C-return branch, not the first
    installed destination. Its original-invocation registration and current
    pointer already come from [os_sched_switch_outcome]; the source origin
    comes from the existing outgoing-storage safety obligation. No task
    source fact is asserted for an arbitrary no-switch acquisition. *)
Lemma os_sched_c_return_task_source_on_switch :
  forall external critical sg entry original returned final,
  os_sched_switch_input external sg original entry ->
  os_sched_requests_switch entry = true ->
  os_sched_c_return external critical sg entry original returned final ->
  kernel_call_task_source returned final.
Proof.
  intros external critical sg entry original returned final
    [[Horigin Hstorage] Hinput] Hrequest Hreturn.
  unfold os_sched_c_return in Hreturn; rewrite Hrequest in Hreturn.
  destruct Hreturn as [installed [Hswitch [Htrace [Harch [Hi [Ho [Hs
    [Hactive [Hcurrent Hparked]]]]]]]]].
  unfold kernel_call_task_source; rewrite Hi, Ho, Hs.
  split; [exact Horigin|]. split; [exact Hactive|].
  unfold task_execution_current; rewrite Horigin; exact Hcurrent.
Qed.

Definition kernel_call_save_pre (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (call : OsSchedCallContext) (mask : Z)
  (before : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg before /\ kernel_call_task_source call before) &&
  (kernel_call_execution_owned external platform call mask **
   critical_region_outside critical sg call.(os_sched_call_invocation) before).

Definition kernel_call_save_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (port : OsIntExitPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (original : OsSchedCallContext) (mask saved : Z)
  (before : UCOS2_Verify_State) : Assertion :=
  EX returned entry,
    coq_prop (kernel_call_save_source external port critical sg original returned
      mask saved before entry) &&
    (critical_region_masked platform critical sg returned.(os_sched_call_invocation)
       returned.(os_sched_call_origin) saved entry **
     os_sched_context_resources external returned ** UCOS2_raw_rep sg entry).

(** An instantaneous call-site handoff from an actual returned execution
    and its current full heap.  This uses the existing outside/raw contract
    in its packaging direction; it is NOT an unmasked execution rule and
    does not claim that an old heap remains unchanged until Save returns.
    The IRQ return producer supplies owned execution to the actual consumer
    after consuming the saved continuation exactly once. *)
Lemma kernel_call_owned_heap_save_input :
  forall external platform critical sg call mask state,
  kernel_call_task_source call state ->
  kernel_call_execution_owned external platform call mask ** UCOS2_inv sg state |--
  kernel_call_save_pre external platform critical sg call mask state.
Proof.
  intros external platform critical sg call mask state Hsource.
  unfold kernel_call_save_pre, critical_region_outside.
  rewrite critical_region_outside_without_running_rep.
  rewrite <- UCOS2_raw_rep_split_running.
  unfold UCOS2_inv; entailer!.
Qed.

Lemma kernel_call_save_post_exposes_task_source :
  forall external platform port critical sg original mask saved before,
  UCOS2_state_inv sg before -> kernel_call_task_source original before ->
  kernel_call_save_post external platform port critical sg original mask saved before |--
  EX returned entry,
    coq_prop (kernel_call_save_source external port critical sg original returned
      mask saved before entry /\ kernel_call_task_source returned entry) &&
    (critical_region_masked platform critical sg returned.(os_sched_call_invocation)
       returned.(os_sched_call_origin) saved entry **
     os_sched_context_resources external returned ** UCOS2_inv sg entry).
Proof.
  intros external platform port critical sg original mask saved before Hvalid Hcaller.
  unfold kernel_call_save_post; Intros returned entry.
  assert (Hsource : kernel_call_save_source external port critical sg original returned
    mask saved before entry) by assumption.
  pose proof (kernel_call_save_source_preserves_task_source external port critical sg
    original returned mask saved before entry Hvalid Hcaller Hsource) as Hcurrent.
  pose proof (kernel_call_save_source_region_interval external port critical sg
    original returned mask saved before entry Hsource) as Hinterval.
  sep_apply_l_atomic (critical_region_interval_open_invariant critical sg
    original.(os_sched_call_invocation) before entry Hinterval Hvalid).
  Exists returned entry; entailer!.
Qed.

(** Only a hook whose actual source step leaves the selected checkpoint
    unchanged can use this consequence.  Generic hooks may alter ready
    membership or physical high caches; destination binding alone does not
    imply readiness.  No assumption is added to the platform resources. *)
Lemma os_int_exit_unchanged_hook_destination_ready :
  forall external port sg handler entry transfer,
  UCOS2_state_inv sg entry -> entry.(SchedState).(isRunning) = true ->
  os_int_exit_transfer_source external port sg handler entry transfer ->
  transfer.(os_int_exit_hooked_state) = os_int_exit_ready_checkpoint true entry ->
  exists node,
    sched_current_ready_at (os_int_exit_installed_state transfer).(TskState)
      (os_int_exit_installed_state transfer).(SchedState)
      transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) node /\
    node.(taskGeneration) = transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration).
Proof.
  intros external port sg handler entry transfer Hvalid Hrunning Hsource Hhook.
  pose proof Hsource as [Hswitch [_ [_ [_ [Hdestination _]]]]].
  pose proof Hvalid as [_ [_ [[Hready Hmetadata] _]]].
  assert (Hselection : os_sched_selection_enabled (os_int_exit_after_nesting entry) = true).
  { apply os_sched_requests_switch_iff in Hswitch; exact (proj1 Hswitch). }
  assert (Hhigh : sched_high_ready_consistency
    transfer.(os_int_exit_hooked_state).(TskState)
    transfer.(os_int_exit_hooked_state).(SchedState)).
  { rewrite Hhook; apply os_sched_ready_checkpoint_high_consistency with (sg := sg);
      assumption. }
  destruct Hdestination as [Hselected [[node [Hnode [Hgeneration [Hprio Hsp]]]] Hrest]].
  assert (Hnonempty : transfer.(os_int_exit_hooked_state).(SchedState).(readyList) <> nil).
  { intro Hempty; unfold sched_high_ready_consistency in Hhigh;
      rewrite Hempty in Hhigh; destruct Hhigh as [Hnone _]; congruence. }
  assert (Hboundary : sched_task_call_boundary
    transfer.(os_int_exit_hooked_state).(TskState)
    (sched_install_selected transfer.(os_int_exit_hooked_state).(SchedState))).
  { apply sched_install_selected_task_boundary with (sg := sg); try assumption.
    - pose proof (os_int_exit_ready_checkpoint_preserves_validity sg true entry Hvalid)
        as [_ [_ [[HreadyNow _] _]]]; rewrite Hhook; exact HreadyNow.
    - rewrite Hhook; exact (eq_trans
        (proj2 (proj2 (os_int_exit_checkpoint_current_frame true entry))) Hrunning). }
  destruct Hboundary as [_ [tid [current [Hcurrent [Htid HreadyNow]]]]].
  change (transfer.(os_int_exit_hooked_state).(SchedState).(highRdyTid) = Some tid) in Htid.
  assert (tid = transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)) by congruence.
  subst tid; assert (current = node) by congruence; subst current.
  exists node; split; [|exact Hgeneration].
  unfold sched_current_ready_at; cbn [os_int_exit_installed_state replace_TskS replace_SchedS
    TskState SchedState glob_task_set_parked_stacks inUsedTaskStates].
  split; [exact Hnode|]. split; [exact Htid|exact HreadyNow].
Qed.

Lemma kernel_resumption_task_source_trace_trans :
  forall external port clients sg observer event_observer first before stopped1
    middle transient stopped2 last after,
  kernel_resumption_task_source_trace external port clients sg observer event_observer
    first before stopped1 middle transient ->
  kernel_resumption_task_source_trace external port clients sg observer event_observer
    middle transient stopped2 last after ->
  kernel_resumption_task_source_trace external port clients sg observer event_observer
    first before (orb stopped1 stopped2) last after.
Proof.
  intros external port clients sg observer event_observer first before stopped1 middle
    transient stopped2 last after Hprefix Hsuffix.
  induction Hprefix as [origin state|first before stop1 middle transient stop2 next final
    Hsegment Htimer Htail IH].
  - exact Hsuffix.
  - rewrite <- Bool.orb_assoc.
    eapply KernelResumptionTaskSourceSegment; [exact Hsegment|exact Htimer|].
    apply IH; exact Hsuffix.
Qed.

Lemma kernel_client_task_source_trace_inclusion :
  forall external port clients registered sg observer event_observer first before stopped last after,
  (forall action, clients action -> registered action) ->
  kernel_client_task_source_trace external port clients sg observer event_observer
    first before stopped last after ->
  kernel_client_task_source_trace external port registered sg observer event_observer
    first before stopped last after.
Proof.
  intros * Hinclude Htrace; induction Htrace.
  - constructor.
  - eapply KernelClientTaskSourceStep; eauto.
Qed.

Lemma kernel_resumption_task_source_trace_inclusion :
  forall external port clients registered sg observer event_observer first before stopped last after,
  (forall action, clients action -> registered action) ->
  kernel_resumption_task_source_trace external port clients sg observer event_observer
    first before stopped last after ->
  kernel_resumption_task_source_trace external port registered sg observer event_observer
    first before stopped last after.
Proof.
  intros * Hinclude Htrace; induction Htrace.
  - constructor.
  - eapply KernelResumptionTaskSourceSegment; [|eassumption|exact IHHtrace].
    eapply kernel_client_task_source_trace_inclusion; eassumption.
Qed.

(** Join the actual last registered transfer to the preceding registered
    control trace.  The action and the transfer share the SAME edge; no
    unrelated trace with merely matching endpoints is substituted.  A
    stopped invocation has no such false-stop normal-return constructor. *)
Lemma kernel_call_save_source_last_interrupt_transfer :
  forall external port critical sg original returned mask saved before
    origin irq_entry handler transfer action,
  kernel_resumption_task_source_trace external port critical.(critical_region_clients)
    sg original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    before false origin irq_entry ->
  critical.(critical_region_clients) action ->
  kernel_client_actor action <> Some original.(os_sched_call_invocation) ->
  kernel_client_stops action original.(os_sched_call_invocation) = false ->
  kernel_client_step action sg irq_entry (os_int_exit_installed_state transfer) ->
  timer_public_trace sg irq_entry.(TimerState) (os_int_exit_installed_state transfer).(TimerState) ->
  os_int_exit_transfer_source external port sg handler irq_entry transfer ->
  returned.(os_sched_call_origin) = RunningInvocation
    transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
    transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration) ->
  returned.(os_sched_call_invocation) = original.(os_sched_call_invocation) ->
  returned.(os_sched_call_origin) = original.(os_sched_call_origin) ->
  returned.(os_sched_call_stack) = original.(os_sched_call_stack) ->
  interrupt_saved_value mask saved ->
  kernel_call_save_source external port critical sg original returned mask saved
    before (os_int_exit_installed_state transfer).
Proof.
  intros external port critical sg original returned mask saved before origin irq_entry
    handler transfer action Hprefix Hin Hforeign Hstop Hstep Htimer Htransfer
    Hreturned Hi Ho Hstack Hsaved.
  assert (Hlast : kernel_resumption_task_source_trace external port
    critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
    origin irq_entry false returned.(os_sched_call_origin) (os_int_exit_installed_state transfer)).
  { rewrite Hreturned.
    replace false with (orb false false) by reflexivity.
    eapply KernelResumptionTaskSourceSegment; [|exact Htimer|constructor].
    rewrite <- (Bool.orb_false_r (kernel_client_stops action original.(os_sched_call_invocation)))
      in Hstop.
    rewrite <- Hstop.
    eapply KernelClientTaskSourceStep; try eassumption.
    - intros invocation Hnone; discriminate.
    - eapply TaskExecutionInterruptTransfer; exact Htransfer.
    - constructor. }
  split; [|exact (conj Hi (conj Ho (conj Hstack Hsaved)))].
  exact (kernel_resumption_task_source_trace_trans external port
    critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
    original.(os_sched_call_origin) before false origin irq_entry false
    returned.(os_sched_call_origin) (os_int_exit_installed_state transfer) Hprefix Hlast).
Qed.
