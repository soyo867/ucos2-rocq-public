Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The descriptor is built from the actual interrupted call and the saved
    PC/CPSR/SP/frame observations. It allocates no OS field and grants no
    ownership. The external save/restore contract must supply the resources.
    This explicit constructor prevents unrelated stack/call identities from
    being silently combined at the first-level IRQ entry. *)
Definition armv7a_irq_saved_call_context (handler : nat)
  (handler_origin : TaskInvocationOrigin) (handler_stack : TaskStackRegion)
  (handler_fragments : TaskStackFragments) (original : OsSchedCallContext)
  (pc mask sp : Z) (saved : TaskStackFragments) : OsIntExitCallContext :=
  {| os_int_exit_invocation := handler;
     os_int_exit_origin := handler_origin;
     os_int_exit_handler_stack := handler_stack;
     os_int_exit_handler_fragments := handler_fragments;
     os_int_exit_interrupted_stack := original.(os_sched_call_stack);
     os_int_exit_interrupted_sp := sp;
     os_int_exit_interrupted_fragments := saved;
     os_int_exit_interrupted_call := original;
     os_int_exit_interrupted_pc := pc;
     os_int_exit_interrupted_mask := mask |}.

Definition armv7a_irq_handler_frame (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (port : OsIntExitPlatformResources)
  (context : OsIntExitCallContext) : Assertion :=
  interrupt_platform_running platform context.(os_int_exit_invocation)
    context.(os_int_exit_origin) 192 **
  os_int_exit_context_resources port context **
  os_int_exit_continuation_escrow external platform port context.

Lemma armv7a_irq_frame_save_split : forall external platform port sg context entry,
  os_int_exit_frame_save_post external platform port context ** UCOS2_inv sg entry |--
  coq_prop (port.(os_int_exit_entry_source) context /\
    os_int_exit_interrupted_call_binding context) &&
  ((UCOS2_inv sg entry **
    task_stack_fragments_rep context.(os_int_exit_interrupted_stack).(stackLeaseRegion)
      context.(os_int_exit_interrupted_fragments)) **
   armv7a_irq_handler_frame external platform port context).
Proof. intros; unfold os_int_exit_frame_save_post, armv7a_irq_handler_frame; entailer!. Qed.

Definition armv7a_irq_context_parked_state (entry : UCOS2_Verify_State)
  (context : OsIntExitCallContext) : UCOS2_Verify_State :=
  os_int_exit_wrapper_parked_state
    (armv7a_irq_live_entry_state entry context.(os_int_exit_interrupted_stack).(stackLeaseSlot)
      context.(os_int_exit_interrupted_sp)) context.

Lemma armv7a_irq_context_saved_binding : forall entry context node,
  entry.(SchedState).(isRunning) = true ->
  entry.(TskState).(inUsedTaskStates) context.(os_int_exit_interrupted_stack).(stackLeaseSlot) = Some node ->
  os_int_exit_saved_exception_binding context (armv7a_irq_context_parked_state entry context).
Proof.
  intros entry context node Hrunning Hnode.
  apply os_int_exit_wrapper_parked_saved_binding; intros current Hcurrent Hgeneration.
  unfold armv7a_irq_live_entry_state, armv7a_irq_entry_counter_state in Hcurrent.
  rewrite Hrunning in Hcurrent.
  unfold os_sched_save_current_sp in Hcurrent; cbn [replace_IntrS TskState] in Hcurrent.
  rewrite Hnode in Hcurrent.
  cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates] in Hcurrent.
  rewrite Z.eqb_refl in Hcurrent; injection Hcurrent as Hcurrent; subst current; reflexivity.
Qed.

(** Connection of the existing architecture-save resource contract to the
    actual shared-memory producer. The saved frame, CPU/handler ownership
    and linear return escrow are all from the SAME context. Counter/SP
    stores preserve the handler resources by a real disjoint execution
    frame and park the saved bytes once. This is the masked memory portion
    of entry, not a proof of the external register-save implementation or
    a licence to treat unmasked raw ownership as stable. *)
Lemma armv7a_irq_frame_save_memory_post :
  forall external platform port sg entry handler origin stack fragments original
    pc mask sp saved node publication heap,
  let context := armv7a_irq_saved_call_context handler origin stack fragments original pc mask sp saved in
  entry.(SchedState).(isRunning) = true -> entry.(IntrState).(intNesting) = 0 ->
  entry.(SchedState).(curTaskID) = Some context.(os_int_exit_interrupted_stack).(stackLeaseSlot) ->
  entry.(TskState).(inUsedTaskStates) context.(os_int_exit_interrupted_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = context.(os_int_exit_interrupted_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = context.(os_int_exit_interrupted_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key context.(os_int_exit_interrupted_stack)) = None ->
  tcb_field_address (task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot) ->
  valid_task_stack_region context.(os_int_exit_interrupted_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range context.(os_int_exit_interrupted_stack).(stackLeaseRegion).(stackRegionWords) 0
    context.(os_int_exit_interrupted_fragments) ->
  task_publication_happened entry.(TskState) publication
    context.(os_int_exit_interrupted_stack).(stackLeaseSlot)
    context.(os_int_exit_interrupted_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range context.(os_int_exit_interrupted_stack).(stackLeaseRegion)
    context.(os_int_exit_interrupted_sp) ->
  (os_int_exit_frame_save_post external platform port context ** UCOS2_inv sg entry) heap ->
  exists final,
    kernel_heap_execution
      (armv7a_irq_live_entry_writes sg entry context.(os_int_exit_interrupted_stack).(stackLeaseSlot)
        context.(os_int_exit_interrupted_sp)) heap final /\
    os_int_exit_saved_exception_binding context (armv7a_irq_context_parked_state entry context) /\
    ((UCOS2_inv sg (armv7a_irq_context_parked_state entry context)) **
      armv7a_irq_handler_frame external platform port context) final.
Proof.
  intros external platform port sg entry handler origin stack fragments original
    pc mask sp saved node publication heap context Hrunning Hnesting
    Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hhistory Hsp Hbefore.
  pose proof (armv7a_irq_frame_save_split external platform port sg context entry heap Hbefore)
    as [[Hsource [Hstack Horigin]] [owned [frame [Hjoin [Howned Hframe]]]]].
  assert (Hproduce : exists after,
    kernel_heap_execution
      (armv7a_irq_live_entry_writes sg entry context.(os_int_exit_interrupted_stack).(stackLeaseSlot)
        context.(os_int_exit_interrupted_sp)) owned after /\
    UCOS2_inv sg (armv7a_irq_context_parked_state entry context) after).
  { assert (Hsame : armv7a_irq_context_parked_state entry context =
      armv7a_irq_live_parked_state entry context.(os_int_exit_interrupted_call)
        context.(os_int_exit_interrupted_sp) context.(os_int_exit_interrupted_fragments)).
    { unfold armv7a_irq_context_parked_state, armv7a_irq_live_parked_state,
        os_int_exit_wrapper_parked_state; rewrite Hstack; reflexivity. }
    rewrite Hsame.
    rewrite <- Hstack in *.
    eapply armv7a_irq_live_entry_parks_stack; eassumption. }
  destruct Hproduce as [after [Hrun Hafter]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin) as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|].
  split; [eapply armv7a_irq_context_saved_binding; eassumption|].
  exists after, frame; split; [exact Hfinal|]; split; assumption.
Qed.
