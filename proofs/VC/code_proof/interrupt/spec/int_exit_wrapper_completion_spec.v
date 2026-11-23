Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_retirement_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SelectedIRQWrapperCompletion.
Import CriticalComponent PrimitiveComponent SelectedCProgram SelectedRetirementTransport.

Definition irq_wrapper_c_input environment sg state local suspended receipt handler
  (frame : Assertion) : Assertion :=
  UCOS2_fields_inv sg state **
  store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations)
      state.(TskState) (kernel_irq_fields_local local suspended receipt))
    state.(TskState).(parkedTaskStacks) **
  (interrupt_platform_running environment.(task_stack_call_platform)
     handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
   os_int_exit_context_resources environment.(task_stack_call_port) handler ** frame).

Definition irq_wrapper_c_output environment sg state local suspended receipt original handler
  (frame : Assertion) : Assertion :=
  flag_source_save_input environment.(task_stack_call_continuations)
    (fun sg state => UCOS2_fields_inv sg state) local sg
    (Some (task_stack_key suspended.(armv7a_continuation_stack)))
    (armv7a_continuation_resumed_call suspended original)
    (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr))
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) receipt **
  task_stack_fragments_rep handler.(os_int_exit_handler_stack)
    handler.(os_int_exit_handler_fragments) ** frame.

(** The wrapper reads/restores its actual saved descriptor.  The receipt is
    the fixed local currently owned by that descriptor; it is not an
    arbitrary assertion reevaluated at the final world.  No scheduling
    install or final TaskSource is a premise of this C/ABI completion. *)
Record irq_wrapper_c_completion environment sg state local suspended receipt original node handler frame
  before after : Prop := {
  irq_wrapper_c_binding : armv7a_continuation_binding suspended;
  irq_wrapper_c_saved_call : suspended.(armv7a_continuation_call) = Some original;
  irq_wrapper_c_current :
    state.(SchedState).(curTaskID) = Some suspended.(armv7a_continuation_stack).(stackLeaseSlot);
  irq_wrapper_c_node :
    state.(TskState).(inUsedTaskStates) suspended.(armv7a_continuation_stack).(stackLeaseSlot) = Some node;
  irq_wrapper_c_generation :
    node.(taskGeneration) = suspended.(armv7a_continuation_stack).(stackLeaseGeneration);
  irq_wrapper_c_parked :
    state.(TskState).(parkedTaskStacks) (task_stack_key suspended.(armv7a_continuation_stack)) =
      Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments));
  irq_wrapper_c_stack_address :
    tcb_field_address (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) TCBStkPtr =
      task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot);
  irq_wrapper_c_coverage : task_stack_live_coverage state.(TskState) None;
  irq_wrapper_c_before_owned :
    irq_wrapper_c_input environment sg state local suspended receipt handler frame before;
  irq_wrapper_c_restore :
    armv7a_restore_transition environment.(task_stack_call_continuations) handler suspended before after
}.

Lemma irq_wrapper_c_completion_resources :
  forall environment sg state local suspended receipt original node handler frame before after,
  irq_wrapper_c_completion environment sg state local suspended receipt original node handler frame before after ->
  irq_wrapper_c_input environment sg state local suspended receipt handler frame before /\
  irq_wrapper_c_output environment sg state local suspended receipt original handler frame after.
Proof.
  intros until after; intro Hcomplete.
  destruct Hcomplete as [Hbinding Hcall Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hinput Hrestore].
  split; [exact Hinput|].
  exact (proj2 (proj2 (kernel_irq_restore_fields_local_resources _ _ _
    environment.(task_stack_call_continuations) sg state local suspended original node handler receipt frame
    before after Hcall Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hinput Hrestore))).
Qed.

Lemma irq_wrapper_c_completion_normal_return :
  forall environment sg state local suspended receipt original node handler frame before after initial,
  irq_wrapper_c_completion environment sg state local suspended receipt original node handler frame before after ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  kernel_call_normal_return original initial
    (armv7a_continuation_resumed_call suspended original)
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)).
Proof.
  intros until initial; intros Hcomplete Horigin.
  destruct Hcomplete as [Hbinding Hcall Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hinput Hrestore].
  assert (Hstack : original.(os_sched_call_stack) = suspended.(armv7a_continuation_stack)).
  { pose proof (proj2 Hbinding) as H; rewrite Hcall in H; exact H. }
  split.
  - unfold task_tcb_init_stack_same_call, armv7a_continuation_resumed_call; simpl.
    repeat split; try reflexivity; exact (eq_sym Hstack).
  - intro Havailable; unfold kernel_call_stack_available, armv7a_continuation_resumed_call,
      os_int_exit_wrapper_restored_state; simpl.
    rewrite Horigin, Hstack.
    apply task_stack_take_lookup.
Qed.

(** Registration and the retirement bit come from this very execution.
    The live generation/current pointer come from its actual wrapper
    read, not from an independently postulated final TaskSource. *)
Lemma selected_sequence_live_return_task_source :
  forall environment critical sg original initial first_heap input stopped current last_heap output node,
  kernel_c_sequence (kernel_program_selected_c_step environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial first_heap input stopped current last_heap output ->
  task_in_range sg initial.(TskState) ->
  kernel_call_task_source original initial ->
  current.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  current.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) ->
  kernel_call_task_source original current.
Proof.
  intros until node; intros Hrun Hrange [Horigin [Hactive Hcurrent0]] Hcurrent Hnode Hgen.
  pose proof (task_observer_lifetime_from_active sg initial.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) Hrange Hactive) as Hlife.
  destruct (kernel_program_selected_c_sequence_observer_lifetime _ _ _ _ _ _ _ _ _ _ _ _ Hrun)
    as [Htransport Hstop].
  destruct (Htransport Hlife) as [[Hregistered Hrest] Hback].
  pose proof (kernel_program_selected_c_sequence_preserves_unretired _ _ _ _ _ _ _ _ _ _ _ _ Hrun
    original.(os_sched_call_invocation) (proj1 (proj2 Hactive))) as Hretired.
  split; [exact Horigin|]; split.
  - split; [exact Hregistered|]; split; [exact Hretired|].
    rewrite Horigin; exists node; split; assumption.
  - unfold task_execution_current; rewrite Horigin; exact Hcurrent.
Qed.

Lemma selected_sequence_irq_wrapper_task_source :
  forall environment critical sg original initial first_heap input stopped state before
    local suspended receipt node handler frame after
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap input stopped state before
      (irq_wrapper_c_input environment sg state local suspended receipt handler frame)),
  task_in_range sg initial.(TskState) ->
  kernel_call_task_source original initial ->
  irq_wrapper_c_completion environment sg state local suspended receipt original node handler frame before after ->
  kernel_call_task_source (armv7a_continuation_resumed_call suspended original)
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)).
Proof.
  intros environment critical sg original initial first_heap input stopped state before
    local suspended receipt node handler frame after run Hrange Hinitial Hcomplete.
  destruct Hcomplete as [Hbinding Hcall Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hinput Hrestore].
  assert (Hstack : original.(os_sched_call_stack) = suspended.(armv7a_continuation_stack)).
  { pose proof (proj2 Hbinding) as H; rewrite Hcall in H; exact H. }
  assert (Hsource : kernel_call_task_source original state).
  { eapply selected_sequence_live_return_task_source; [exact run|exact Hrange|exact Hinitial| | |];
      rewrite Hstack; eassumption. }
  destruct Hsource as [Horigin [Hactive Hcur]].
  unfold kernel_call_task_source, armv7a_continuation_resumed_call; simpl.
  split; [rewrite <- Hstack; exact Horigin|]; split.
  - exact Hactive.
  - unfold task_execution_current; rewrite Horigin.
    change (state.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot)).
    rewrite Hstack; exact Hcurrent.
Qed.

Inductive irq_wrapper_c_step environment sg : KernelCSegmentRelation :=
| IRQWrapperCStep : forall state local suspended receipt original node handler frame before after,
  irq_wrapper_c_completion environment sg state local suspended receipt original node handler frame before after ->
  irq_wrapper_c_step environment sg state before
    (irq_wrapper_c_input environment sg state local suspended receipt handler frame)
    false (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) after
    (irq_wrapper_c_output environment sg state local suspended receipt original handler frame).

Lemma irq_wrapper_c_step_resources :
  forall environment sg state before input stopped current after output,
  irq_wrapper_c_step environment sg state before input stopped current after output ->
  input before /\ output after.
Proof. intros until output; intro Hstep; destruct Hstep; eapply irq_wrapper_c_completion_resources; exact H. Qed.

End SelectedIRQWrapperCompletion.

