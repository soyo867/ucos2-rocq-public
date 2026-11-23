Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_wrapper_completion_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.lib.event_pool.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_control_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SelectedIRQWrapperSegment.
Import CriticalComponent PrimitiveComponent SelectedCProgram SelectedCSource SelectedIRQWrapperCompletion.

Lemma irq_wrapper_c_step_preserves_observer :
  forall environment sg state before input stopped current after output,
  irq_wrapper_c_step environment sg state before input stopped current after output ->
  forall observer origin,
  task_invocation_active state.(TskState) observer origin /\ sched_observer_current_cache origin state ->
  task_invocation_active current.(TskState) observer origin /\ sched_observer_current_cache origin current.
Proof.
  intros until output; intro Hstep; destruct Hstep; intros observer origin [Hactive Hcache].
  split; [exact Hactive|exact Hcache].
Qed.

Lemma irq_wrapper_c_step_lifetime :
  forall environment sg state before input stopped current after output,
  irq_wrapper_c_step environment sg state before input stopped current after output ->
  forall observer origin,
  task_observer_lifetime_result observer origin state.(TskState) current.(TskState) stopped.
Proof.
  intros until output; intro Hstep; destruct Hstep; intros observer origin.
  apply task_observer_lifetime_result_not_stopped, task_observer_lifetime_transport_fields;
    reflexivity.
Qed.

Lemma irq_wrapper_c_step_source_frames :
  forall environment sg state before input stopped current after output,
  irq_wrapper_c_step environment sg state before input stopped current after output ->
  forall task_observer event_observer,
  task_creation_frame task_observer state.(TskState) current.(TskState) /\
  event_creation_frame event_observer state.(EventState) current.(EventState) /\
  state.(NameState) = current.(NameState) /\ state.(TimerState) = current.(TimerState).
Proof.
  intros until output; intro Hstep; destruct Hstep; intros task_observer event_observer.
  repeat split; reflexivity.
Qed.

Lemma irq_wrapper_c_step_control :
  forall environment sg state before input stopped current after output,
  irq_wrapper_c_step environment sg state before input stopped current after output ->
  kernel_call_control_rely sg state current.
Proof. intros until output; intro Hstep; destruct Hstep; split; reflexivity. Qed.

Lemma irq_wrapper_c_step_idle_non_idle :
  forall environment sg observed state before input stopped current after output,
  irq_wrapper_c_step environment sg state before input stopped current after output ->
  (task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState)) /\
  (flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current).
Proof.
  intros until output; intro Hstep; destruct Hstep; split; intro Hfact; exact Hfact.
Qed.

(** Report-only extension.  Every existing source leaf is retained; the
    new branch is the actual no-selection IRQ wrapper take/restore.
    The nominal sequence type is still CriticalComponent.kernel_c_sequence. *)
Inductive kernel_program_wrapper_c_step environment critical sg observer origin : KernelCSegmentRelation :=
| KernelProgramWrapperOriginal : forall state before input stopped current after output,
  kernel_program_selected_c_step environment critical sg observer origin
    state before input stopped current after output ->
  kernel_program_wrapper_c_step environment critical sg observer origin
    state before input stopped current after output
| KernelProgramWrapperIRQ : forall state before input stopped current after output,
  irq_wrapper_c_step environment sg state before input stopped current after output ->
  kernel_program_wrapper_c_step environment critical sg observer origin
    state before input stopped current after output.

Lemma kernel_program_wrapper_c_step_resources :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_program_wrapper_c_step environment critical sg observer origin
    state before input stopped current after output -> input before /\ output after.
Proof.
  intros until output; intro Hstep; destruct Hstep.
  - eapply kernel_program_selected_c_step_resources; exact H.
  - eapply irq_wrapper_c_step_resources; exact H.
Qed.

Lemma kernel_program_wrapper_c_sequence_resources :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_c_sequence (kernel_program_wrapper_c_step environment critical sg observer origin)
    state before input stopped current after output -> input before /\ output after.
Proof.
  intros environment critical sg observer origin.
  apply kernel_c_sequence_resources, kernel_program_wrapper_c_step_resources.
Qed.

Definition kernel_program_wrapper_sequence_include
  environment critical sg observer origin state before input stopped current after output
  (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    state before input stopped current after output) :
  kernel_c_sequence (kernel_program_wrapper_c_step environment critical sg observer origin)
    state before input stopped current after output.
Proof.
  induction run.
  - constructor; exact H.
  - apply KernelCSequenceAtom, KernelProgramWrapperOriginal; exact H.
  - eapply KernelCSequenceThen; eassumption.
  - eapply KernelCSequenceAdapt; eassumption.
Defined.

Lemma selected_sequence_irq_wrapper_completion :
  forall environment critical sg original initial first_heap input stopped state before
    local suspended receipt node handler frame after
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap input stopped state before
      (irq_wrapper_c_input environment sg state local suspended receipt handler frame)),
  task_in_range sg initial.(TskState) ->
  kernel_call_task_source original initial ->
  irq_wrapper_c_completion environment sg state local suspended receipt original node handler frame before after ->
  kernel_c_sequence (kernel_program_wrapper_c_step environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial first_heap input (orb stopped false)
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) after
    (irq_wrapper_c_output environment sg state local suspended receipt original handler frame) /\
  kernel_call_task_source (armv7a_continuation_resumed_call suspended original)
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) /\
  kernel_call_normal_return original initial (armv7a_continuation_resumed_call suspended original)
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)).
Proof.
  intros environment critical sg original initial first_heap input stopped state before
    local suspended receipt node handler frame after run Hrange Hinitial Hcomplete.
  split.
  - eapply KernelCSequenceThen.
    + exact (kernel_program_wrapper_sequence_include _ _ _ _ _ _ _ _ _ _ _ _ run).
    + intros heap Howned; exact Howned.
    + apply KernelCSequenceAtom, KernelProgramWrapperIRQ.
      econstructor; exact Hcomplete.
  - split.
    + eapply selected_sequence_irq_wrapper_task_source; eassumption.
    + eapply irq_wrapper_c_completion_normal_return; [exact Hcomplete|exact (proj1 Hinitial)].
Qed.

End SelectedIRQWrapperSegment.

