Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_wrapper_completion_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.lib.event_pool.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_control_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_idle_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SelectedIRQWrapperSource.
Import CriticalComponent PrimitiveComponent SelectedCProgram SelectedCSource.
Import SelectedControlComposition SelectedIdleComposition.
Import SelectedIRQWrapperCompletion SelectedIRQWrapperSegment.

Inductive kernel_program_wrapper_c_step_source environment critical sg observer origin event_observer :
  forall state before input stopped current after output,
  kernel_program_wrapper_c_step environment critical sg observer origin
    state before input stopped current after output -> Prop :=
| KernelProgramWrapperOriginalSource : forall state before input stopped current after output step,
  kernel_program_selected_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output step ->
  kernel_program_wrapper_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output
    (@KernelProgramWrapperOriginal environment critical sg observer origin
      state before input stopped current after output step)
| KernelProgramWrapperIRQSource : forall state before input stopped current after output step,
  kernel_program_wrapper_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output
    (@KernelProgramWrapperIRQ environment critical sg observer origin
      state before input stopped current after output step).

Definition kernel_program_wrapper_c_sequence_source environment critical sg observer origin event_observer
  state before input stopped current after output
  (run : kernel_c_sequence (kernel_program_wrapper_c_step environment critical sg observer origin)
    state before input stopped current after output) : Prop :=
  kernel_c_sequence_has_source (kernel_program_wrapper_c_step environment critical sg observer origin)
    (kernel_program_wrapper_c_step_source environment critical sg observer origin event_observer)
    state before input stopped current after output run.

Lemma kernel_program_wrapper_c_step_source_frames :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (step : kernel_program_wrapper_c_step environment critical sg observer origin
      state before input stopped current after output),
  kernel_program_wrapper_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output step ->
  task_creation_frame observer state.(TskState) current.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation state.(EventState) current.(EventState)) /\
  state.(NameState) = current.(NameState) /\ timer_public_trace sg state.(TimerState) current.(TimerState).
Proof.
  intros until step; intro Hsource; destruct Hsource.
  - eapply kernel_program_selected_c_step_source_frames; exact H.
  - destruct (irq_wrapper_c_step_source_frames _ _ _ _ _ _ _ _ _ step observer 0)
      as [Htask [_ [Hname Htimer]]].
    split; [exact Htask|]. split.
    + intros invocation Hobserver.
      exact (proj1 (proj2 (irq_wrapper_c_step_source_frames _ _ _ _ _ _ _ _ _ step observer invocation))).
    + split; [exact Hname|]. rewrite Htimer; constructor.
Qed.

Lemma kernel_program_wrapper_c_sequence_source_frames :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_wrapper_c_step environment critical sg observer origin)
      state before input stopped current after output),
  kernel_program_wrapper_c_sequence_source environment critical sg observer origin event_observer
    state before input stopped current after output run ->
  task_creation_frame observer state.(TskState) current.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation state.(EventState) current.(EventState)) /\
  state.(NameState) = current.(NameState) /\ timer_public_trace sg state.(TimerState) current.(TimerState).
Proof.
  intros until run; intro Hsource.
  eapply (kernel_c_sequence_source_relation
    (kernel_program_wrapper_c_step environment critical sg observer origin)
    (kernel_program_wrapper_c_step_source environment critical sg observer origin event_observer)
    (fun entry final => task_creation_frame observer entry.(TskState) final.(TskState) /\
      (forall invocation, event_observer = Some invocation ->
        event_creation_frame invocation entry.(EventState) final.(EventState)) /\
      entry.(NameState) = final.(NameState) /\ timer_public_trace sg entry.(TimerState) final.(TimerState))).
  - intro entry; split; [reflexivity|]. split; [intros; reflexivity|]. split; [reflexivity|constructor].
  - intros first middle last [Ht [He [Hn Hr]]] [Ht' [He' [Hn' Hr']]].
    split.
    + unfold task_creation_frame in *; etransitivity; [exact Ht'|exact Ht].
    + split.
      * intros invocation Hobserver; unfold event_creation_frame in *;
          etransitivity; [exact (He' invocation Hobserver)|exact (He invocation Hobserver)].
      * split; [etransitivity; eassumption|]. eapply timer_public_trace_trans; eassumption.
  - intros; eapply kernel_program_wrapper_c_step_source_frames; eassumption.
  - exact Hsource.
Qed.

(** The output marker is indexed by the transparent injection of precisely
    the supplied run, including each original bridge and heap. *)
Lemma kernel_program_wrapper_sequence_include_source :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      state before input stopped current after output),
  kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    state before input stopped current after output run ->
  kernel_program_wrapper_c_sequence_source environment critical sg observer origin event_observer
    state before input stopped current after output
    (kernel_program_wrapper_sequence_include environment critical sg observer origin
      state before input stopped current after output run).
Proof.
  intros until run; intro Hsource.
  unfold kernel_program_selected_c_sequence_source in Hsource.
  unfold kernel_program_wrapper_c_sequence_source.
  induction Hsource; cbn [kernel_program_wrapper_sequence_include].
  - constructor.
  - apply KernelCSourceAtom, KernelProgramWrapperOriginalSource; exact H.
  - apply KernelCSourceThen; assumption.
  - apply KernelCSourceAdapt; assumption.
Qed.

Lemma kernel_program_wrapper_c_step_preserves_observer :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_program_wrapper_c_step environment critical sg observer origin
    state before input stopped current after output -> stopped = false ->
  task_invocation_active state.(TskState) observer origin /\ sched_observer_current_cache origin state ->
  task_invocation_active current.(TskState) observer origin /\ sched_observer_current_cache origin current.
Proof.
  intros until output; intros Hstep Hstop Hinitial; destruct Hstep.
  - eapply kernel_program_selected_c_step_preserves_observer; eassumption.
  - eapply irq_wrapper_c_step_preserves_observer; eassumption.
Qed.

Lemma kernel_program_wrapper_c_step_observer_lifetime :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_program_wrapper_c_step environment critical sg observer origin
    state before input stopped current after output ->
  task_observer_lifetime_result observer origin state.(TskState) current.(TskState) stopped.
Proof.
  intros until output; intro Hstep; destruct Hstep.
  - eapply kernel_program_selected_c_step_observer_lifetime; eassumption.
  - eapply irq_wrapper_c_step_lifetime; eassumption.
Qed.

Lemma kernel_program_wrapper_c_sequence_preserves_observer :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_c_sequence (kernel_program_wrapper_c_step environment critical sg observer origin)
    state before input stopped current after output -> stopped = false ->
  task_invocation_active state.(TskState) observer origin /\ sched_observer_current_cache origin state ->
  task_invocation_active current.(TskState) observer origin /\ sched_observer_current_cache origin current.
Proof.
  intros environment critical sg observer origin.
  apply kernel_c_sequence_preserves_observer, kernel_program_wrapper_c_step_preserves_observer.
Qed.

Lemma kernel_program_wrapper_c_sequence_observer_lifetime :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_c_sequence (kernel_program_wrapper_c_step environment critical sg observer origin)
    state before input stopped current after output ->
  task_observer_lifetime_result observer origin state.(TskState) current.(TskState) stopped.
Proof.
  intros environment critical sg observer origin.
  apply kernel_c_sequence_observer_lifetime, kernel_program_wrapper_c_step_observer_lifetime.
Qed.

Lemma kernel_program_wrapper_c_step_running :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_program_wrapper_c_step environment critical sg observer origin
    state before input stopped current after output ->
  current.(SchedState).(isRunning) = state.(SchedState).(isRunning).
Proof.
  intros until output; intro Hstep; destruct Hstep.
  - eapply kernel_program_selected_c_step_running; eassumption.
  - exact (proj1 (irq_wrapper_c_step_control _ _ _ _ _ _ _ _ _ H)).
Qed.

Lemma kernel_program_wrapper_c_sequence_running :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_c_sequence (kernel_program_wrapper_c_step environment critical sg observer origin)
    state before input stopped current after output ->
  current.(SchedState).(isRunning) = state.(SchedState).(isRunning).
Proof.
  intros until output; intro Hrun; induction Hrun.
  - reflexivity.
  - eapply kernel_program_wrapper_c_step_running; exact H.
  - etransitivity; [exact IHHrun2|exact IHHrun1].
  - exact IHHrun.
Qed.

(** This producer composes the same source-indexed prefix and the actual
    saved-descriptor return.  It does not select another endpoint-equal run. *)
Lemma selected_sequence_irq_wrapper_completion_source :
  forall environment critical sg event_observer original initial first_heap input stopped state before
    local suspended receipt node handler frame after
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap input stopped state before
      (irq_wrapper_c_input environment sg state local suspended receipt handler frame)),
  kernel_program_selected_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer
    _ _ _ _ _ _ _ run ->
  task_in_range sg initial.(TskState) -> kernel_call_task_source original initial ->
  irq_wrapper_c_completion environment sg state local suspended receipt original node handler frame before after ->
  exists (completed : kernel_c_sequence (kernel_program_wrapper_c_step environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial first_heap input (orb stopped false)
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) after
    (irq_wrapper_c_output environment sg state local suspended receipt original handler frame)),
  kernel_program_wrapper_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer
    _ _ _ _ _ _ _ completed /\
  kernel_call_task_source (armv7a_continuation_resumed_call suspended original)
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) /\
  kernel_call_normal_return original initial (armv7a_continuation_resumed_call suspended original)
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)).
Proof.
  intros until run; intros Hsource Hrange Hinitial Hcomplete.
  pose (prefix := kernel_program_wrapper_sequence_include _ _ _ _ _ _ _ _ _ _ _ _ run).
  pose (step := @KernelProgramWrapperIRQ environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _
    (@IRQWrapperCStep environment sg state local suspended receipt original node handler frame before after Hcomplete)).
  pose (tail := KernelCSequenceAtom _ _ _ _ _ _ _ _ step).
  exists (KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ prefix (fun heap Howner => Howner) tail).
  split.
  - unfold kernel_program_wrapper_c_sequence_source; apply KernelCSourceThen.
    + apply kernel_program_wrapper_sequence_include_source; exact Hsource.
    + unfold tail; apply KernelCSourceAtom; unfold step; apply KernelProgramWrapperIRQSource.
  - split.
    + eapply selected_sequence_irq_wrapper_task_source; eassumption.
    + eapply irq_wrapper_c_completion_normal_return; [exact Hcomplete|exact (proj1 Hinitial)].
Qed.

End SelectedIRQWrapperSource.
