Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_program_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_returned_c_segment_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SelectedReturnedCSource.
Import SelectedIRQWrapperSegment SelectedIRQWrapperSource OSIntExitReturnedC SelectedReturnedCProgram.

Inductive kernel_program_returned_c_step_source environment critical sg observer origin event_observer :
  forall state before input stopped current after output,
  kernel_program_returned_c_step environment critical sg observer origin
    state before input stopped current after output -> Prop :=
| KernelProgramReturnedWrapperSource : forall state before input stopped current after output step,
  kernel_program_wrapper_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output step ->
  kernel_program_returned_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output
    (@KernelProgramReturnedWrapper environment critical sg observer origin
      state before input stopped current after output step)
| KernelProgramReturnedExitSource : forall state before input stopped current after output step,
  kernel_program_returned_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output
    (@KernelProgramReturnedExit environment critical sg observer origin
      state before input stopped current after output step).

Definition kernel_program_returned_c_sequence_source environment critical sg observer origin event_observer
  state before input stopped current after output
  (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
    state before input stopped current after output) : Prop :=
  kernel_c_sequence_has_source (kernel_program_returned_c_step environment critical sg observer origin)
    (kernel_program_returned_c_step_source environment critical sg observer origin event_observer)
    state before input stopped current after output run.

Lemma kernel_program_returned_c_step_source_frames :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (step : kernel_program_returned_c_step environment critical sg observer origin
      state before input stopped current after output),
  kernel_program_returned_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output step ->
  task_creation_frame observer state.(TskState) current.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation state.(EventState) current.(EventState)) /\
  state.(NameState) = current.(NameState) /\ timer_public_trace sg state.(TimerState) current.(TimerState).
Proof.
  intros until step; intro Hsource; destruct Hsource.
  - eapply kernel_program_wrapper_c_step_source_frames; exact H.
  - destruct (os_int_exit_returned_c_step_source_frames _ _ _ _ _ _ _ _ _ _ step observer 0)
      as [Ht [_ [Hn Htme]]].
    split; [exact Ht|]. split.
    + intros invocation Hevent.
      exact (proj1 (proj2 (os_int_exit_returned_c_step_source_frames
        _ _ _ _ _ _ _ _ _ _ step observer invocation))).
    + split; [exact Hn|]. rewrite Htme; constructor.
Qed.

Lemma kernel_program_returned_c_sequence_source_frames :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
      state before input stopped current after output),
  kernel_program_returned_c_sequence_source environment critical sg observer origin event_observer
    state before input stopped current after output run ->
  task_creation_frame observer state.(TskState) current.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation state.(EventState) current.(EventState)) /\
  state.(NameState) = current.(NameState) /\ timer_public_trace sg state.(TimerState) current.(TimerState).
Proof.
  intros until run; intro Hsource.
  eapply (kernel_c_sequence_source_relation
    (kernel_program_returned_c_step environment critical sg observer origin)
    (kernel_program_returned_c_step_source environment critical sg observer origin event_observer)
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
  - intros; eapply kernel_program_returned_c_step_source_frames; eassumption.
  - exact Hsource.
Qed.

Lemma kernel_program_returned_sequence_include_source :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_wrapper_c_step environment critical sg observer origin)
      state before input stopped current after output),
  kernel_program_wrapper_c_sequence_source environment critical sg observer origin event_observer
    state before input stopped current after output run ->
  kernel_program_returned_c_sequence_source environment critical sg observer origin event_observer
    state before input stopped current after output
    (kernel_program_returned_sequence_include environment critical sg observer origin
      state before input stopped current after output run).
Proof.
  intros until run; intro Hsource.
  unfold kernel_program_wrapper_c_sequence_source in Hsource.
  unfold kernel_program_returned_c_sequence_source.
  induction Hsource; cbn [kernel_program_returned_sequence_include].
  - constructor.
  - apply KernelCSourceAtom, KernelProgramReturnedWrapperSource; exact H.
  - apply KernelCSourceThen; assumption.
  - apply KernelCSourceAdapt; assumption.
Qed.

End SelectedReturnedCSource.
