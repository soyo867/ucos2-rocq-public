Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_returned_c_segment_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SelectedReturnedCProgram.
Import SelectedIRQWrapperSegment SelectedIRQWrapperSource OSIntExitReturnedC.

(** Keep every existing C execution and add the actual OSIntExit Returned
    counter/selector/wrapper completion.  The latter is not a take-only
    step and is never represented by a change of heap in an Adapt rule. *)
Inductive kernel_program_returned_c_step environment critical sg observer origin : KernelCSegmentRelation :=
| KernelProgramReturnedWrapper : forall state before input stopped current after output,
  kernel_program_wrapper_c_step environment critical sg observer origin
    state before input stopped current after output ->
  kernel_program_returned_c_step environment critical sg observer origin
    state before input stopped current after output
| KernelProgramReturnedExit : forall state before input stopped current after output,
  os_int_exit_returned_c_step environment critical sg state before input stopped current after output ->
  kernel_program_returned_c_step environment critical sg observer origin
    state before input stopped current after output.

Lemma kernel_program_returned_c_step_resources :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_program_returned_c_step environment critical sg observer origin
    state before input stopped current after output -> input before /\ output after.
Proof.
  intros until output; intro Hstep; destruct Hstep.
  - eapply kernel_program_wrapper_c_step_resources; eassumption.
  - eapply os_int_exit_returned_c_step_resources; eassumption.
Qed.

Lemma kernel_program_returned_c_sequence_resources :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
    state before input stopped current after output -> input before /\ output after.
Proof.
  intros environment critical sg observer origin.
  apply kernel_c_sequence_resources, kernel_program_returned_c_step_resources.
Qed.

Definition kernel_program_returned_sequence_include
  environment critical sg observer origin state before input stopped current after output
  (run : kernel_c_sequence (kernel_program_wrapper_c_step environment critical sg observer origin)
    state before input stopped current after output) :
  kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
    state before input stopped current after output.
Proof.
  induction run.
  - eapply KernelCSequenceRefl; eassumption.
  - apply KernelCSequenceAtom, KernelProgramReturnedWrapper; exact H.
  - eapply KernelCSequenceThen; eassumption.
  - eapply KernelCSequenceAdapt; eassumption.
Defined.

Lemma kernel_program_returned_c_step_preserves_observer :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_program_returned_c_step environment critical sg observer origin
    state before input stopped current after output -> stopped = false ->
  task_invocation_active state.(TskState) observer origin /\ sched_observer_current_cache origin state ->
  task_invocation_active current.(TskState) observer origin /\ sched_observer_current_cache origin current.
Proof.
  intros until output; intros Hstep Hstop Hinitial; destruct Hstep.
  - eapply kernel_program_wrapper_c_step_preserves_observer; eassumption.
  - eapply os_int_exit_returned_c_step_preserves_observer; eassumption.
Qed.

Lemma kernel_program_returned_c_step_observer_lifetime :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_program_returned_c_step environment critical sg observer origin
    state before input stopped current after output ->
  task_observer_lifetime_result observer origin state.(TskState) current.(TskState) stopped.
Proof.
  intros until output; intro Hstep; destruct Hstep.
  - eapply kernel_program_wrapper_c_step_observer_lifetime; eassumption.
  - eapply os_int_exit_returned_c_step_lifetime; eassumption.
Qed.

Lemma kernel_program_returned_c_sequence_preserves_observer :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
    state before input stopped current after output -> stopped = false ->
  task_invocation_active state.(TskState) observer origin /\ sched_observer_current_cache origin state ->
  task_invocation_active current.(TskState) observer origin /\ sched_observer_current_cache origin current.
Proof.
  intros environment critical sg observer origin.
  apply kernel_c_sequence_preserves_observer, kernel_program_returned_c_step_preserves_observer.
Qed.

Lemma kernel_program_returned_c_sequence_observer_lifetime :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
    state before input stopped current after output ->
  task_observer_lifetime_result observer origin state.(TskState) current.(TskState) stopped.
Proof.
  intros environment critical sg observer origin.
  apply kernel_c_sequence_observer_lifetime, kernel_program_returned_c_step_observer_lifetime.
Qed.

Lemma kernel_program_returned_c_step_running :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_program_returned_c_step environment critical sg observer origin
    state before input stopped current after output ->
  current.(SchedState).(isRunning) = state.(SchedState).(isRunning).
Proof.
  intros until output; intro Hstep; destruct Hstep.
  - eapply kernel_program_wrapper_c_step_running; eassumption.
  - eapply os_int_exit_returned_c_step_running; eassumption.
Qed.

Lemma kernel_program_returned_c_sequence_running :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
    state before input stopped current after output ->
  current.(SchedState).(isRunning) = state.(SchedState).(isRunning).
Proof.
  intros until output; intro Hrun; induction Hrun.
  - reflexivity.
  - eapply kernel_program_returned_c_step_running; eassumption.
  - etransitivity; eassumption.
  - exact IHHrun.
Qed.

Lemma kernel_program_returned_c_sequence_completed_current_cache :
  forall environment critical sg original returned initial before input stopped current after output,
  kernel_c_sequence (kernel_program_returned_c_step environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial before input stopped current after output ->
  task_in_range sg initial.(TskState) -> kernel_call_task_source original initial ->
  sched_current_consistency initial.(TskState) initial.(SchedState) ->
  kernel_call_normal_return original initial returned current -> kernel_call_task_source returned current ->
  stopped = false /\ sched_current_consistency current.(TskState) current.(SchedState).
Proof.
  intros environment critical sg original returned.
  apply (kernel_c_sequence_completed_current_cache
    (kernel_program_returned_c_step environment critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin)) sg original returned).
  - exact (kernel_program_returned_c_step_preserves_observer environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  - exact (kernel_program_returned_c_step_observer_lifetime environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin)).
Qed.

End SelectedReturnedCProgram.
