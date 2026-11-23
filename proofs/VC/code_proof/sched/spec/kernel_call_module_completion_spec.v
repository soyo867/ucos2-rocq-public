(* Report candidate: actual module completions; staged only by the parent. *)
Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_events_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.interrupt_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_phase_spec.

Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module ModuleCompletionSource.
Import PrimitiveComponent SelectedProgramEvents.
Import SelectedEnvironmentPhaseEffects SelectedEnvironmentPhaseProperties.

(** Each branch keeps an existing module completion, including its operation
    and its exact caller heaps.  A C sequence is an implementation of the
    Task execution branch; arbitrary event/sequence pairs are not constructors. *)
Inductive flag_pend_selected_event_source environment critical sg : FlagPendLinkedEvent -> Prop :=
| FlagPendModuleTaskSave : forall local next_local active original mask saved before first_heap
    stopped returned current last_heap,
    os_sched_continuation_c_save_execution environment critical local next_local active sg
      original mask before first_heap saved stopped returned current last_heap ->
    flag_pend_selected_event_source environment critical sg
      (flag_pend_task_save_completed_c_event environment critical local next_local active sg
        original mask saved before first_heap returned current last_heap)
| FlagPendModuleTaskRestore : forall local next_local active original saved acquired before first_heap
    stopped returned current last_heap,
    os_sched_continuation_c_restore_execution environment critical local next_local active sg
      original saved acquired before first_heap stopped returned current last_heap ->
    flag_pend_selected_event_source environment critical sg
      (flag_pend_task_restore_completed_c_event environment critical local next_local active sg
        original saved acquired before first_heap returned current last_heap)
| FlagPendModuleUninterrupted : forall event,
    flag_pend_task_primitive_c_event environment critical sg event ->
    flag_pend_selected_event_source environment critical sg event
| FlagPendModuleView : forall event,
    ViewPrimitiveComponent.flag_pend_view_primitive_completion environment critical sg event ->
    flag_pend_selected_event_source environment critical sg event.

Lemma flag_pend_selected_event_source_resources : forall environment critical sg event,
  flag_pend_selected_event_source environment critical sg event ->
  event.(flag_pend_event_input) event.(flag_pend_event_first_heap) /\
  event.(flag_pend_event_output) event.(flag_pend_event_last_heap).
Proof.
  intros environment critical sg event Hactual; destruct Hactual.
  - eapply os_sched_continuation_c_save_execution_resources; eassumption.
  - eapply os_sched_continuation_c_restore_execution_resources; eassumption.
  - eapply flag_pend_task_primitive_c_event_resources; eassumption.
  - eapply ViewPrimitiveComponent.flag_pend_view_primitive_completion_resources; eassumption.
Qed.

Definition flag_pend_selected_linked_sources environment critical sg :
  FlagPendProgramSources environment critical sg :=
  {| flag_pend_program_event_source := flag_pend_selected_event_source environment critical sg;
     flag_pend_program_event_resources := flag_pend_selected_event_source_resources environment critical sg |}.

Definition flag_pend_selected_linked_prefix environment critical sg operation caller original before
  returned_caller returned current (input : Assertion) first_heap (output : Assertion) last_heap : Prop :=
  flag_pend_program_event_source environment critical sg
    (flag_pend_selected_linked_sources environment critical sg)
    {| flag_pend_event_operation := operation; flag_pend_event_caller := caller;
       flag_pend_event_original := original; flag_pend_event_returned_caller := returned_caller;
       flag_pend_event_returned := returned; flag_pend_event_before := before;
       flag_pend_event_current := current; flag_pend_event_first_heap := first_heap;
       flag_pend_event_last_heap := last_heap; flag_pend_event_input := input;
       flag_pend_event_output := output |}.

Lemma flag_pend_selected_linked_prefix_resources : forall environment critical sg operation caller original before
  returned_caller returned current input first_heap output last_heap,
  flag_pend_selected_linked_prefix environment critical sg operation caller original before
    returned_caller returned current input first_heap output last_heap ->
  input first_heap /\ output last_heap.
Proof.
  intros; exact (flag_pend_program_event_resources environment critical sg
    (flag_pend_selected_linked_sources environment critical sg) _ H).
Qed.

Definition flag_pend_selected_completed_source operation environment critical sg caller original before
  (input : Assertion) first_heap returned_caller returned current last_heap (output : Assertion) : Prop :=
  flag_pend_selected_linked_prefix environment critical sg operation caller original before
    returned_caller returned current input first_heap
    (coq_prop (flag_pend_call_endpoint_observations environment sg caller original before returned current) && output)
    last_heap.

Lemma flag_pend_selected_completed_source_endpoints : forall operation environment critical sg caller original before
  input first_heap returned_caller returned current last_heap output,
  flag_pend_selected_completed_source operation environment critical sg caller original before
    input first_heap returned_caller returned current last_heap output ->
  flag_pend_call_endpoint_observations environment sg caller original before returned current /\
    input first_heap /\ output last_heap.
Proof.
  intros operation environment critical sg caller original before input first_heap
    returned_caller returned current last_heap output Hactual.
  destruct (flag_pend_selected_linked_prefix_resources environment critical sg operation caller original before
    returned_caller returned current input first_heap _ last_heap Hactual) as [Hinput [Hendpoints Houtput]].
  exact (conj Hendpoints (conj Hinput Houtput)).
Qed.

Lemma flag_pend_selected_event_source_current_cache : forall environment critical sg event,
  flag_pend_selected_event_source environment critical sg event ->
  event.(flag_pend_event_caller) = FlagPendTaskCaller event.(flag_pend_event_original) ->
  task_in_range sg event.(flag_pend_event_before).(TskState) ->
  kernel_call_task_source event.(flag_pend_event_original) event.(flag_pend_event_before) ->
  sched_current_consistency event.(flag_pend_event_before).(TskState) event.(flag_pend_event_before).(SchedState) ->
  kernel_call_normal_return event.(flag_pend_event_original) event.(flag_pend_event_before)
    event.(flag_pend_event_returned) event.(flag_pend_event_current) ->
  kernel_call_task_source event.(flag_pend_event_returned) event.(flag_pend_event_current) ->
  sched_current_consistency event.(flag_pend_event_current).(TskState) event.(flag_pend_event_current).(SchedState).
Proof.
  intros environment critical sg event Hactual Hcaller Hrange Horiginal Hcache Hnormal Hreturned.
  destruct Hactual as
    [local next_local active original mask saved before first_heap stopped returned current last_heap Hsave
    |local next_local active original saved acquired before first_heap stopped returned current last_heap Hrestore
    |event Hprimitive |event Hview].
  - destruct (os_sched_continuation_c_save_execution_effect_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsave)
      as [_ [_ Hsource]].
    eapply SelectedEnvironmentPhaseProperties.flag_pend_program_c_event_current_cache;
      [exact Hsource|exact Hcaller|exact Hrange|exact Horiginal|exact Hcache|exact Hnormal|exact Hreturned].
  - destruct (os_sched_continuation_c_restore_execution_effect_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrestore)
      as [_ Hsource].
    eapply SelectedEnvironmentPhaseProperties.flag_pend_program_c_event_current_cache;
      [exact Hsource|exact Hcaller|exact Hrange|exact Horiginal|exact Hcache|exact Hnormal|exact Hreturned].
  - destruct Hprimitive; exact Hcache.
  - destruct Hview; discriminate Hcaller.
Qed.

Lemma flag_pend_selected_save_current_cache :
  forall environment critical local next_local active sg original mask saved before first_heap returned current last_heap,
  flag_pend_selected_event_source environment critical sg
    (flag_pend_task_save_completed_c_event environment critical local next_local active sg
      original mask saved before first_heap returned current last_heap) ->
  kernel_call_task_source original before ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  kernel_call_task_source returned current ->
  sched_current_consistency current.(TskState) current.(SchedState).
Proof.
  intros until last_heap; intros Hactual Horiginal Hcache Hreturned.
  destruct (flag_pend_selected_event_source_resources _ _ _ _ Hactual) as [Hinput [Hendpoint Houtput]].
  destruct Hendpoint as [_ [_ [_ [Hnormal _]]]].
  eapply (flag_pend_selected_event_source_current_cache environment critical sg
    (flag_pend_task_save_completed_c_event environment critical local next_local active sg
      original mask saved before first_heap returned current last_heap));
    [exact Hactual|reflexivity| |exact Horiginal|exact Hcache|exact Hnormal|exact Hreturned].
  eapply flag_pend_caller_save_input_task_in_range; exact Hinput.
Qed.

Lemma flag_pend_selected_restore_current_cache :
  forall environment critical local next_local active sg original saved acquired before first_heap returned current last_heap,
  flag_pend_selected_event_source environment critical sg
    (flag_pend_task_restore_completed_c_event environment critical local next_local active sg
      original saved acquired before first_heap returned current last_heap) ->
  kernel_call_task_source original before ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  kernel_call_task_source returned current ->
  sched_current_consistency current.(TskState) current.(SchedState).
Proof.
  intros until last_heap; intros Hactual Horiginal Hcache Hreturned.
  destruct (flag_pend_selected_event_source_resources _ _ _ _ Hactual) as [Hinput [Hendpoint Houtput]].
  destruct Hendpoint as [_ [_ [_ [Hnormal _]]]].
  eapply (flag_pend_selected_event_source_current_cache environment critical sg
    (flag_pend_task_restore_completed_c_event environment critical local next_local active sg
      original saved acquired before first_heap returned current last_heap));
    [exact Hactual|reflexivity| |exact Horiginal|exact Hcache|exact Hnormal|exact Hreturned].
  eapply flag_pend_caller_restore_input_task_in_range; exact Hinput.
Qed.
End ModuleCompletionSource.
