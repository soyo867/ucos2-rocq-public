(* Report candidate: actual module completions; staged only by the parent. *)
Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_phase_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_events_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_module_completion_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_boot_primitive_spec.

Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SelectedEventSources.
Import PrimitiveComponent FlagPendBootPrimitive.

Local Lemma flag_pend_boot_endpoint_from_normal_return : forall environment sg original before returned current,
  original.(os_sched_call_origin) = BootInvocation ->
  kernel_call_normal_return original before returned current ->
  flag_pend_call_endpoint_observations environment sg
    (FlagPendTaskCaller original) original before returned current.
Proof.
  intros environment sg original before returned current Hboot Hnormal.
  assert (Hnot : ~ kernel_call_task_source original before).
  { intros [Horigin _]; rewrite Hboot in Horigin; discriminate. }
  cbn [flag_pend_call_endpoint_observations]; tauto.
Qed.

Local Lemma flag_pend_endpoint_from_task_observations : forall environment sg caller original before returned current,
  flag_pend_call_endpoint_observations environment sg caller original before returned current ->
  flag_pend_call_endpoint_observations environment sg caller original before returned current.
Proof. intros; assumption. Qed.

Definition flag_pend_event_with_owners (event : FlagPendLinkedEvent)
  (input output : Assertion) : FlagPendLinkedEvent :=
  {| flag_pend_event_operation := event.(flag_pend_event_operation);
     flag_pend_event_caller := event.(flag_pend_event_caller);
     flag_pend_event_original := event.(flag_pend_event_original);
     flag_pend_event_returned_caller := event.(flag_pend_event_returned_caller);
     flag_pend_event_returned := event.(flag_pend_event_returned);
     flag_pend_event_before := event.(flag_pend_event_before);
     flag_pend_event_current := event.(flag_pend_event_current);
     flag_pend_event_first_heap := event.(flag_pend_event_first_heap);
     flag_pend_event_last_heap := event.(flag_pend_event_last_heap);
     flag_pend_event_input := input; flag_pend_event_output := output |}.

Definition flag_pend_task_save_completed_c_event environment critical local next_local active sg
  original mask saved before first_heap returned current last_heap : FlagPendLinkedEvent :=
  {| flag_pend_event_operation := FlagPendSaveSource;
     flag_pend_event_caller := FlagPendTaskCaller original;
     flag_pend_event_original := original;
     flag_pend_event_returned_caller := FlagPendTaskCaller returned;
     flag_pend_event_returned := returned;
     flag_pend_event_before := before; flag_pend_event_current := current;
     flag_pend_event_first_heap := first_heap; flag_pend_event_last_heap := last_heap;
     flag_pend_event_input := flag_pend_caller_save_input environment critical local active sg
       (FlagPendTaskCaller original) original mask before;
     flag_pend_event_output :=
       coq_prop (flag_pend_call_endpoint_observations environment sg
         (FlagPendTaskCaller original) original before returned current) &&
       flag_pend_caller_restore_input environment critical next_local active sg
         (FlagPendTaskCaller returned) returned saved current current |}.

Definition flag_pend_task_restore_completed_c_event environment critical local next_local active sg
  original saved acquired before first_heap returned current last_heap : FlagPendLinkedEvent :=
  {| flag_pend_event_operation := FlagPendRestoreSource;
     flag_pend_event_caller := FlagPendTaskCaller original;
     flag_pend_event_original := original;
     flag_pend_event_returned_caller := FlagPendTaskCaller returned;
     flag_pend_event_returned := returned;
     flag_pend_event_before := before; flag_pend_event_current := current;
     flag_pend_event_first_heap := first_heap; flag_pend_event_last_heap := last_heap;
     flag_pend_event_input := flag_pend_caller_restore_input environment critical local active sg
       (FlagPendTaskCaller original) original saved acquired before;
     flag_pend_event_output :=
       coq_prop (flag_pend_call_endpoint_observations environment sg
         (FlagPendTaskCaller original) original before returned current) &&
       flag_pend_caller_save_input environment critical next_local active sg
         (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current |}.

(** Consequence changes only assertions at the original heaps.  It does not
    change a call, result, state, operation, or physical execution. *)
Inductive flag_pend_selected_event_source environment critical sg : FlagPendLinkedEvent -> Prop :=
| FlagPendCompletedModule : forall event,
    ModuleCompletionSource.flag_pend_selected_event_source environment critical sg event ->
    flag_pend_selected_event_source environment critical sg event
| FlagPendCompletedBootSave : forall local next_local original mask saved before first_heap
    returned current last_heap,
    flag_pend_boot_save_completion environment critical local next_local sg
      original mask saved before first_heap returned current last_heap ->
    flag_pend_selected_event_source environment critical sg
      (flag_pend_task_save_completed_c_event environment critical local next_local (fun _ _ => emp) sg
        original mask saved before first_heap returned current last_heap)
| FlagPendCompletedBootRestore : forall local next_local original saved acquired before first_heap
    returned current last_heap,
    flag_pend_boot_restore_completion environment critical local next_local sg
      original saved acquired before first_heap returned current last_heap ->
    flag_pend_selected_event_source environment critical sg
      (flag_pend_task_restore_completed_c_event environment critical local next_local (fun _ _ => emp) sg
        original saved acquired before first_heap returned current last_heap)
| FlagPendCompletedConsequence : forall event input output,
    flag_pend_selected_event_source environment critical sg event ->
    (event.(flag_pend_event_input) |-- input) ->
    (event.(flag_pend_event_output) |-- output) ->
    flag_pend_selected_event_source environment critical sg
      (flag_pend_event_with_owners event input output).

Lemma flag_pend_selected_event_source_resources : forall environment critical sg event,
  flag_pend_selected_event_source environment critical sg event ->
  event.(flag_pend_event_input) event.(flag_pend_event_first_heap) /\
  event.(flag_pend_event_output) event.(flag_pend_event_last_heap).
Proof.
  intros environment critical sg event Hactual; induction Hactual.
  - eapply ModuleCompletionSource.flag_pend_selected_event_source_resources; eassumption.
  - destruct (flag_pend_boot_save_completion_post _ _ _ _ _ _ _ _ _ _ _ _ _ H)
      as [Hboot [_ [Hnormal [_ [_ [Hin Hout]]]]]].
    split; [exact Hin|]. split; [|exact Hout].
    apply flag_pend_boot_endpoint_from_normal_return; assumption.
  - destruct (flag_pend_boot_restore_completion_post _ _ _ _ _ _ _ _ _ _ _ _ _ H)
      as [Hboot [_ [Hnormal [_ [_ [Hin Hout]]]]]].
    split; [exact Hin|]. split; [|exact Hout].
    apply flag_pend_boot_endpoint_from_normal_return; assumption.
  - destruct IHHactual as [Hin Hout]; split; [apply H|apply H0]; assumption.
Qed.

Definition flag_pend_selected_linked_sources environment critical sg :
  FlagPendProgramSources environment critical sg :=
  {| flag_pend_program_event_source := flag_pend_selected_event_source environment critical sg;
     flag_pend_program_event_resources := flag_pend_selected_event_source_resources environment critical sg |}.

Definition flag_pend_selected_completed_source operation environment critical sg caller original before
  (input : Assertion) first_heap returned_caller returned current last_heap (output : Assertion) : Prop :=
  flag_pend_selected_event_source environment critical sg
    {| flag_pend_event_operation := operation; flag_pend_event_caller := caller;
       flag_pend_event_original := original; flag_pend_event_returned_caller := returned_caller;
       flag_pend_event_returned := returned; flag_pend_event_before := before;
       flag_pend_event_current := current; flag_pend_event_first_heap := first_heap;
       flag_pend_event_last_heap := last_heap; flag_pend_event_input := input;
       flag_pend_event_output :=
         coq_prop (flag_pend_call_endpoint_observations environment sg caller original before returned current) && output |}.

Lemma flag_pend_selected_completed_source_endpoints : forall operation environment critical sg caller original before
  input first_heap returned_caller returned current last_heap output,
  flag_pend_selected_completed_source operation environment critical sg caller original before
    input first_heap returned_caller returned current last_heap output ->
  flag_pend_call_endpoint_observations environment sg caller original before returned current /\
    input first_heap /\ output last_heap.
Proof.
  intros until output; intro Hactual.
  destruct (flag_pend_selected_event_source_resources _ _ _ _ Hactual) as [Hin [Hendpoint Hout]].
  exact (conj Hendpoint (conj Hin Hout)).
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
  intros environment critical sg event Hactual; induction Hactual;
    intros Hcaller Hrange Horiginal Hcache Hnormal Hreturned.
  - eapply ModuleCompletionSource.flag_pend_selected_event_source_current_cache;
      [exact H|exact Hcaller|exact Hrange|exact Horiginal|exact Hcache|exact Hnormal|exact Hreturned].
  - destruct (flag_pend_boot_save_completion_post _ _ _ _ _ _ _ _ _ _ _ _ _ H) as [Hboot _].
    destruct Horiginal as [Horigin _]; cbn in Horigin; rewrite Hboot in Horigin; discriminate.
  - destruct (flag_pend_boot_restore_completion_post _ _ _ _ _ _ _ _ _ _ _ _ _ H) as [Hboot _].
    destruct Horiginal as [Horigin _]; cbn in Horigin; rewrite Hboot in Horigin; discriminate.
  - apply IHHactual; assumption.
Qed.

Lemma flag_pend_task_save_source_from_execution :
  forall environment critical local next_local active sg original mask saved before first_heap stopped returned current last_heap,
  SelectedEnvironmentPhaseEffects.os_sched_continuation_c_save_execution environment critical local next_local active sg
    original mask before first_heap saved stopped returned current last_heap ->
  flag_pend_selected_event_source environment critical sg
    (flag_pend_task_save_completed_c_event environment critical local next_local active sg
      original mask saved before first_heap returned current last_heap).
Proof.
  intros until last_heap; intro Hactual.
  apply (FlagPendCompletedConsequence environment critical sg
    (kernel_c_program_spec.flag_pend_task_save_completed_c_event environment critical local next_local active sg
      original mask saved before first_heap returned current last_heap)).
  - apply FlagPendCompletedModule; eapply ModuleCompletionSource.FlagPendModuleTaskSave; exact Hactual.
  - intros h Hinput; exact Hinput.
  - intros h [Hendpoint Houtput]; split; [|exact Houtput].
    apply flag_pend_endpoint_from_task_observations; exact Hendpoint.
Qed.

Lemma flag_pend_task_restore_source_from_execution :
  forall environment critical local next_local active sg original saved acquired before first_heap stopped returned current last_heap,
  SelectedEnvironmentPhaseEffects.os_sched_continuation_c_restore_execution environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap ->
  flag_pend_selected_event_source environment critical sg
    (flag_pend_task_restore_completed_c_event environment critical local next_local active sg
      original saved acquired before first_heap returned current last_heap).
Proof.
  intros until last_heap; intro Hactual.
  apply (FlagPendCompletedConsequence environment critical sg
    (kernel_c_program_spec.flag_pend_task_restore_completed_c_event environment critical local next_local active sg
      original saved acquired before first_heap returned current last_heap)).
  - apply FlagPendCompletedModule; eapply ModuleCompletionSource.FlagPendModuleTaskRestore; exact Hactual.
  - intros h Hinput; exact Hinput.
  - intros h [Hendpoint Houtput]; split; [|exact Houtput].
    apply flag_pend_endpoint_from_task_observations; exact Hendpoint.
Qed.

Lemma flag_pend_completed_source_from_module : forall environment critical sg event output,
  ModuleCompletionSource.flag_pend_selected_event_source environment critical sg event ->
  (event.(flag_pend_event_output) |--
    coq_prop (flag_pend_call_protocol.flag_pend_call_endpoint_observations environment sg
      event.(flag_pend_event_caller) event.(flag_pend_event_original) event.(flag_pend_event_before)
      event.(flag_pend_event_returned) event.(flag_pend_event_current)) && output) ->
  flag_pend_selected_completed_source event.(flag_pend_event_operation) environment critical sg
    event.(flag_pend_event_caller) event.(flag_pend_event_original) event.(flag_pend_event_before)
    event.(flag_pend_event_input) event.(flag_pend_event_first_heap)
    event.(flag_pend_event_returned_caller) event.(flag_pend_event_returned)
    event.(flag_pend_event_current) event.(flag_pend_event_last_heap) output.
Proof.
  intros environment critical sg event output Hactual Hpost.
  apply (FlagPendCompletedConsequence environment critical sg event).
  - apply FlagPendCompletedModule; exact Hactual.
  - intros h Hinput; exact Hinput.
  - intros h Houtput; destruct (Hpost h Houtput) as [Hendpoint Howned].
    split; [apply flag_pend_endpoint_from_task_observations; exact Hendpoint|exact Howned].
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
  destruct (flag_pend_selected_event_source_resources _ _ _ _ Hactual) as [Hin [Hendpoint Hout]].
  destruct Hendpoint as [_ [_ [_ [Hnormal _]]]].
  eapply (flag_pend_selected_event_source_current_cache environment critical sg
    (flag_pend_task_save_completed_c_event environment critical local next_local active sg
      original mask saved before first_heap returned current last_heap));
    [exact Hactual|reflexivity| |exact Horiginal|exact Hcache|exact Hnormal|exact Hreturned].
  eapply flag_pend_caller_save_input_task_in_range; exact Hin.
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
  destruct (flag_pend_selected_event_source_resources _ _ _ _ Hactual) as [Hin [Hendpoint Hout]].
  destruct Hendpoint as [_ [_ [_ [Hnormal _]]]].
  eapply (flag_pend_selected_event_source_current_cache environment critical sg
    (flag_pend_task_restore_completed_c_event environment critical local next_local active sg
      original saved acquired before first_heap returned current last_heap));
    [exact Hactual|reflexivity| |exact Horiginal|exact Hcache|exact Hnormal|exact Hreturned].
  eapply flag_pend_caller_restore_input_task_in_range; exact Hin.
Qed.

End SelectedEventSources.

Module CompletedCallerSource := SelectedEventSources.
