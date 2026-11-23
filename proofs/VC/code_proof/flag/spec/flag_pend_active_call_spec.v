Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_phase_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_call_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_inactive_view_primitive_spec.

Module FlagPendActiveCaller.
Import PrimitiveComponent FlagPendInactiveViewPrimitive.

Definition flag_pend_caller_save_observation environment critical
  (active : OsSchedCallContext -> UCOS2_Verify_State -> Assertion) sg caller original
  returned_caller returned mask saved before current : Prop :=
  CompletedCallerEvents.flag_pend_caller_save_observation environment critical sg
    caller original returned_caller returned mask saved before current \/
  (active = (fun _ _ => emp) /\ caller = FlagPendTaskCaller original /\
   returned_caller = FlagPendTaskCaller returned /\
   flag_pend_inactive_save_effect environment critical sg original mask saved before returned current).

Definition flag_pend_caller_restore_observation environment critical
  (active : OsSchedCallContext -> UCOS2_Verify_State -> Assertion) sg caller original
  returned_caller returned before current : Prop :=
  CompletedCallerEvents.flag_pend_caller_restore_observation environment critical sg
    caller original returned_caller returned before current \/
  (active = (fun _ _ => emp) /\ caller = FlagPendTaskCaller original /\
   returned_caller = FlagPendTaskCaller returned /\
   flag_pend_inactive_restore_effect environment critical sg original before returned current).

Definition flag_pend_caller_endpoint_observations environment
  (active : OsSchedCallContext -> UCOS2_Verify_State -> Assertion) sg caller original before returned current : Prop :=
  active <> (fun _ _ => emp) ->
  flag_pend_call_protocol.flag_pend_call_endpoint_observations environment sg caller original before returned current.

(** The first branch retains the complete, source-indexed Task/view contract.
    The second branch holds the same approved physical View completion, and is
    available only when the actual resource argument is emp. *)
Definition flag_pend_selected_caller_save_event environment critical local active sg
  caller original mask saved before returned_caller returned current next_local
  (first_heap last_heap : model) : Prop :=
  CompletedCallerEvents.flag_pend_selected_caller_save_event environment critical local active sg
    caller original mask saved before returned_caller returned current next_local first_heap last_heap \/
  (active = (fun _ _ => emp) /\ caller = FlagPendTaskCaller original /\
   returned_caller = FlagPendTaskCaller returned /\
   flag_pend_inactive_save_completion environment critical local next_local sg
     original mask saved before first_heap returned current last_heap).

Definition flag_pend_selected_caller_restore_event environment critical local active sg
  caller original saved acquired before returned_caller returned current next_local
  (first_heap last_heap : model) : Prop :=
  CompletedCallerEvents.flag_pend_selected_caller_restore_event environment critical local active sg
    caller original saved acquired before returned_caller returned current next_local first_heap last_heap \/
  (active = (fun _ _ => emp) /\ caller = FlagPendTaskCaller original /\
   returned_caller = FlagPendTaskCaller returned /\
   flag_pend_inactive_restore_completion environment critical local next_local sg
     original saved acquired before first_heap returned current last_heap).

Definition flag_pend_selected_caller_save_output environment critical local active sg
  caller original mask before first_heap saved : Assertion :=
  fun last_heap => exists returned_caller returned current next_local,
    flag_pend_selected_caller_save_event environment critical local active sg
      caller original mask saved before returned_caller returned current next_local first_heap last_heap.

Definition flag_pend_selected_caller_restore_output environment critical local active sg
  caller original saved acquired before first_heap : Assertion :=
  fun last_heap => exists returned_caller returned current next_local,
    flag_pend_selected_caller_restore_event environment critical local active sg
      caller original saved acquired before returned_caller returned current next_local first_heap last_heap.

Lemma flag_pend_completed_save_output_included :
  forall environment critical local active sg caller original mask before first_heap saved,
  CompletedCallerEvents.flag_pend_selected_caller_save_output environment critical local active sg
    caller original mask before first_heap saved |--
  flag_pend_selected_caller_save_output environment critical local active sg
    caller original mask before first_heap saved.
Proof.
  intros until saved; intros last_heap [returned_caller [returned [current [next_local Hevent]]]].
  exists returned_caller, returned, current, next_local; left; exact Hevent.
Qed.

Lemma flag_pend_completed_restore_output_included :
  forall environment critical local active sg caller original saved acquired before first_heap,
  CompletedCallerEvents.flag_pend_selected_caller_restore_output environment critical local active sg
    caller original saved acquired before first_heap |--
  flag_pend_selected_caller_restore_output environment critical local active sg
    caller original saved acquired before first_heap.
Proof.
  intros until first_heap; intros last_heap [returned_caller [returned [current [next_local Hevent]]]].
  exists returned_caller, returned, current, next_local; left; exact Hevent.
Qed.

Lemma flag_pend_completed_save_event_included :
  forall environment critical local active sg caller original mask saved before
    returned_caller returned current next_local first_heap last_heap,
  CompletedCallerEvents.flag_pend_selected_caller_save_event environment critical local active sg
    caller original mask saved before returned_caller returned current next_local first_heap last_heap ->
  flag_pend_selected_caller_save_event environment critical local active sg
    caller original mask saved before returned_caller returned current next_local first_heap last_heap.
Proof. intros; left; assumption. Qed.

Lemma flag_pend_completed_restore_event_included :
  forall environment critical local active sg caller original saved acquired before
    returned_caller returned current next_local first_heap last_heap,
  CompletedCallerEvents.flag_pend_selected_caller_restore_event environment critical local active sg
    caller original saved acquired before returned_caller returned current next_local first_heap last_heap ->
  flag_pend_selected_caller_restore_event environment critical local active sg
    caller original saved acquired before returned_caller returned current next_local first_heap last_heap.
Proof. intros; left; assumption. Qed.

Lemma flag_pend_inactive_save_event_from_completion :
  forall environment critical local next_local sg original mask saved before first_heap returned current last_heap,
  flag_pend_inactive_save_completion environment critical local next_local sg
    original mask saved before first_heap returned current last_heap ->
  flag_pend_selected_caller_save_event environment critical local (fun _ _ => emp) sg
    (FlagPendTaskCaller original) original mask saved before
    (FlagPendTaskCaller returned) returned current next_local first_heap last_heap.
Proof. intros; right; repeat split; assumption || reflexivity. Qed.

Lemma flag_pend_inactive_restore_event_from_completion :
  forall environment critical local next_local sg original saved acquired before first_heap returned current last_heap,
  flag_pend_inactive_restore_completion environment critical local next_local sg
    original saved acquired before first_heap returned current last_heap ->
  flag_pend_selected_caller_restore_event environment critical local (fun _ _ => emp) sg
    (FlagPendTaskCaller original) original saved acquired before
    (FlagPendTaskCaller returned) returned current next_local first_heap last_heap.
Proof. intros; right; repeat split; assumption || reflexivity. Qed.

Lemma flag_pend_save_event_nonempty :
  forall environment critical local active sg caller original mask saved before
    returned_caller returned current next_local first_heap last_heap,
  active <> (fun _ _ => emp) ->
  flag_pend_selected_caller_save_event environment critical local active sg
    caller original mask saved before returned_caller returned current next_local first_heap last_heap ->
  CompletedCallerEvents.flag_pend_selected_caller_save_event environment critical local active sg
    caller original mask saved before returned_caller returned current next_local first_heap last_heap.
Proof. intros until last_heap; intros Hactive [Hstrong|[Hempty Hrest]]; [exact Hstrong|contradiction]. Qed.

Lemma flag_pend_restore_event_nonempty :
  forall environment critical local active sg caller original saved acquired before
    returned_caller returned current next_local first_heap last_heap,
  active <> (fun _ _ => emp) ->
  flag_pend_selected_caller_restore_event environment critical local active sg
    caller original saved acquired before returned_caller returned current next_local first_heap last_heap ->
  CompletedCallerEvents.flag_pend_selected_caller_restore_event environment critical local active sg
    caller original saved acquired before returned_caller returned current next_local first_heap last_heap.
Proof. intros until last_heap; intros Hactive [Hstrong|[Hempty Hrest]]; [exact Hstrong|contradiction]. Qed.

Lemma flag_pend_save_output_nonempty :
  forall environment critical local active sg caller original mask before first_heap saved,
  active <> (fun _ _ => emp) ->
  flag_pend_selected_caller_save_output environment critical local active sg caller original mask before first_heap saved |--
  CompletedCallerEvents.flag_pend_selected_caller_save_output environment critical local active sg
    caller original mask before first_heap saved.
Proof.
  intros until saved; intros Hactive last_heap [returned_caller [returned [current [next_local Hevent]]]].
  exists returned_caller, returned, current, next_local.
  eapply flag_pend_save_event_nonempty; eassumption.
Qed.

Lemma flag_pend_restore_output_nonempty :
  forall environment critical local active sg caller original saved acquired before first_heap,
  active <> (fun _ _ => emp) ->
  flag_pend_selected_caller_restore_output environment critical local active sg caller original saved acquired before first_heap |--
  CompletedCallerEvents.flag_pend_selected_caller_restore_output environment critical local active sg
    caller original saved acquired before first_heap.
Proof.
  intros until first_heap; intros Hactive last_heap [returned_caller [returned [current [next_local Hevent]]]].
  exists returned_caller, returned, current, next_local.
  eapply flag_pend_restore_event_nonempty; eassumption.
Qed.

Lemma flag_pend_save_event_resources :
  forall environment critical local active sg caller original mask saved before
    returned_caller returned current next_local first_heap last_heap,
  flag_pend_selected_caller_save_event environment critical local active sg
    caller original mask saved before returned_caller returned current next_local first_heap last_heap ->
  interrupt_saved_value mask saved /\
  flag_pend_caller_save_input environment critical local active sg caller original mask before first_heap /\
  flag_pend_caller_restore_input environment critical next_local active sg
    returned_caller returned saved current current last_heap.
Proof.
  intros until last_heap; intros [Hstrong|[Hempty [Hcaller [Hreturned Hcomplete]]]].
  - destruct Hstrong as [_ [Hsaved [Hinput [Houtput _]]]].
    exact (conj Hsaved (conj Hinput Houtput)).
  - subst active caller returned_caller.
    exact (proj2 (proj2 (flag_pend_inactive_save_completion_post environment critical local next_local sg
      original mask saved before first_heap returned current last_heap Hcomplete))).
Qed.

Lemma flag_pend_restore_event_resources :
  forall environment critical local active sg caller original saved acquired before
    returned_caller returned current next_local first_heap last_heap,
  flag_pend_selected_caller_restore_event environment critical local active sg
    caller original saved acquired before returned_caller returned current next_local first_heap last_heap ->
  flag_pend_caller_restore_input environment critical local active sg caller original saved acquired before first_heap /\
  flag_pend_caller_save_input environment critical next_local active sg
    returned_caller returned (armv7a_irq_fiq_mask saved) current last_heap.
Proof.
  intros until last_heap; intros [Hstrong|[Hempty [Hcaller [Hreturned Hcomplete]]]].
  - destruct Hstrong as [_ [Hinput [Houtput _]]]. exact (conj Hinput Houtput).
  - subst active caller returned_caller.
    exact (proj2 (proj2 (flag_pend_inactive_restore_completion_post environment critical local next_local sg
      original saved acquired before first_heap returned current last_heap Hcomplete))).
Qed.

Lemma flag_pend_task_save_event_effect :
  forall environment critical local active sg original mask saved before
    returned_caller returned current next_local first_heap last_heap,
  flag_pend_selected_caller_save_event environment critical local active sg
    (FlagPendTaskCaller original) original mask saved before
    returned_caller returned current next_local first_heap last_heap ->
  returned_caller = FlagPendTaskCaller returned /\ task_tcb_init_stack_same_call returned original /\
  (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect environment critical sg
     original mask saved before returned current \/
   flag_pend_inactive_save_effect environment critical sg original mask saved before returned current).
Proof.
  intros until last_heap; intros [Hstrong|[Hempty [_ [Hcaller Hcomplete]]]].
  - destruct Hstrong as [Hobs Hrest].
    destruct returned_caller as [actual|view key]; cbn [CompletedCallerEvents.flag_pend_caller_save_observation] in Hobs;
      [|contradiction].
    destruct Hobs as [_ [Heq [Heffect [Hsame Hsource]]]]. subst actual.
    exact (conj eq_refl (conj Hsame (or_introl Heffect))).
  - split; [exact Hcaller|].
    pose proof (flag_pend_inactive_save_completion_effect environment critical local next_local sg
      original mask saved before first_heap returned current last_heap Hcomplete) as Heffect.
    exact (conj (proj1 (flag_pend_inactive_save_effect_observations _ _ _ _ _ _ _ _ _ Heffect))
      (or_intror Heffect)).
Qed.

Lemma flag_pend_task_restore_event_effect :
  forall environment critical local active sg original saved acquired before
    returned_caller returned current next_local first_heap last_heap,
  flag_pend_selected_caller_restore_event environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before
    returned_caller returned current next_local first_heap last_heap ->
  returned_caller = FlagPendTaskCaller returned /\ task_tcb_init_stack_same_call returned original /\
  (ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect environment critical sg
     original before returned current \/
   flag_pend_inactive_restore_effect environment critical sg original before returned current).
Proof.
  intros until last_heap; intros [Hstrong|[Hempty [_ [Hcaller Hcomplete]]]].
  - destruct Hstrong as [Hobs Hrest].
    destruct returned_caller as [actual|view key]; cbn [CompletedCallerEvents.flag_pend_caller_restore_observation] in Hobs;
      [|contradiction].
    destruct Hobs as [_ [Heq [Heffect [Hsame Hsource]]]]. subst actual.
    exact (conj eq_refl (conj Hsame (or_introl Heffect))).
  - split; [exact Hcaller|].
    pose proof (flag_pend_inactive_restore_completion_effect environment critical local next_local sg
      original saved acquired before first_heap returned current last_heap Hcomplete) as Heffect.
    exact (conj (proj1 (flag_pend_inactive_restore_effect_observations _ _ _ _ _ _ _ Heffect))
      (or_intror Heffect)).
Qed.

Lemma flag_pend_save_event_output :
  forall environment critical local active sg caller original mask saved before
    returned_caller returned current next_local first_heap last_heap,
  flag_pend_selected_caller_save_event environment critical local active sg
    caller original mask saved before returned_caller returned current next_local first_heap last_heap ->
  flag_pend_selected_caller_save_output environment critical local active sg caller original mask before first_heap saved last_heap.
Proof. intros; exists returned_caller, returned, current, next_local; assumption. Qed.

Lemma flag_pend_restore_event_output :
  forall environment critical local active sg caller original saved acquired before
    returned_caller returned current next_local first_heap last_heap,
  flag_pend_selected_caller_restore_event environment critical local active sg
    caller original saved acquired before returned_caller returned current next_local first_heap last_heap ->
  flag_pend_selected_caller_restore_output environment critical local active sg caller original saved acquired before first_heap last_heap.
Proof. intros; exists returned_caller, returned, current, next_local; assumption. Qed.

Lemma flag_pend_inactive_save_output_from_completion :
  forall environment critical local next_local sg original mask saved before first_heap returned current last_heap,
  flag_pend_inactive_save_completion environment critical local next_local sg
    original mask saved before first_heap returned current last_heap ->
  flag_pend_selected_caller_save_output environment critical local (fun _ _ => emp) sg
    (FlagPendTaskCaller original) original mask before first_heap saved last_heap.
Proof. intros; eapply flag_pend_save_event_output; eapply flag_pend_inactive_save_event_from_completion; eassumption. Qed.

Lemma flag_pend_inactive_restore_output_from_completion :
  forall environment critical local next_local sg original saved acquired before first_heap returned current last_heap,
  flag_pend_inactive_restore_completion environment critical local next_local sg
    original saved acquired before first_heap returned current last_heap ->
  flag_pend_selected_caller_restore_output environment critical local (fun _ _ => emp) sg
    (FlagPendTaskCaller original) original saved acquired before first_heap last_heap.
Proof. intros; eapply flag_pend_restore_event_output; eapply flag_pend_inactive_restore_event_from_completion; eassumption. Qed.

Lemma flag_pend_save_event_observation :
  forall environment critical local active sg caller original mask saved before
    returned_caller returned current next_local first_heap last_heap,
  flag_pend_selected_caller_save_event environment critical local active sg
    caller original mask saved before returned_caller returned current next_local first_heap last_heap ->
  flag_pend_caller_save_observation environment critical active sg
    caller original returned_caller returned mask saved before current.
Proof.
  intros until last_heap; intros [Hstrong|[Hempty [Hcaller [Hreturned Hcomplete]]]].
  - left; exact (proj1 Hstrong).
  - right; refine (conj Hempty (conj Hcaller (conj Hreturned _))).
    eapply flag_pend_inactive_save_completion_effect; exact Hcomplete.
Qed.

Lemma flag_pend_restore_event_observation :
  forall environment critical local active sg caller original saved acquired before
    returned_caller returned current next_local first_heap last_heap,
  flag_pend_selected_caller_restore_event environment critical local active sg
    caller original saved acquired before returned_caller returned current next_local first_heap last_heap ->
  flag_pend_caller_restore_observation environment critical active sg
    caller original returned_caller returned before current.
Proof.
  intros until last_heap; intros [Hstrong|[Hempty [Hcaller [Hreturned Hcomplete]]]].
  - left; exact (proj1 Hstrong).
  - right; refine (conj Hempty (conj Hcaller (conj Hreturned _))).
    eapply flag_pend_inactive_restore_completion_effect; exact Hcomplete.
Qed.

Lemma flag_pend_save_observation_nonempty :
  forall environment critical active sg caller original returned_caller returned mask saved before current,
  active <> (fun _ _ => emp) ->
  flag_pend_caller_save_observation environment critical active sg
    caller original returned_caller returned mask saved before current ->
  CompletedCallerEvents.flag_pend_caller_save_observation environment critical sg
    caller original returned_caller returned mask saved before current.
Proof. intros until current; intros Hactive [Hobs|[Hempty Hrest]]; [exact Hobs|contradiction]. Qed.

Lemma flag_pend_restore_observation_nonempty :
  forall environment critical active sg caller original returned_caller returned before current,
  active <> (fun _ _ => emp) ->
  flag_pend_caller_restore_observation environment critical active sg
    caller original returned_caller returned before current ->
  CompletedCallerEvents.flag_pend_caller_restore_observation environment critical sg
    caller original returned_caller returned before current.
Proof. intros until current; intros Hactive [Hobs|[Hempty Hrest]]; [exact Hobs|contradiction]. Qed.

Lemma flag_pend_selected_caller_save_output_open :
  forall environment critical local active sg caller original mask before before_heap saved,
  flag_pend_selected_caller_save_output environment critical local active sg caller original mask before before_heap saved |--
  EX returned_caller returned acquired next_local,
    coq_prop (flag_pend_caller_save_observation environment critical active sg
      caller original returned_caller returned mask saved before acquired /\ interrupt_saved_value mask saved /\
      flag_pend_caller_endpoint_observations environment active sg caller original before returned acquired) &&
    flag_pend_caller_restore_input environment critical next_local active sg
      returned_caller returned saved acquired acquired.
Proof.
  intros environment critical local active sg caller original mask before before_heap saved heap
    [returned_caller [returned [acquired [next_local Hevent]]]].
  destruct (flag_pend_save_event_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hevent)
    as [Hsaved [Hin Hout]].
  exists returned_caller, returned, acquired, next_local; split; [|exact Hout].
  split; [eapply flag_pend_save_event_observation; exact Hevent|].
  split; [exact Hsaved|]. intros Hactive.
  pose proof (flag_pend_save_event_nonempty _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactive Hevent)
    as [_ [_ [_ [_ Hsource]]]].
  exact (proj1 (CompletedCallerSource.flag_pend_selected_completed_source_endpoints
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsource)).
Qed.

Lemma flag_pend_selected_caller_restore_output_open :
  forall environment critical local active sg caller original saved acquired before before_heap,
  flag_pend_selected_caller_restore_output environment critical local active sg caller original saved acquired before before_heap |--
  EX returned_caller returned current next_local,
    coq_prop (flag_pend_caller_restore_observation environment critical active sg
      caller original returned_caller returned before current /\
      flag_pend_caller_endpoint_observations environment active sg caller original before returned current) &&
    flag_pend_caller_save_input environment critical next_local active sg
      returned_caller returned (armv7a_irq_fiq_mask saved) current.
Proof.
  intros environment critical local active sg caller original saved acquired before before_heap heap
    [returned_caller [returned [current [next_local Hevent]]]].
  destruct (flag_pend_restore_event_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hevent)
    as [Hin Hout].
  exists returned_caller, returned, current, next_local; split; [|exact Hout].
  split; [eapply flag_pend_restore_event_observation; exact Hevent|]. intros Hactive.
  pose proof (flag_pend_restore_event_nonempty _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactive Hevent)
    as [_ [_ [_ Hsource]]].
  exact (proj1 (CompletedCallerSource.flag_pend_selected_completed_source_endpoints
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsource)).
Qed.

Lemma flag_pend_task_save_observation_effect :
  forall environment critical active sg original returned_caller returned mask saved before current,
  flag_pend_caller_save_observation environment critical active sg
    (FlagPendTaskCaller original) original returned_caller returned mask saved before current ->
  returned_caller = FlagPendTaskCaller returned /\ task_tcb_init_stack_same_call returned original /\
  (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect environment critical sg
     original mask saved before returned current \/
   flag_pend_inactive_save_effect environment critical sg original mask saved before returned current).
Proof.
  intros until current; intros [Hobs|[Hempty [_ [Hcaller Heffect]]]].
  - destruct returned_caller as [actual|view key]; cbn [CompletedCallerEvents.flag_pend_caller_save_observation] in Hobs;
      [|contradiction].
    destruct Hobs as [_ [Heq [Heffect [Hsame Hsource]]]]. subst actual.
    exact (conj eq_refl (conj Hsame (or_introl Heffect))).
  - exact (conj Hcaller (conj
      (proj1 (flag_pend_inactive_save_effect_observations _ _ _ _ _ _ _ _ _ Heffect))
      (or_intror Heffect))).
Qed.

Lemma flag_pend_task_restore_observation_effect :
  forall environment critical active sg original returned_caller returned before current,
  flag_pend_caller_restore_observation environment critical active sg
    (FlagPendTaskCaller original) original returned_caller returned before current ->
  returned_caller = FlagPendTaskCaller returned /\ task_tcb_init_stack_same_call returned original /\
  (ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect environment critical sg
     original before returned current \/
   flag_pend_inactive_restore_effect environment critical sg original before returned current).
Proof.
  intros until current; intros [Hobs|[Hempty [_ [Hcaller Heffect]]]].
  - destruct returned_caller as [actual|view key]; cbn [CompletedCallerEvents.flag_pend_caller_restore_observation] in Hobs;
      [|contradiction].
    destruct Hobs as [_ [Heq [Heffect [Hsame Hsource]]]]. subst actual.
    exact (conj eq_refl (conj Hsame (or_introl Heffect))).
  - exact (conj Hcaller (conj
      (proj1 (flag_pend_inactive_restore_effect_observations _ _ _ _ _ _ _ Heffect))
      (or_intror Heffect))).
Qed.

End FlagPendActiveCaller.
