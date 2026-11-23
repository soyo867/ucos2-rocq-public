Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_profile_heap_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** These are named SOURCE CUTS, not an all-kernel/environment certificate.
    IntExit ends before scheduling and restore; profile counts begin after
    the real high-ready selection and end before the switch. Nothing below
    says that an arbitrary handler, user call or BSP preserves OS state. *)
Inductive KernelFullProfileSourceCut : Type :=
| KernelFullIntEnter
| KernelFullIntExitCounter (observed_running : bool)
| KernelFullProfileCounts (slot : TaskID) (node : TaskAbstractState).

Definition kernel_full_profile_cut_input (cut : KernelFullProfileSourceCut)
  (state : UCOS2_Verify_State) : Prop :=
  match cut with
  | KernelFullProfileCounts slot node =>
      state.(SchedState).(highRdyTid) = Some slot /\
      state.(TskState).(inUsedTaskStates) slot = Some node
  | _ => True
  end.

Definition kernel_full_profile_cut_state (cut : KernelFullProfileSourceCut)
  (state : UCOS2_Verify_State) : UCOS2_Verify_State :=
  match cut with
  | KernelFullIntEnter => os_int_enter_state state
  | KernelFullIntExitCounter observed => os_int_exit_counter_state observed state
  | KernelFullProfileCounts slot node => os_sched_profile_counts_state state slot node
  end.

Definition kernel_full_profile_cut_client (cut : KernelFullProfileSourceCut)
  : KernelClientAction :=
  {| kernel_client_actor := None;
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun _ before after =>
       kernel_full_profile_cut_input cut before /\
       after = kernel_full_profile_cut_state cut before |}.

Lemma kernel_full_profile_cut_preserves_resources : forall cut,
  kernel_client_preserves_resources UCOS2_full_state_inv
    (kernel_full_profile_cut_client cut).
Proof.
  intros cut sg before after Hvalid [Hinput ->].
  destruct cut as [|observed|slot node]; cbn in Hinput |- *.
  - split; [exact Hvalid|]. split; [intros; reflexivity|].
    split; [intros; reflexivity|intros; assumption].
  - split; [exact Hvalid|]. split; [intros; reflexivity|].
    split; [intros; reflexivity|intros; assumption].
  - destruct Hinput as [Hhigh Hnode].
    split.
    + eapply os_sched_profile_counts_preserves_full_validity; eassumption.
    + split; [intros; reflexivity|]. split; [intros; reflexivity|].
      intros observer origin Hnormal Hactive.
      unfold os_sched_profile_counts_state, os_sched_profile_global_state,
        os_sched_profile_task_state; cbn [replace_SchedS replace_TskS TskState].
      eapply glob_task_set_usedtask_preserves_invocation_active;
        [exact Hnode|reflexivity|exact Hactive].
Qed.

(** The registry enumerates exactly the proved cuts. Extending it requires
    another source instance and its memory binding; membership is not an
    arbitrary proposition asserting preservation of the desired invariant. *)
Definition kernel_full_profile_cut_registered (action : KernelClientAction) : Prop :=
  exists cut, action = kernel_full_profile_cut_client cut.

Lemma kernel_full_profile_registered_preserves_resources : forall action,
  kernel_full_profile_cut_registered action ->
  kernel_client_preserves_resources UCOS2_full_state_inv action.
Proof.
  intros action [cut ->]; apply kernel_full_profile_cut_preserves_resources.
Qed.

Definition kernel_full_profile_cut_fragment (sg : StableGlobVars)
  (cut : KernelFullProfileSourceCut) (state : UCOS2_Verify_State)
  (before after : model) : Prop :=
  match cut with
  | KernelFullIntEnter =>
      kernel_heap_execution (os_int_enter_heap_writes sg state) before after
  | KernelFullIntExitCounter observed =>
      kernel_heap_execution (os_int_exit_counter_heap_writes sg observed state) before after
  | KernelFullProfileCounts _ _ => os_sched_profile_counts_fragment sg before after
  end.

Lemma kernel_full_profile_cut_produces_heap : forall sg cut state (frame : Assertion) before,
  kernel_full_profile_cut_input cut state ->
  (UCOS2_full_inv sg state ** frame) before ->
  exists after,
    kernel_full_profile_cut_fragment sg cut state before after /\
    (UCOS2_full_inv sg (kernel_full_profile_cut_state cut state) ** frame) after.
Proof.
  intros sg cut state frame before Hinput Hbefore.
  destruct cut as [|observed|slot node]; cbn in Hinput |- *.
  - destruct Hbefore as [owned [rest [Hjoin [Hinv Hframe]]]].
    destruct (os_int_enter_source_heap_full_profile_post sg state owned Hinv)
      as [post [Hrun Hpost]].
    destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin)
      as [after [Hwhole Hjoined]].
    exists after; split; [exact Hwhole|].
    exists post, rest; split; [exact Hjoined|]; split; assumption.
  - destruct Hbefore as [owned [rest [Hjoin [Hinv Hframe]]]].
    destruct (os_int_exit_counter_heap_full_profile_post sg observed state owned Hinv)
      as [post [Hrun Hpost]].
    destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin)
      as [after [Hwhole Hjoined]].
    exists after; split; [exact Hwhole|].
    exists post, rest; split; [exact Hjoined|]; split; assumption.
  - destruct Hinput as [Hhigh Hnode].
    eapply os_sched_profile_counts_full_frame_post; eassumption.
Qed.

Lemma kernel_full_profile_cut_fragment_deterministic : forall sg cut state before first second,
  kernel_full_profile_cut_fragment sg cut state before first ->
  kernel_full_profile_cut_fragment sg cut state before second -> first = second.
Proof.
  intros sg cut state before first second Hfirst Hsecond; destruct cut;
    cbn in Hfirst, Hsecond.
  - eapply kernel_heap_execution_deterministic; eassumption.
  - eapply kernel_heap_execution_deterministic; eassumption.
  - eapply os_sched_profile_counts_fragment_deterministic; eassumption.
Qed.

(** Consumes the ACTUAL endpoint of the source writes. The existential
    producer cannot be substituted for an unrelated concrete after heap. *)
Lemma kernel_full_profile_cut_preserves_heap : forall sg cut state (frame : Assertion) before after,
  kernel_full_profile_cut_input cut state ->
  (UCOS2_full_inv sg state ** frame) before ->
  kernel_full_profile_cut_fragment sg cut state before after ->
  (UCOS2_full_inv sg (kernel_full_profile_cut_state cut state) ** frame) after.
Proof.
  intros sg cut state frame before after Hinput Hbefore Hsource.
  destruct (kernel_full_profile_cut_produces_heap sg cut state frame before Hinput Hbefore)
    as [produced [Hproduced Hpost]].
  replace after with produced by
    (eapply kernel_full_profile_cut_fragment_deterministic; eassumption).
  exact Hpost.
Qed.

Lemma kernel_full_profile_registered_trace_preserves_invariant :
  forall sg observer event_observer before stopped after,
  kernel_resumption_resource_trace kernel_full_profile_cut_registered sg
    observer event_observer before stopped after ->
  UCOS2_full_state_inv sg before ->
  UCOS2_full_state_inv sg after.
Proof.
  intros sg observer event_observer before stopped after Htrace Hbefore.
  exact (proj1 (kernel_resumption_resource_trace_transports_invariant
    UCOS2_full_state_inv kernel_full_profile_cut_registered sg observer event_observer
    before stopped after kernel_full_profile_registered_preserves_resources Htrace Hbefore)).
Qed.
