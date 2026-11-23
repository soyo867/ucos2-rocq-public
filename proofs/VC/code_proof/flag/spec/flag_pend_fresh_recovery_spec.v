Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Import UCOS2_C_Rules TaskStateDef PendPhaseCandidate.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagPendFreshRecovery.

(** A field observation for an existing task generation.  It does not
    assert that the task remains live or that execution returns to it.
    Those facts come from the actual completed caller source. *)
Definition flag_pend_fresh_fields_at_origin (origin : TaskInvocationOrigin)
  (state : UCOS2_Verify_State) : Prop :=
  match origin with
  | BootInvocation => True
  | RunningInvocation slot generation =>
      forall task, state.(TskState).(inUsedTaskStates) slot = Some task ->
        task.(taskGeneration) = generation ->
        flag_active_event_clear task /\ task.(tcbFlagNode) = 0
  end.

Lemma flag_pend_fresh_fields_task_state_eq : forall origin before after,
  before.(TskState) = after.(TskState) ->
  (flag_pend_fresh_fields_at_origin origin before <->
   flag_pend_fresh_fields_at_origin origin after).
Proof.
  intros origin before after Htasks; destruct origin; simpl; [tauto|].
  rewrite Htasks; reflexivity.
Qed.

Lemma flag_active_fresh_registration_fields : forall original call state,
  flag_active_fresh_registration original call state ->
  flag_pend_fresh_fields_at_origin original.(os_sched_call_origin) state.
Proof.
  intros original call state [old [Hfields Hnode]].
  destruct Hfields as [Hsame [Horigin [Hlookup [Hgeneration [Hactive Hclear]]]]].
  unfold flag_pend_fresh_fields_at_origin; rewrite Horigin.
  intros task Htask Hgen; assert (task = old) by congruence; subst task; auto.
Qed.

Lemma flag_active_fresh_registration_from_returned_source : forall original returned current,
  task_tcb_init_stack_same_call returned original ->
  kernel_call_task_source returned current ->
  flag_pend_fresh_fields_at_origin original.(os_sched_call_origin) current ->
  flag_active_fresh_registration original returned current.
Proof.
  intros original returned current Hsame Hreturned Hfields.
  pose proof (proj1 (task_tcb_init_stack_same_call_source_iff returned original current Hsame)
    Hreturned) as [Horigin [Hactive Hcurrent]].
  pose proof Hactive as [Hregistered [Hretired Hlive]].
  rewrite Horigin in Hlive.
  destruct Hlive as [task [Hlookup Hgeneration]].
  unfold flag_pend_fresh_fields_at_origin in Hfields; rewrite Horigin in Hfields.
  destruct (Hfields task Hlookup Hgeneration) as [Hclear Hnode].
  exists task; split; [|exact Hnode].
  unfold flag_active_task_fields.
  exact (conj Hsame (conj Horigin (conj Hlookup (conj Hgeneration (conj Hactive Hclear))))).
Qed.

Lemma flag_pend_fresh_observation_from_returned_source : forall original returned current,
  task_tcb_init_stack_same_call returned original ->
  kernel_call_task_source returned current ->
  flag_pend_fresh_fields_at_origin original.(os_sched_call_origin) current ->
  emp |-- flag_pend_fresh_observation original returned current.
Proof.
  intros original returned current Hsame Hsource Hfields heap Hempty; split; [|exact Hempty].
  eapply flag_active_fresh_registration_from_returned_source; eassumption.
Qed.

Lemma flag_pend_first_observation_fields : forall mode original initial call current,
  flag_pend_first_observation mode original initial call current |--
  coq_prop ((flag_pend_valid_mode mode \/ flag_pend_task_entry original initial) ->
    flag_pend_fresh_fields_at_origin original.(os_sched_call_origin) current) &&
  flag_pend_first_observation mode original initial call current.
Proof.
  intros mode original initial call current heap Howned; split; [|exact Howned].
  destruct Howned as [Hregistration Hempty]; intro Hguard.
  apply (flag_active_fresh_registration_fields original call current), Hregistration, Hguard.
Qed.

Lemma flag_pend_first_observation_from_returned_source : forall mode original initial returned current,
  task_tcb_init_stack_same_call returned original ->
  ((flag_pend_valid_mode mode \/ flag_pend_task_entry original initial) ->
    kernel_call_task_source returned current) ->
  ((flag_pend_valid_mode mode \/ flag_pend_task_entry original initial) ->
    flag_pend_fresh_fields_at_origin original.(os_sched_call_origin) current) ->
  emp |-- flag_pend_first_observation mode original initial returned current.
Proof.
  intros mode original initial returned current Hsame Hsource Hfields heap Hempty.
  split; [|exact Hempty]; intro Hguard.
  eapply flag_active_fresh_registration_from_returned_source;
    [exact Hsame|apply Hsource; exact Hguard|apply Hfields; exact Hguard].
Qed.

End FlagPendFreshRecovery.
