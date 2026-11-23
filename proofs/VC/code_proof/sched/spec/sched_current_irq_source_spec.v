Require Import Coq.ZArith.ZArith.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_profile_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Import TaskStateDef.
Local Open Scope Z_scope.

(** Both stores of the actual interrupt context switch use the same
    selected destination.  The conclusion is about those stores, not an
    assumed property of the earlier interrupt or foreign execution. *)
Lemma os_int_exit_destination_installs_current_consistency : forall external transfer,
  os_int_exit_destination_binding external transfer ->
  sched_current_consistency (os_int_exit_installed_state transfer).(TskState)
    (os_int_exit_installed_state transfer).(SchedState).
Proof.
  intros external transfer [Hselected [[node [Hnode [Hgeneration [Hpriority Hsp]]]] Hrest]].
  unfold sched_current_consistency.
  destruct (os_int_exit_installed_current_eq transfer)
    as [Hcurrent [Hcache [Htasks Hintr]]].
  rewrite Hcurrent, Hselected.
  exists node; split; [rewrite Htasks; exact Hnode|rewrite Hcache; exact Hpriority].
Qed.

Lemma os_int_exit_checkpoint_preserves_current_consistency : forall observed entry,
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  sched_current_consistency (os_int_exit_ready_checkpoint observed entry).(TskState)
    (os_int_exit_ready_checkpoint observed entry).(SchedState).
Proof.
  intros observed entry Hconsistent.
  destruct (os_int_exit_checkpoint_current_frame observed entry) as [Hcurrent [Hcache Hrunning]].
  destruct (os_int_exit_checkpoint_frame observed entry) as [Htasks Hstate].
  unfold sched_current_consistency in *.
  rewrite Htasks, Hcurrent, Hcache; exact Hconsistent.
Qed.

Lemma os_int_exit_wrapper_take_preserves_current_consistency : forall state incoming,
  sched_current_consistency state.(TskState) state.(SchedState) ->
  sched_current_consistency (os_int_exit_wrapper_restored_state state incoming).(TskState)
    (os_int_exit_wrapper_restored_state state incoming).(SchedState).
Proof. intros; exact H. Qed.

(** Ordinary return consumes the actual post-Save entry observation.
    No transport across the preceding environmental interval is inferred
    merely from validity or from the fact that the call returned. *)
Lemma os_int_exit_full_call_current_consistency :
  forall external port critical sg context before outcome,
  os_int_exit_full_call external port critical sg context before outcome ->
  (forall entry, outcome = OsIntExitReturned entry ->
    sched_current_consistency entry.(TskState) entry.(SchedState)) ->
  sched_current_consistency (os_int_exit_outcome_state before outcome).(TskState)
    (os_int_exit_outcome_state before outcome).(SchedState).
Proof.
  intros external port critical sg context before [entry|entry transfer] Hcall Hentry.
  - apply os_int_exit_checkpoint_preserves_current_consistency.
    apply Hentry; reflexivity.
  - destruct Hcall as [Hrunning [Hinterval Htransfer]].
    unfold os_int_exit_transfer_source in Htransfer.
    apply os_int_exit_destination_installs_current_consistency with (external := external).
    tauto.
Qed.

Lemma os_sched_profile_counts_preserves_current_consistency : forall state slot node,
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  sched_current_consistency state.(TskState) state.(SchedState) ->
  sched_current_consistency (os_sched_profile_counts_state state slot node).(TskState)
    (os_sched_profile_counts_state state slot node).(SchedState).
Proof.
  intros state slot node Hnode Hconsistent.
  apply sched_current_consistency_fields_frame with
    (before_tasks := state.(TskState)) (before := state.(SchedState)); try reflexivity.
  - intros current old Hcurrent Hold.
    destruct (Z.eq_dec current slot) as [->|Hother].
    + rewrite Hnode in Hold; inversion Hold; subst old.
      exists (task_record_context_switch node); split; [|reflexivity].
      cbn [os_sched_profile_counts_state os_sched_profile_global_state os_sched_profile_task_state
        replace_SchedS replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
      rewrite Z.eqb_refl; reflexivity.
    + exists old; split; [|reflexivity].
      cbn [os_sched_profile_counts_state os_sched_profile_global_state os_sched_profile_task_state
        replace_SchedS replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
      rewrite (proj2 (Z.eqb_neq current slot) Hother); exact Hold.
  - exact Hconsistent.
Qed.

(** These are exactly the three existing source cuts in this registry;
    this theorem is not a certificate for an arbitrary registered client. *)
Lemma kernel_full_profile_cut_preserves_current_consistency : forall cut sg before after,
  kernel_client_step (kernel_full_profile_cut_client cut) sg before after ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros cut sg before after [Hinput ->] Hconsistent.
  destruct cut as [|observed|slot node]; cbn in Hinput |- *.
  - exact Hconsistent.
  - exact Hconsistent.
  - apply os_sched_profile_counts_preserves_current_consistency; [exact (proj2 Hinput)|exact Hconsistent].
Qed.

Lemma kernel_full_profile_registered_preserves_current_consistency : forall action sg before after,
  kernel_full_profile_cut_registered action ->
  kernel_client_step action sg before after ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros action sg before after [cut ->] Hstep Hconsistent.
  eapply kernel_full_profile_cut_preserves_current_consistency; eassumption.
Qed.

(** InterruptAbstractState contains exactly nesting and lock counters.
    Equality follows from the two actual enabled endpoint observations;
    it is not a new assumption about every intermediate client step. *)
Lemma os_sched_enabled_endpoints_interrupt_state_eq : forall before after,
  os_sched_selection_enabled before = true ->
  os_sched_selection_enabled after = true -> after.(IntrState) = before.(IntrState).
Proof.
  intros before after Hbefore Hafter.
  apply os_sched_selection_enabled_iff in Hbefore.
  apply os_sched_selection_enabled_iff in Hafter.
  destruct (before.(IntrState)) as [before_int before_lock].
  destruct (after.(IntrState)) as [after_int after_lock].
  cbn in Hbefore, Hafter |- *.
  destruct Hbefore as [-> ->]; destruct Hafter as [-> ->]; reflexivity.
Qed.

Lemma os_sched_enabled_endpoints_control_rely : forall sg before after,
  os_sched_selection_enabled before = true ->
  os_sched_selection_enabled after = true ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning) ->
  kernel_call_control_rely sg before after.
Proof.
  intros sg before after Hbefore Hafter Hrunning; split; [exact Hrunning|].
  apply os_sched_enabled_endpoints_interrupt_state_eq; assumption.
Qed.

Lemma kernel_full_profile_cut_running_eq : forall cut sg before after,
  kernel_client_step (kernel_full_profile_cut_client cut) sg before after ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros cut sg before after [Hinput ->]; destruct cut; reflexivity.
Qed.
