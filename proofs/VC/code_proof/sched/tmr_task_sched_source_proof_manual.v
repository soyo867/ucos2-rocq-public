(** Current Timer Scheduler manual candidate; all 22 targets require a fresh fixed check. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From Ucos2Verify.VC.code.sched Require Import tmr_task_sched_source_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec Ucos2Verify.VC.code.sched.spec.sched_task_return_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_sched_phase_spec.
Local Open Scope sac.


Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_sched_phase_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_call_spec.
Import PrimitiveComponent ContinuationPhaseEffects.
Import SchedulerPhaseCandidate SchedulerActivePhaseComponent SchedulerCalleePhaseComponent.
Import SchedulerPairedPhaseComponent SchedulerRestorePhaseComponent SelectedCallerPhaseComponent.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Require Import Ucos2Verify.VC.code.sched.tmr_task_sched_source_proof_auto.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_proof_helpers.

Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_entry_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_local_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_counter_entry_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_caller_control_spec.

Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_caller_control_spec.

Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_completed_caller_signal_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_signal_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.

Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_sched_source_call_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_sched_entry_call_spec.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.

Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_sched_source_call_spec.

Lemma proof_of_OS_Sched_entail_wit_1 : tmr_task_sched_source_goal.OS_Sched_entail_wit_1.
Proof.
  unfold OS_Sched_entail_wit_1; left.
  intros before mask context sg critical active local environment entry_heap retval save_caller save_scheduled save_entry save_local save_after_heap active_before Hsignal_17 Hidle_entry_18 Hnonidle_entry_19 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 Hsignal_24 Hidle_entry_27 Hnonidle_entry_28 PreH7 PreH8 Hsource_coverage_27 PreH9 PreH10 PreH11 PreH12 Hsignal_32 PreH28 Hnonidle_entry_38 PreH13 PreH14 PreH15 PreH16 Hrequires_control1 PreH17 PreH18 PreH19 PreH20 Hsignal_42 Hidle_entry_49 Hnonidle_entry_50 PreH21 Hsource_coverage_44 PreH22 PreH23 Hrequires_control2 PreH24 PreH25 PreH26 PreH27 PreH29 heap [active_after
    [unmap_after [Hjoin [Hactive Hunmap]]]].

  pose proof (SchedulerSelectedSave.os_sched_task_save_observation_from_selected_c_event
    (task_sw_hook_call_environment environment) critical local save_local active sg
    context mask retval before save_caller save_scheduled save_entry entry_heap save_after_heap
    PreH1 PreH15 PreH5 PreH6) as Hsave_observation.
  pose proof Hsave_observation as
    [Heffect [Hsame [Hsaved [Hpreserved [Hcut [Hcache [Hnormal Hcontrol]]]]]]].
  pose proof (SchedulerPhaseCandidate.os_sched_task_save_preserves_entry
    (task_sw_hook_call_environment environment) critical sg context mask retval
    before save_scheduled save_entry Hsave_observation
    (proj1 PreH14) (proj1 (proj2 PreH14)) (proj2 (proj2 PreH14)))
    as Hreturned_entry.
  assert (Hrunning : save_entry.(SchedState).(isRunning) = true).
  { rewrite (proj1 PreH4); exact PreH13. }

  (** The captured full entry heap and the actual active subheap remain
      distinct.  The following resources come from the latter's output. *)
  pose proof Hactive as [_ [_ [_ [_ [_ [_ Hrestore]]]]]].
  pose proof (proj1 (os_sched_active_restore_input_state_inv
    (task_sw_hook_call_environment environment) critical save_local active sg
    save_scheduled retval save_entry save_entry active_after Hrestore)) as Hvalid.
  assert (Hcoverage : task_stack_live_coverage save_entry.(TskState)
    (task_stack_call_active_key save_scheduled)).
  { destruct Hrestore as [fields_heap [receipt_heap [_ [[Hcoverage _] _]]]].
    exact Hcoverage. }
  assert (Hrestore_owned :
    (os_sched_active_restore_input (task_sw_hook_call_environment environment)
      critical save_local active sg save_scheduled retval save_entry save_entry **
      unmap_table_rep sg) heap).
  { exists active_after, unmap_after; split; [exact Hjoin|].
    split; assumption. }

  assert (Hopen :
    os_sched_active_restore_input (task_sw_hook_call_environment environment)
      critical save_local active sg save_scheduled retval save_entry save_entry **
      unmap_table_rep sg |--
    critical_region_masked
      (task_stack_call_platform (task_sw_hook_call_environment environment))
      critical sg (os_sched_call_invocation save_scheduled)
      (os_sched_call_origin save_scheduled) retval save_entry **
    task_tcb_init_stack_context (task_sw_hook_call_environment environment) save_scheduled **
    os_sched_fields_capsules (task_sw_hook_call_environment environment) save_local save_entry **
    active save_scheduled save_entry **
    ((&("OSIntNesting")) # UChar |-> os_sched_ints save_entry) **
    ((&("OSLockNesting")) # UChar |-> os_sched_locks save_entry) **
    sched_new_rep sg (os_sched_group save_entry) (os_sched_rows save_entry)
      (os_sched_old_high save_entry) **
    PtrArray.full (&("OSTCBPrioTbl")) 64 (os_sched_table sg save_entry) **
    ((&("OSPrioCur")) # UChar |-> os_sched_current save_entry) **
    ((&("OSTCBHighRdy")) # Ptr |-> os_sched_old_pointer sg save_entry) **
    ((&("OSCtxSwCtr")) # UInt |-> os_sched_counter save_entry) **
    os_sched_fields_work_frame sg save_entry).
  { pose proof (proj1 (os_sched_fields_work_cells_entry_equiv sg save_entry)) as Hcells.
    unfold os_sched_fields_work_cells in Hcells.
    pose proof PreH21 as Haddresses.
    unfold os_sched_global_addresses in Haddresses.
    destruct Haddresses as [Hints [Hlocks [Hhigh [Hcurrent
      [Hhigh_tcb [Htable [Hcounter Hnew]]]]]]].
    rewrite <- Hints, <- Hlocks, <- Hcurrent, <- Hhigh_tcb,
      <- Htable, <- Hcounter in Hcells.
    unfold os_sched_active_restore_input, os_sched_fields_restore_input, UCOS2_fields_inv.
    Intros.
    sep_apply_l_atomic Hcells.
    unfold task_tcb_init_stack_context.
    entailer!. }
  pose proof (Hopen heap Hrestore_owned) as Hopened.
  repeat (first [assumption | split]).
Qed.

Lemma proof_of_OS_Sched_entail_wit_2 : tmr_task_sched_source_goal.OS_Sched_entail_wit_2.
Proof.
  unfold OS_Sched_entail_wit_2; left.
  intros before mask context sg critical active local environment entry_heap save_caller save_scheduled save_entry save_local save_after_heap active_before cpu_sr PreH1 PreH2 PreH3 Hsignal_20 Hidle_entry_21 Hnonidle_entry_22 PreH4 PreH5 PreH6 Hsource_coverage_24 PreH7 PreH8 Hrequires_control1 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
  pose proof (proj1 (os_sched_selection_enabled_iff save_entry) (proj2 (proj2 PreH12)))
    as [Hints Hlocks].
  pose proof (sched_selected_priority_in_range save_entry.(TskState) save_entry.(SchedState)) as Hrange.
  pose proof (os_sched_selected_table_value sg save_entry) as Htable.
  pose proof PreH1 as Haddresses.
  unfold sched_new_global_addresses in Haddresses.
  destruct Haddresses as [Hunmap [Hgroup [Hrows Hhigh]]].
  Exists save_local save_scheduled save_entry.
  unfold sched_new_rep.
  rewrite Hgroup, Hrows, Hhigh.
  rewrite <- (os_sched_selected_eq_callee_result save_entry).
  change (os_sched_ints save_entry = 0) in Hints.
  change (os_sched_locks save_entry = 0) in Hlocks.
  change (0 <= os_sched_selected save_entry < 64) in Hrange.
  entailer!.
  all: try lia; try tauto.
  rewrite <- Hhigh, <- Hgroup, <- Hrows; exact PreH6.
Qed.

Lemma proof_of_OS_Sched_entail_wit_3 : tmr_task_sched_source_goal.OS_Sched_entail_wit_3.
Proof.
  unfold OS_Sched_entail_wit_3; left.
  intros before mask context sg critical active environment scheduled_2 entry_2 entry_local_2 cpu_sr PreH1 Hsignal_13 Hidle_entry_14 Hnonidle_entry_15 PreH2 Hsource_coverage_15 PreH3 PreH4 Hrequires_control1 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20.
  pose proof (proj2 (proj2 PreH8)) as Henabled.
  assert (Hrequest : os_sched_requests_switch entry_2 = true).
  { unfold os_sched_requests_switch; rewrite Henabled.
    apply sched_switch_byte_guard_iff; exact PreH1. }
  pose proof PreH13 as Hcut.
  destruct Hcut as [Hnonempty Hbinding].
  destruct (Hbinding Hrequest) as [Hstorage Hparked].
  pose proof (os_sched_selected_work_cells_masked (task_sw_hook_call_environment environment)
    critical entry_local_2 active sg scheduled_2 cpu_sr entry_2 entry_2
    PreH12 Henabled (Hnonempty Henabled) PreH14 PreH5) as Hmasked.
  rewrite Hrequest in Hmasked.
  pose proof PreH2 as Haddresses.
  unfold os_sched_global_addresses, sched_new_global_addresses in Haddresses.
  destruct Haddresses as [Hints [Hlocks [Hhigh [Hcurrent [Hpointer [Htable [Hcounter
    [Hunmap [Hgroup [Hrows Hhigh']]]]]]]]]].
  unfold os_sched_fields_work_cells, sched_new_rep in Hmasked.
  rewrite <- Hints, <- Hlocks, <- Hhigh, <- Hcurrent, <- Hpointer, <- Htable,
    <- Hcounter, <- Hgroup, <- Hrows in Hmasked.
  rewrite <- PreH19 in Hmasked.
  assert (Hcounter_value : unsigned_last_nbits (os_sched_counter entry_2 + 1) 32 =
    (os_sched_counter entry_2 + 1) mod 4294967296) by reflexivity.
  rewrite <- Hcounter_value in Hmasked.
  Exists entry_local_2 scheduled_2 entry_2.
  unfold SchedulerCalleePhaseComponent.os_sched_task_switch_pre, os_sched_active_switch_pre, os_sched_fields_switch_pre.
  entailer!.
  sep_apply_r_atomic Hmasked; entailer!.
Qed.

Lemma proof_of_OS_Sched_entail_wit_4_1 : tmr_task_sched_source_goal.OS_Sched_entail_wit_4_1.
Proof.
  unfold OS_Sched_entail_wit_4_1; left.
  intros before mask context sg critical active environment cpu_sr scheduled entry entry_local switch_heap Hsignal_13 Hidle_entry_14 Hnonidle_entry_15 Hsignal_14 Hidle_entry_17 Hnonidle_entry_18 PreH1 Hsource_coverage_16 PreH2 PreH3 Hrequires_control1 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 heap Howned.
  destruct Howned as [Hpre [returned [current [next_local [[[Hbody Hlife]
    [Hidle_current Hnonidle_current]] Howner]]]]].
  destruct (tmr_task_sched_same_body_restore_input (task_sw_hook_call_environment environment)
    critical next_local active sg returned cpu_sr entry current
    (proj1 (proj2 Hbody)) heap Howner) as [Hvalid Hrestore].
  exists next_local, scheduled, entry, returned, current.
  pose proof (proj1 PreH7) as Hsource.
  pose proof (proj1 Hbody) as Hbody_source.
  pose proof (proj1 (proj2 (proj2 (proj2 Hbody)))) as [Hrunning_eq Hintr_eq].
  pose proof (proj1 (os_sched_selection_enabled_iff entry) (proj2 (proj2 PreH7)))
    as [Hints_entry Hlocks_entry].
  assert (Hrunning : current.(SchedState).(isRunning) = true).
  { rewrite Hrunning_eq; exact PreH6. }
  assert (Hints_current : os_sched_ints current = 0).
  { unfold os_sched_ints; rewrite Hintr_eq; exact Hints_entry. }
  assert (Hlocks_current : os_sched_locks current = 0).
  { unfold os_sched_locks; rewrite Hintr_eq; exact Hlocks_entry. }
  repeat (first [assumption | split]).
Qed.

Lemma proof_of_OS_Sched_entail_wit_4_2 : tmr_task_sched_source_goal.OS_Sched_entail_wit_4_2.
Proof.
  unfold OS_Sched_entail_wit_4_2; left.
  intros before mask context sg critical active environment scheduled entry entry_local cpu_sr PreH1 Hsignal_13 Hidle_entry_14 Hnonidle_entry_15 PreH2 Hsource_coverage_15 PreH3 PreH4 Hrequires_control1 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20.
  pose proof (proj2 (proj2 PreH8)) as Henabled.
  assert (Hrequest : os_sched_requests_switch entry = false).
  { unfold os_sched_requests_switch; rewrite Henabled.
    unfold sched_switch_byte_guard; change (negb (Z.eqb (os_sched_selected entry)
      (os_sched_current entry)) = false); rewrite PreH1, Z.eqb_refl; reflexivity. }
  pose proof (proj1 PreH13 Henabled) as Hnonempty.
  pose proof (SchedulerPhaseCandidate.os_sched_task_nonswitch_body_observation
    (task_sw_hook_call_environment environment) critical sg scheduled entry
    PreH12 (proj1 PreH8) (proj1 (proj2 PreH8)) Henabled Hrequest Hnonempty) as Hbody.
  pose proof (os_sched_ready_checkpoint_preserves_validity sg entry PreH12) as Hvalid_prefix.
  pose proof (os_sched_selected_work_cells_masked (task_sw_hook_call_environment environment)
    critical entry_local active sg scheduled cpu_sr entry entry
    PreH12 Henabled Hnonempty PreH14 PreH5) as Hmasked.
  rewrite Hrequest in Hmasked.
  pose proof PreH2 as Haddresses.
  unfold os_sched_global_addresses, sched_new_global_addresses in Haddresses.
  destruct Haddresses as [Hints [Hlocks [Hhigh [Hcurrent [Hpointer [Htable [Hcounter
    [Hunmap [Hgroup [Hrows Hhigh']]]]]]]]]].
  unfold os_sched_fields_work_cells, sched_new_rep in Hmasked.
  rewrite <- Hints, <- Hlocks, <- Hhigh, <- Hcurrent, <- Hpointer, <- Htable,
    <- Hcounter, <- Hgroup, <- Hrows in Hmasked.
  rewrite <- PreH19 in Hmasked.
  match type of Hmasked with ?P |-- _ =>
    match goal with |- ?L |-- _ =>
      assert (Hreorder : L |-- P) by entailer!
    end
  end.
  intros actual Hresources.
  pose proof (Hmasked actual (Hreorder actual Hresources)) as Hmasked_owned.
  pose (returned := scheduled).
  pose (current := os_sched_prefix_state entry).
  pose (next_local := entry_local).
  pose proof Hbody as Hreturned_body.
  change (SchedulerPhaseCandidate.os_sched_task_body_observation
    (task_sw_hook_call_environment environment) critical sg scheduled entry returned current) in Hreturned_body.
  destruct (tmr_task_sched_same_body_restore_input (task_sw_hook_call_environment environment)
    critical next_local active sg returned cpu_sr entry current
    (proj1 (proj2 Hreturned_body)) actual Hmasked_owned) as [Hvalid Hrestore].
  exists next_local, scheduled, entry, returned, current.
  assert (Hidle_current : task_idle_ready sg current.(TskState)) by exact Hidle_entry_14.
  assert (Hnonidle_current : flag_pend_non_idle_at sg returned current) by exact Hnonidle_entry_15.
  pose proof (proj1 PreH8) as Hsource.
  pose proof (proj1 Hreturned_body) as Hbody_source.
  assert (Hlife : tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current).
  { eapply (tmr_task_registered_body_source_preserves_signal_lifetime
      (task_sw_hook_call_environment environment) critical sg entry scheduled returned current).
    - apply tmr_task_registered_source_coverage_task_sw_hook; exact Hsource_coverage_15.
    - apply task_sw_hook_call_environment_source_binding.
    - exact (proj1 (proj1 (proj2 (proj2 (proj2 PreH12))))).
    - exact Hsignal_13.
    - exact Hbody_source. }

  pose proof (proj1 (proj2 (proj2 (proj2 Hreturned_body)))) as [Hrunning_eq Hintr_eq].
  pose proof (proj1 (os_sched_selection_enabled_iff entry) (proj2 (proj2 PreH8)))
    as [Hints_entry Hlocks_entry].
  assert (Hrunning : current.(SchedState).(isRunning) = true).
  { rewrite Hrunning_eq; exact PreH7. }
  assert (Hints_current : os_sched_ints current = 0).
  { unfold os_sched_ints; rewrite Hintr_eq; exact Hints_entry. }
  assert (Hlocks_current : os_sched_locks current = 0).
  { unfold os_sched_locks; rewrite Hintr_eq; exact Hlocks_entry. }
  repeat (first [assumption | split]).
Qed.

Lemma proof_of_OS_Sched_entail_wit_4_3 : tmr_task_sched_source_goal.OS_Sched_entail_wit_4_3.
Proof.
  unfold OS_Sched_entail_wit_4_3; left; intros.
  match goal with
  | Hentry : SchedulerCalleePhaseComponent.os_sched_task_entry_observation _ ?entry,
    Hguard : unsigned_last_nbits (os_sched_locks ?entry) 32 <> 0 |- _ =>
      pose proof (proj1 (os_sched_selection_enabled_iff entry) (proj2 (proj2 Hentry)))
        as [_ Hlocks];
      unfold os_sched_locks in Hguard; rewrite Hlocks in Hguard;
      exfalso; apply Hguard; reflexivity
  end.
Qed.

Lemma proof_of_OS_Sched_entail_wit_4_4 : tmr_task_sched_source_goal.OS_Sched_entail_wit_4_4.
Proof.
  unfold OS_Sched_entail_wit_4_4; left; intros.
  match goal with
  | Hentry : SchedulerCalleePhaseComponent.os_sched_task_entry_observation _ ?entry,
    Hguard : unsigned_last_nbits (os_sched_ints ?entry) 32 <> 0 |- _ =>
      pose proof (proj1 (os_sched_selection_enabled_iff entry) (proj2 (proj2 Hentry)))
        as [Hints _];
      unfold os_sched_ints in Hguard; rewrite Hints in Hguard;
      exfalso; apply Hguard; reflexivity
  end.
Qed.

Lemma proof_of_OS_Sched_return_wit_1 : tmr_task_sched_source_goal.OS_Sched_return_wit_1.
Proof.
  unfold OS_Sched_return_wit_1; right.
  intros before mask context sg critical active environment cpu_sr history_scheduled history_returned history_entry history_final history_local restore_heap Hsignal_15 Hidle_entry_16 Hnonidle_entry_17 Hsignal_16 Hidle_entry_19 Hnonidle_entry_20 Hsignal_17 Hidle_entry_22 Hnonidle_entry_23 Hready Hints Hlocks Hactive_entry Hsignal_22 Hidle_entry_29 Hnonidle_entry_30 Hglobals Hsource_coverage_24 Hclients Hprotocol Hrequires_control1 Hstable Hsave Hsource Hbody Hsame Hpreserved Hsaved Hcut Hbody_source Hvalid Hsave_effect Hrunning Hints' Hlocks'.
  eapply tmr_task_completed_restore_output_history_entry; eassumption.
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_4_pure : tmr_task_sched_source_goal.OS_Sched_partial_solve_wit_4_pure.
Proof.
  unfold OS_Sched_partial_solve_wit_4_pure; left.
  intros before mask context sg critical active local environment entry_heap PreH1 Hsource_coverage_11 PreH2 PreH3 PreH4 PreH5 Hsignal_16 PreH21 Hnonidle_entry_18 PreH6 PreH7 PreH8 PreH9 Hrequires_control1 PreH10 PreH11 PreH12 PreH13 Hsignal_26 Hidle_entry_29 Hnonidle_entry_30 PreH14 Hsource_coverage_28 PreH15 PreH16 Hrequires_control2 PreH17 PreH18 PreH19 PreH20 PreH22 heap Howned.
  split; [exact PreH5|].
  apply FlagPendActiveCallerControl.flag_pend_caller_counters_zero_from_counters; assumption.
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_7_pure : tmr_task_sched_source_goal.OS_Sched_partial_solve_wit_7_pure.
Proof.
  unfold OS_Sched_partial_solve_wit_7_pure; left.
  intros before mask context sg critical active local environment entry_heap save_caller save_scheduled save_entry save_local save_after_heap active_before cpu_sr PreH1 PreH2 Hsignal_19 Hidle_entry_20 Hnonidle_entry_21 PreH3 PreH4 PreH5 Hsource_coverage_23 PreH6 PreH7 Hrequires_control1 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 heap Howned.
  unfold os_sched_global_addresses in *; unfold coq_prop; tauto.
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_10_pure : tmr_task_sched_source_goal.OS_Sched_partial_solve_wit_10_pure.
Proof.
  unfold OS_Sched_partial_solve_wit_10_pure; left.
  intros before mask context sg critical active environment cpu_sr scheduled entry entry_local switch_heap Hsignal_13 Hidle_entry_14 Hnonidle_entry_15 Hsignal_14 Hidle_entry_17 Hnonidle_entry_18 Hglobals Hsource_coverage_16 Hclients Hprotocol Hrequires_control1 Hstable Hsave Hrunning Hentry Hsame Hsource Hsaved Hcut Heffect heap Howned.
  pose proof (proj1 (os_sched_selection_enabled_iff entry) (proj2 (proj2 Hentry)))
    as [Hints Hlocks].
  unfold coq_prop; repeat (first [assumption | split]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_14_pure : tmr_task_sched_source_goal.OS_Sched_partial_solve_wit_14_pure.
Proof.
  unfold OS_Sched_partial_solve_wit_14_pure; left.
  intros before mask context sg critical active environment cpu_sr history_scheduled history_returned history_entry history_final history_local restore_heap Hsignal_15 Hidle_entry_16 Hnonidle_entry_17 Hsignal_16 Hidle_entry_19 Hnonidle_entry_20 PreH1 PreH2 PreH3 PreH4 Hsignal_21 Hidle_entry_26 Hnonidle_entry_27 PreH5 Hsource_coverage_23 PreH6 PreH7 Hrequires_control1 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 heap Howned.
  split; [split; [exact PreH4|reflexivity]|].
  apply FlagPendActiveCallerControl.flag_pend_caller_counters_zero_from_counters; assumption.
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_1 : tmr_task_sched_source_goal.OS_Sched_which_implies_wit_1.
Proof.
  unfold OS_Sched_which_implies_wit_1; left.
  intros before mask context sg critical active local environment Hsignal_9 Hidle_entry_10 Hnonidle_entry_11 Hsource_coverage_10 Hclients Hprotocol Hrequires_control1 Hstable Hrunning heap Howned.
  destruct (SchedulerCalleePhaseComponent.os_sched_task_call_pre_open (task_sw_hook_call_environment environment)
    critical local active sg context mask before Hclients heap Howned)
    as [[Hentry Hstable'] Hsave].
  pose proof (proj1 Hentry) as Hsource.
  pose proof (proj1 (os_sched_selection_enabled_iff before) (proj2 (proj2 Hentry)))
    as [Hints Hlocks].
  pose proof (FlagPendEntryControl.flag_pend_running_protocol_entry
    sg active before Hprotocol Hrunning) as Hactive_entry.
  repeat (first [assumption | split]).
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_2 : tmr_task_sched_source_goal.OS_Sched_which_implies_wit_2.
Proof.
  unfold OS_Sched_which_implies_wit_2; left.
  intros before mask context sg critical active local environment Hregistry_coverage_9 Hints Hlocks Hentry heap Howned.
  destruct (SchedulerPairedPhaseComponent.os_sched_active_save_input_implies_caller_input
    (task_sw_hook_call_environment environment) critical local active sg context mask before
    heap Howned) as [[Hcut Hclients] Hpaired].
  repeat (first [assumption | split]).

Qed.

Lemma proof_of_OS_Sched_which_implies_wit_3 : tmr_task_sched_source_goal.OS_Sched_which_implies_wit_3.
Proof.
  unfold OS_Sched_which_implies_wit_3; left.
  intros before mask context sg critical active local environment Hints Hlocks Hentry.
  apply os_sched_active_heap_capture.
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_4 : tmr_task_sched_source_goal.OS_Sched_which_implies_wit_4.
Proof.
  unfold OS_Sched_which_implies_wit_4; left.
  intros before mask context sg critical active local environment entry_heap cpu_sr Hsignal_11 Hidle_entry_12 Hnonidle_entry_13 Hsource_added_12 Hnonempty Hints Hlocks Hrunning heap Howned.
  pose proof (tmr_task_active_save_output_signal
    (task_sw_hook_call_environment environment) critical local active sg
    context mask before entry_heap cpu_sr
    Hnonempty Hsource_added_12 Hsignal_11 heap Howned) as Hstrong.
  destruct Hstrong as [returned_caller [returned [acquired [next_local [Hevent Hlife]]]]].
  pose proof Hevent as [_ [_ [_ [Hafter _]]]].
  destruct (tmr_task_completed_save_event_idle_non_idle
    (task_sw_hook_call_environment environment) critical local active sg context mask cpu_sr before
    returned_caller returned acquired next_local entry_heap heap Hevent Hsource_added_12
    Hidle_entry_12 Hnonidle_entry_13) as [Hidle_return Hnonidle_return].
  exists returned_caller, next_local, heap, returned, acquired.
  repeat (first [assumption | reflexivity | split]).
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_5 : tmr_task_sched_source_goal.OS_Sched_which_implies_wit_5.
Proof.
  unfold OS_Sched_which_implies_wit_5; left.
  intros before mask context sg critical active local environment entry_heap save_caller save_scheduled save_entry save_local save_after_heap cpu_sr Hsignal_16 Hidle_entry_17 Hnonidle_entry_18 Hlayout Hsource Havailable Hidle Hcut Hsource_coverage_22 Hclients Hevent heap [Heq Hpost].
  subst heap.
  destruct (SchedulerPairedPhaseComponent.os_sched_caller_save_event_active_event
    (task_sw_hook_call_environment environment) critical local active sg context mask cpu_sr before
    save_caller save_scheduled save_entry save_local entry_heap save_after_heap
    Hlayout Hsource Havailable Hidle Hcut Hclients Hevent)
    as [active_before [Hsplit [Hnormal [Hcontrol [Hreturned [Hcut' Howned]]]]]].
  exists active_before; repeat (first [assumption | split]).
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_6 : tmr_task_sched_source_goal.OS_Sched_which_implies_wit_6.
Proof.
  unfold OS_Sched_which_implies_wit_6; left.
  intros sg critical active environment scheduled entry entry_local cpu_sr Hsignal_9 Hidle_entry_10 Hnonidle_entry_11.
  intros heap Howned; exists heap; repeat (first [assumption | reflexivity | split]).
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_7 : tmr_task_sched_source_goal.OS_Sched_which_implies_wit_7.
Proof.
  unfold OS_Sched_which_implies_wit_7; left.
  intros sg critical active environment scheduled entry entry_local switch_heap cpu_sr Hsource_coverage_10 Hsignal_11 Hidle_entry_12 Hnonidle_entry_13.
  exact (tmr_task_sched_switch_source_post_entry environment critical entry_local active
    sg scheduled cpu_sr entry entry switch_heap Hsource_coverage_10 Hsignal_11).
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_8 : tmr_task_sched_source_goal.OS_Sched_which_implies_wit_8.
Proof.
  unfold OS_Sched_which_implies_wit_8; left.
  intros sg critical active environment history_returned history_entry history_final history_local cpu_sr Hsignal_10 Hidle_entry_11 Hnonidle_entry_12 Hprotocol Hrequires_control1 Hrunning Hints Hlocks heap Howned.
  destruct (SchedulerRestorePhaseComponent.os_sched_task_restore_input_implies_caller_input
    (task_sw_hook_call_environment environment) critical history_local active sg history_returned
    cpu_sr history_entry history_final heap Howned) as [Hready Hcaller].
  pose proof (FlagPendEntryControl.flag_pend_running_protocol_entry
    sg active history_final Hprotocol Hrunning) as Hentry.
  repeat (first [assumption | split]).
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_9 : tmr_task_sched_source_goal.OS_Sched_which_implies_wit_9.
Proof.
  unfold OS_Sched_which_implies_wit_9; left.
  intros sg critical active environment history_returned history_entry history_final history_local cpu_sr Hsignal_10 Hidle_entry_11 Hnonidle_entry_12 Hints Hlocks Hentry.
  intros heap Howned; exists heap; repeat (first [assumption | reflexivity | split]).
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_10 : tmr_task_sched_source_goal.OS_Sched_which_implies_wit_10.
Proof.
  unfold OS_Sched_which_implies_wit_10; left.
  intros sg critical active environment history_returned history_entry history_final history_local restore_heap cpu_sr Hsignal_11 Hidle_entry_12 Hnonidle_entry_13 Hnonempty.
  intros heap Howned.
  pose proof (FlagPendActiveCaller.flag_pend_restore_output_nonempty
    (task_sw_hook_call_environment environment) critical history_local active sg
    (FlagPendTaskCaller history_returned) history_returned cpu_sr history_entry history_final
    restore_heap Hnonempty heap Howned) as Houtput.
  repeat (first [assumption | split]).
Qed.
