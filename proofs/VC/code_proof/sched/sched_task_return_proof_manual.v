(** Prepared current canonical manual partition; 48-target migration; fresh check pending. *)
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
From Ucos2Verify.VC.code.sched Require Import sched_task_return_goal.
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

Require Import Ucos2Verify.VC.code.sched.sched_task_return_proof_auto.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_proof_helpers.

Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_entry_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_local_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_counter_entry_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_caller_control_spec.

Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_caller_control_spec.

Lemma proof_of_OS_Sched_entail_wit_1 : sched_task_return_goal.OS_Sched_entail_wit_1.
Proof.
  unfold OS_Sched_entail_wit_1; left.
  intros before mask context sg critical active local environment entry_heap retval save_caller save_scheduled
    save_entry save_local save_after_heap active_before PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 Hrequires_control1 PreH17 PreH18 PreH19 PreH20 PreH21
    PreH22 PreH23 Hrequires_control2 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 heap [active_after
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

Lemma proof_of_OS_Sched_entail_wit_2 : sched_task_return_goal.OS_Sched_entail_wit_2.
Proof.
  unfold OS_Sched_entail_wit_2; left.
  intros before mask context sg critical active local environment entry_heap save_caller save_scheduled save_entry
    save_local save_after_heap active_before cpu_sr PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
    Hrequires_control1 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19.
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

Lemma proof_of_OS_Sched_entail_wit_3 : sched_task_return_goal.OS_Sched_entail_wit_3.
Proof.
  unfold OS_Sched_entail_wit_3; left.
  intros before mask context sg critical active environment scheduled_2 entry_2 entry_local_2 cpu_sr PreH1 PreH2
    PreH3 PreH4 Hrequires_control1 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
    PreH16 PreH17 PreH18 PreH19 PreH20.
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

Lemma proof_of_OS_Sched_entail_wit_4_1 : sched_task_return_goal.OS_Sched_entail_wit_4_1.
Proof.
  unfold OS_Sched_entail_wit_4_1; left.
  intros before mask context sg critical active environment cpu_sr scheduled entry entry_local switch_heap PreH1
    PreH2 PreH3 Hrequires_control1 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 heap Howned.
  pose proof (SchedulerCalleePhaseComponent.os_sched_task_switch_output_open (task_sw_hook_call_environment environment)
    critical entry_local active sg scheduled cpu_sr entry entry switch_heap heap Howned) as Hbody_post.
  destruct (SchedulerCalleePhaseComponent.os_sched_task_body_restore_input (task_sw_hook_call_environment environment)
    critical active sg scheduled cpu_sr entry entry heap Hbody_post)
    as [returned [current [next_local [[Hbody Hvalid] Hrestore]]]].
  exists next_local, returned, current, scheduled, entry.
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

Lemma proof_of_OS_Sched_entail_wit_4_2 : sched_task_return_goal.OS_Sched_entail_wit_4_2.
Proof.
  unfold OS_Sched_entail_wit_4_2; left.
  intros before mask context sg critical active environment scheduled entry entry_local cpu_sr PreH1 PreH2 PreH3
    PreH4 Hrequires_control1 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
    PreH17 PreH18 PreH19 PreH20.
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
  assert (Hpost : SchedulerCalleePhaseComponent.os_sched_task_body_post (task_sw_hook_call_environment environment)
    critical active sg scheduled cpu_sr entry entry actual).
  { exists scheduled, (os_sched_prefix_state entry), entry_local.
    exact (conj Hbody Hmasked_owned). }
  destruct (SchedulerCalleePhaseComponent.os_sched_task_body_restore_input (task_sw_hook_call_environment environment)
    critical active sg scheduled cpu_sr entry entry actual Hpost)
    as [returned [current [next_local [[Hreturned_body Hvalid] Hrestore]]]].
  exists next_local, returned, current, scheduled, entry.
  pose proof (proj1 PreH8) as Hsource.
  pose proof (proj1 Hreturned_body) as Hbody_source.

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

Lemma proof_of_OS_Sched_entail_wit_4_3 : sched_task_return_goal.OS_Sched_entail_wit_4_3.
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

Lemma proof_of_OS_Sched_entail_wit_4_4 : sched_task_return_goal.OS_Sched_entail_wit_4_4.
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

Lemma proof_of_OS_Sched_return_wit_1 : sched_task_return_goal.OS_Sched_return_wit_1.
Proof.
  unfold OS_Sched_return_wit_1; right.
  intros before mask context sg critical active environment cpu_sr history_scheduled history_returned
    history_entry history_final history_local restore_heap Hready Hints Hlocks Hactive_entry Hglobals
    Hclients Hprotocol Hrequires_control1 Hstable Hsave Hsource Hbody Hsame Hpreserved Hsaved Hcut
    Hbody_source Hvalid Hsave_effect Hrunning Hints' Hlocks'.
  eapply SchedulerRestorePhaseComponent.os_sched_task_caller_restore_output_implies_history_return_post; eassumption.
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_4_pure : sched_task_return_goal.OS_Sched_partial_solve_wit_4_pure.
Proof.
  unfold OS_Sched_partial_solve_wit_4_pure; left.
  intros before mask context sg critical active local environment entry_heap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
    PreH7 PreH8 PreH9 Hrequires_control1 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 Hrequires_control2
    PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 heap Howned.
  split; [exact PreH5|].
  apply FlagPendActiveCallerControl.flag_pend_caller_counters_zero_from_counters; assumption.
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_7_pure : sched_task_return_goal.OS_Sched_partial_solve_wit_7_pure.
Proof.
  unfold OS_Sched_partial_solve_wit_7_pure; left.
  intros before mask context sg critical active local environment entry_heap save_caller save_scheduled save_entry
    save_local save_after_heap active_before cpu_sr PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
    Hrequires_control1 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 heap Howned.
  unfold os_sched_global_addresses in *; unfold coq_prop; tauto.
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_10_pure : sched_task_return_goal.OS_Sched_partial_solve_wit_10_pure.
Proof.
  unfold OS_Sched_partial_solve_wit_10_pure; left.
  intros before mask context sg critical active environment cpu_sr scheduled entry entry_local switch_heap
    Hglobals Hclients Hprotocol Hrequires_control1 Hstable Hsave Hrunning Hentry Hsame Hsource Hsaved Hcut
    Heffect heap Howned.
  pose proof (proj1 (os_sched_selection_enabled_iff entry) (proj2 (proj2 Hentry)))
    as [Hints Hlocks].
  unfold coq_prop; repeat (first [assumption | split]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_14_pure : sched_task_return_goal.OS_Sched_partial_solve_wit_14_pure.
Proof.
  unfold OS_Sched_partial_solve_wit_14_pure; left.
  intros before mask context sg critical active environment cpu_sr history_scheduled history_returned
    history_entry history_final history_local restore_heap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
    Hrequires_control1 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    PreH20 PreH21 heap Howned.
  split; [split; [exact PreH4|reflexivity]|].
  apply FlagPendActiveCallerControl.flag_pend_caller_counters_zero_from_counters; assumption.
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_1 : sched_task_return_goal.OS_Sched_which_implies_wit_1.
Proof.
  unfold OS_Sched_which_implies_wit_1; left.
  intros before mask context sg critical active local environment Hclients Hprotocol Hrequires_control1 Hstable
    Hrunning heap Howned.
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

Lemma proof_of_OS_Sched_which_implies_wit_2 : sched_task_return_goal.OS_Sched_which_implies_wit_2.
Proof.
  unfold OS_Sched_which_implies_wit_2; left.
  intros before mask context sg critical active local environment Hints Hlocks Hentry heap Howned.
  destruct (SchedulerPairedPhaseComponent.os_sched_active_save_input_implies_caller_input
    (task_sw_hook_call_environment environment) critical local active sg context mask before
    heap Howned) as [[Hcut Hclients] Hpaired].
  repeat (first [assumption | split]).
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_3 : sched_task_return_goal.OS_Sched_which_implies_wit_3.
Proof.
  unfold OS_Sched_which_implies_wit_3; left.
  intros before mask context sg critical active local environment Hints Hlocks Hentry.
  apply os_sched_active_heap_capture.
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_4 : sched_task_return_goal.OS_Sched_which_implies_wit_4.
Proof.
  unfold OS_Sched_which_implies_wit_4; left.
  intros before mask context sg critical active local environment entry_heap cpu_sr
    Hnonempty Hints Hlocks Hrunning heap Howned.
  pose proof (FlagPendActiveCaller.flag_pend_save_output_nonempty
    (task_sw_hook_call_environment environment) critical local active sg
    (FlagPendTaskCaller context) context mask before entry_heap cpu_sr
    Hnonempty heap Howned) as Hstrong.
  destruct Hstrong as [returned_caller [returned [acquired [next_local Hevent]]]].
  pose proof Hevent as [_ [_ [_ [Hafter _]]]].
  exists returned_caller, returned, acquired, next_local, heap.
  split; [exact Hevent|]. split; [reflexivity|exact Hafter].
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_5 : sched_task_return_goal.OS_Sched_which_implies_wit_5.
Proof.
  unfold OS_Sched_which_implies_wit_5; left.
  intros before mask context sg critical active local environment entry_heap
    save_caller save_scheduled save_entry save_local save_after_heap cpu_sr
    Hlayout Hsource Havailable Hidle Hcut Hclients Hevent heap [Heq Hpost].
  subst heap.
  destruct (SchedulerPairedPhaseComponent.os_sched_caller_save_event_active_event
    (task_sw_hook_call_environment environment) critical local active sg context mask cpu_sr before
    save_caller save_scheduled save_entry save_local entry_heap save_after_heap
    Hlayout Hsource Havailable Hidle Hcut Hclients Hevent)
    as [active_before [Hsplit [Hnormal [Hcontrol [Hreturned [Hcut' Howned]]]]]].
  exists active_before; repeat (first [assumption | split]).
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_6 : sched_task_return_goal.OS_Sched_which_implies_wit_6.
Proof.
  unfold OS_Sched_which_implies_wit_6; left.
  intros sg critical active environment scheduled entry entry_local cpu_sr.
  apply os_sched_active_heap_capture.
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_7 : sched_task_return_goal.OS_Sched_which_implies_wit_7.
Proof.
  unfold OS_Sched_which_implies_wit_7; left.
  intros sg critical active environment scheduled entry entry_local switch_heap cpu_sr.
  exact (SchedulerCalleePhaseComponent.os_sched_task_switch_source_output_observation environment critical entry_local active
    sg scheduled cpu_sr entry entry switch_heap).
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_8 : sched_task_return_goal.OS_Sched_which_implies_wit_8.
Proof.
  unfold OS_Sched_which_implies_wit_8; left.
  intros sg critical active environment history_returned history_entry history_final history_local cpu_sr
    Hprotocol Hrequires_control1 Hrunning Hints Hlocks heap Howned.
  destruct (SchedulerRestorePhaseComponent.os_sched_task_restore_input_implies_caller_input
    (task_sw_hook_call_environment environment) critical history_local active sg history_returned
    cpu_sr history_entry history_final heap Howned) as [Hready Hcaller].
  pose proof (FlagPendEntryControl.flag_pend_running_protocol_entry
    sg active history_final Hprotocol Hrunning) as Hentry.
  repeat (first [assumption | split]).
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_9 : sched_task_return_goal.OS_Sched_which_implies_wit_9.
Proof.
  unfold OS_Sched_which_implies_wit_9; left.
  intros sg critical active environment history_returned history_entry history_final history_local cpu_sr Hints Hlocks Hentry.
  apply os_sched_active_heap_capture.
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_10 : sched_task_return_goal.OS_Sched_which_implies_wit_10.
Proof.
  unfold OS_Sched_which_implies_wit_10; left.
  intros sg critical active environment history_returned history_entry history_final
    history_local restore_heap cpu_sr Hnonempty.
  apply FlagPendActiveCaller.flag_pend_restore_output_nonempty.
  exact Hnonempty.
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_11 : sched_task_return_goal.OS_Sched_which_implies_wit_11.
Proof.
  unfold OS_Sched_which_implies_wit_11; left.
  intros sg critical active environment history_returned history_entry history_final
    history_local restore_heap cpu_sr Hnonempty.
  apply FlagPendActiveCaller.flag_pend_restore_output_nonempty.
  exact Hnonempty.
Qed.
