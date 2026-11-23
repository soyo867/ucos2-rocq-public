From SimpleC.Verification Require Import VCPrelude.
From Ucos2Verify.VC.code.sched Require Import sem_client_sched_goal.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sem_client_sched_case_lib.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_sched_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Import UCOS2_C_Rules TaskStateDef SchedulerPhaseCandidate.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma proof_of_OS_Sched_entail_wit_1 : OS_Sched_entail_wit_1.
Proof.
  left; intros.
  unfold sem_pend_client_sched_save_output; Intros scheduled acquired next_local.
  assert (Hsource : sem_pend_client_return_source environment critical sg context before scheduled acquired) by tauto.
  assert (Hentry : sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout
    waiting scheduled acquired) by tauto.
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hsource) as Hsame.
  pose proof (proj1 (proj1 Hentry)) as Hvalid.
  pose proof (sem_client_sched_entry_cut _ _ _ _ _ _ _ _ _ _ _ _ PreH2 Hentry) as Hcut.
  assert (Hpreserved : task_tcb_init_stack_source_preserved context before acquired).
  { intro Hbefore. apply (proj1 (task_tcb_init_stack_same_call_source_iff scheduled context acquired Hsame)).
    exact (proj1 (proj2 (proj1 Hentry))). }
  unfold sem_pend_fields_masked.
  rewrite <- (os_sched_fields_restore_input_masked_world environment critical next_local sg scheduled retval acquired acquired).
  unfold os_sched_fields_restore_input, UCOS2_fields_inv; Intros.
  Exists next_local scheduled acquired.
  pose proof (proj1 (os_sched_fields_work_cells_entry_equiv sg acquired)) as Hcells.
  unfold os_sched_fields_work_cells in Hcells.
  pose proof PreH1 as Haddresses.
  destruct Haddresses as [Hints [Hlocks [Hhigh [Hcurrent [Hpointer [Htable [Hcounter Hnew]]]]]]].
  rewrite <- Hints, <- Hlocks, <- Hcurrent, <- Hpointer, <- Htable, <- Hcounter in Hcells.
  sep_apply_l_atomic Hcells.
  unfold task_tcb_init_stack_context; entailer!.
Qed.

Lemma proof_of_OS_Sched_entail_wit_2 : OS_Sched_entail_wit_2.
Proof.
  left; intros.
  pose proof (proj1 (os_sched_selection_enabled_iff entry_2) (proj1 (proj2 (proj2 PreH8))))
    as [Hints Hlocks].
  pose proof (sched_selected_priority_in_range entry_2.(TskState) entry_2.(SchedState)) as Hrange.
  pose proof (os_sched_selected_table_value sg entry_2) as Htable.
  pose proof PreH1 as Haddresses.
  destruct Haddresses as [Hunmap [Hgroup [Hrows Hhigh]]].
  Exists entry_local_2 scheduled_2 entry_2.
  unfold sched_new_rep.
  rewrite Hgroup, Hrows, Hhigh.
  rewrite <- (os_sched_selected_eq_callee_result entry_2).
  change (os_sched_ints entry_2 = 0) in Hints.
  change (os_sched_locks entry_2 = 0) in Hlocks.
  change (0 <= os_sched_selected entry_2 < 64) in Hrange.
  entailer!; try lia; try tauto.
  rewrite <- Hhigh, <- Hgroup, <- Hrows; exact PreH4.
Qed.

Lemma proof_of_OS_Sched_entail_wit_3 : OS_Sched_entail_wit_3.
Proof.
  left; intros.
  pose proof (proj1 (proj2 (proj2 PreH6))) as Henabled.
  assert (Hrequest : os_sched_requests_switch entry_2 = true).
  { unfold os_sched_requests_switch; rewrite Henabled.
    apply sched_switch_byte_guard_iff; exact PreH1. }
  destruct (proj2 PreH11 Hrequest) as [Hstorage Hparked].
  pose proof (sem_client_sched_selected_cells_masked environment critical entry_local_2 sg scheduled_2 cpu_sr entry_2
    PreH10 Henabled (proj1 PreH11 Henabled) PreH12) as Hmasked.
  rewrite Hrequest in Hmasked.
  pose proof PreH2 as Haddresses.
  unfold os_sched_global_addresses, sched_new_global_addresses in Haddresses.
  destruct Haddresses as [Hints [Hlocks [Hhigh [Hcurrent [Hpointer [Htable [Hcounter
    [Hunmap [Hgroup [Hrows Hhigh']]]]]]]]]].
  unfold os_sched_fields_work_cells, sched_new_rep in Hmasked.
  rewrite <- Hints, <- Hlocks, <- Hhigh, <- Hcurrent, <- Hpointer, <- Htable,
    <- Hcounter, <- Hgroup, <- Hrows in Hmasked.
  rewrite <- PreH17 in Hmasked.
  assert (Hcounter_value : unsigned_last_nbits (os_sched_counter entry_2 + 1) 32 =
    (os_sched_counter entry_2 + 1) mod 4294967296) by reflexivity.
  rewrite <- Hcounter_value in Hmasked.
  match type of Hmasked with ?P |-- _ =>
    match goal with |- ?L |-- _ =>
      assert (Hreorder : L |-- P) by
        (entailer!; solve [
         intros owned_heap [priority_heap [ready_heap [Hjoin [Hpriority Hready]]]];
         exists ready_heap, priority_heap;
         split; [apply UCOS2_C_Rules.join_comm; exact Hjoin | split; assumption]])
    end
  end.
  intros heap Howned.
  pose proof (Hmasked heap (Hreorder heap Howned)) as Hreturned.
  exists entry_local_2, scheduled_2, entry_2.
  unfold sem_client_sched_switch_input, os_sched_fields_switch_pre.
  repeat (first [assumption | split]).
Qed.

Lemma proof_of_OS_Sched_entail_wit_4_1 : OS_Sched_entail_wit_4_1.
Proof.
  left; intros.
  intros heap [returned [current [next_local [[Hbody [Hcontext [Hselected [Henabled Hfields]]]] Hmasked]]]].
  exists next_local, returned, current, scheduled_2, entry_2.
  unfold sem_pend_client_sched_restore_input.
  repeat (first [assumption | split]).
Qed.

Lemma proof_of_OS_Sched_entail_wit_4_2 : OS_Sched_entail_wit_4_2.
Proof.
  left; intros.
  pose proof (proj1 (proj2 (proj2 PreH6))) as Henabled.
  assert (Hrequest : os_sched_requests_switch entry_2 = false).
  { unfold os_sched_requests_switch; rewrite Henabled.
    unfold sched_switch_byte_guard.
    change (negb (Z.eqb (os_sched_selected entry_2) (os_sched_current entry_2)) = false).
    rewrite PreH1, Z.eqb_refl; reflexivity. }
  destruct (sem_client_sched_nonswitch_observation environment critical sg original mask initial observed eid timeout
    waiting scheduled_2 entry_2 PreH6 Hrequest) as [Hbody [Hcontext [Hselected Hfields]]].
  pose proof (sem_client_sched_selected_cells_masked environment critical entry_local sg scheduled_2 cpu_sr entry_2
    PreH10 Henabled (proj1 PreH11 Henabled) PreH12) as Hmasked.
  rewrite Hrequest in Hmasked.
  pose proof PreH2 as Haddresses.
  unfold os_sched_global_addresses, sched_new_global_addresses in Haddresses.
  destruct Haddresses as [Hints [Hlocks [Hhigh [Hcurrent [Hpointer [Htable [Hcounter
    [Hunmap [Hgroup [Hrows Hhigh']]]]]]]]]].
  unfold os_sched_fields_work_cells, sched_new_rep in Hmasked.
  rewrite <- Hints, <- Hlocks, <- Hhigh, <- Hcurrent, <- Hpointer, <- Htable,
    <- Hcounter, <- Hgroup, <- Hrows in Hmasked.
  rewrite <- PreH17 in Hmasked.
  match type of Hmasked with ?P |-- _ =>
    match goal with |- ?L |-- _ =>
      assert (Hreorder : L |-- P) by (entailer!; solve [
         intros owned_heap [priority_heap [ready_heap [Hjoin [Hpriority Hready]]]];
         exists ready_heap, priority_heap;
         split; [apply UCOS2_C_Rules.join_comm; exact Hjoin | split; assumption]])
    end
  end.
  intros heap Howned.
  pose proof (Hmasked heap (Hreorder heap Howned)) as Hreturned.
  exists entry_local, scheduled_2, (os_sched_prefix_state entry_2), scheduled_2, entry_2.
  unfold sem_pend_client_sched_restore_input.
  repeat (first [assumption | split]).
Qed.

Lemma proof_of_OS_Sched_entail_wit_4_3 : OS_Sched_entail_wit_4_3.
Proof.
  left; intros.
  match goal with
  | Hentry : sem_pend_client_sched_entry _ _ _ _ _ _ _ _ _ _ _ ?entry,
    Hguard : unsigned_last_nbits (os_sched_locks ?entry) 32 <> 0 |- _ =>
      pose proof (proj1 (os_sched_selection_enabled_iff entry) (proj1 (proj2 (proj2 Hentry)))) as [_ Hlocks];
      unfold os_sched_locks in Hguard; rewrite Hlocks in Hguard;
      exfalso; apply Hguard; reflexivity
  end.
Qed.

Lemma proof_of_OS_Sched_entail_wit_4_4 : OS_Sched_entail_wit_4_4.
Proof.
  left; intros.
  match goal with
  | Hentry : sem_pend_client_sched_entry _ _ _ _ _ _ _ _ _ _ _ ?entry,
    Hguard : unsigned_last_nbits (os_sched_ints ?entry) 32 <> 0 |- _ =>
      pose proof (proj1 (os_sched_selection_enabled_iff entry) (proj1 (proj2 (proj2 Hentry)))) as [Hints _];
      unfold os_sched_ints in Hguard; rewrite Hints in Hguard;
      exfalso; apply Hguard; reflexivity
  end.
Qed.

Lemma proof_of_OS_Sched_return_wit_1 : OS_Sched_return_wit_1.
Proof.
  right; intros.
  eapply sem_pend_sched_restore_output_compose; eassumption.
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_2_pure : OS_Sched_partial_solve_wit_2_pure.
Proof.
  left; intros.
  assert (Haddresses : sched_new_global_addresses sg
    (&("OSUnMapTbl")) (&("OSRdyGrp")) (&("OSRdyTbl")) (&("OSPrioHighRdy"))).
  { unfold os_sched_global_addresses in PreH3; tauto. }
  entailer!.
Qed.
