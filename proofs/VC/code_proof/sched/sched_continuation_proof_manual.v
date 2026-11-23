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
From Ucos2Verify.VC.code.sched Require Import sched_continuation_goal.
From Ucos2Verify.VC.code.sched Require Import sched_continuation_proof_auto.
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
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OS_Sched_entail_wit_1 : OS_Sched_entail_wit_1.
Proof.
  left; intros.
  unfold os_sched_continuation_call_save_history_output; Intros scheduled acquired.
  unfold task_tcb_init_continuation_restore_input, UCOS2_inv; Intros.
  Exists acquired scheduled.
  pose proof PreH2 as Haddresses.
  destruct PreH2 as [Hints [Hlocks [Hhigh [Hcur [Hptr [Htable [Hctr Hnew]]]]]]].
  rewrite Hints, Hlocks, Hcur, Hptr, Htable, Hctr.
  rewrite Hints, Hlocks, Hcur, Hptr, Htable, Hctr in Haddresses.
  unfold task_tcb_init_stack_context; entailer!.
  rewrite (os_sched_work_cells_entry_equiv sg acquired).
  unfold os_sched_work_cells; entailer!.
Qed.

Lemma proof_of_OS_Sched_entail_wit_2 : OS_Sched_entail_wit_2.
Proof.
  left; intros.
  add_pure (0 <= os_sched_ints entry_2 <= 255) as Hints.
  { sep_apply_l_atomic (store_uchar_range (&("OSIntNesting")) (os_sched_ints entry_2));
      entailer!. }
  add_pure (0 <= os_sched_locks entry_2 <= 255) as Hlocks.
  { sep_apply_l_atomic (store_uchar_range (&("OSLockNesting")) (os_sched_locks entry_2));
      entailer!. }
  unfold unsigned_last_nbits in PreH2, PreH3.
  rewrite Z.mod_small in PreH2 by (change (0 <= os_sched_locks entry_2 < 4294967296); lia).
  rewrite Z.mod_small in PreH3 by (change (0 <= os_sched_ints entry_2 < 4294967296); lia).
  pose proof (sched_selected_priority_in_range entry_2.(TskState) entry_2.(SchedState)) as Hrange.
  pose proof (os_sched_selected_table_value sg entry_2) as Hlookup.
  Exists entry_2 scheduled_2.
  unfold sched_new_rep.
  rewrite <- os_sched_selected_eq_callee_result.
  destruct PreH1 as [Hunmap [Hgroup [Hrows Hhigh]]].
  rewrite Hgroup, Hrows, Hhigh.
  rewrite Hgroup, Hrows, Hhigh in PreH4.
  entailer!.
Qed.

Lemma proof_of_OS_Sched_entail_wit_3 : OS_Sched_entail_wit_3.
Proof.
  left; intros.
  assert (Hen : os_sched_selection_enabled entry_2 = true).
  { apply os_sched_selection_enabled_iff; split; assumption. }
  assert (Hswitch : os_sched_requests_switch entry_2 = true).
  { apply os_sched_requests_switch_iff; split; assumption. }
  pose proof (proj2 PreH8 Hswitch) as Hinput.
  Exists entry_2 scheduled_2; entailer!.
  unfold os_sched_continuation_switch_pre; entailer!.
  rewrite <- (task_tcb_init_continuation_restore_input_masked_world
    environment critical saved_local sg scheduled_2 cpu_sr entry_2 (os_sched_prefix_state entry_2)).
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_stack_context; entailer!.
  unfold os_sched_prefix_state.
  rewrite <- (os_sched_prefix_merge_inv sg entry_2 PreH7 (proj1 PreH8)).
  rewrite PreH14.
  unfold os_sched_global_addresses, sched_new_global_addresses in PreH2.
  destruct PreH2 as [Hints [Hlocks [Hhigh [Hcur [Hptr [Htable [Hctr
    [Hunmap [Hgroup [Hrows Hhigh']]]]]]]]]].
  rewrite Hints, Hlocks, Hhigh, Hcur, Hptr, Htable, Hctr, Hgroup, Hrows.
  unfold os_sched_prefix_rep, os_sched_prefix_physical_rep; rewrite Hen.
  unfold os_sched_counter_stage; rewrite Hswitch.
  unfold sched_cache_cells, sched_physical_without_high,
    os_sched_work_frame, os_sched_ints, os_sched_locks, os_sched_group,
    os_sched_rows, os_sched_selected, os_sched_selected_tcb,
    os_sched_current, os_sched_counter, os_sched_table,
    task_public_storage, task_public_storage_without_prio_tbl, store_prio_tbl,
    UCOS2_raw_rep_missing_task_storage_sched, UCOS2_selected_rep, unsigned_last_nbits.
  cbn [UCOS2_module_rep sched_increment_switch_counter
    SchedStateDef.curSchedPrio SchedStateDef.curTaskID
    SchedStateDef.ctxSwCtr SchedStateDef.isRunning].
  change (2 ^ 32) with 4294967296.
  rewrite sched_rows_array_equiv.
  entailer!.
  rewrite <- (interrupt_inv_merge_counters sg entry_2.(IntrState)).
  unfold store_int_state; entailer!.
Qed.

Lemma proof_of_OS_Sched_entail_wit_4_1 : OS_Sched_entail_wit_4_1.
Proof.
  left; intros.
  sep_apply_l_atomic (os_sched_continuation_body_restore_input
    environment critical saved_local sg scheduled_2 cpu_sr entry_2 entry_2).
  Intros returned final.
  Exists returned final entry_2 scheduled_2; entailer!.
Qed.

Lemma proof_of_OS_Sched_entail_wit_4_2 : OS_Sched_entail_wit_4_2.
Proof.
  left; intros.
  assert (Hen : os_sched_selection_enabled entry_2 = true).
  { apply os_sched_selection_enabled_iff; split; assumption. }
  assert (Hswitch : os_sched_requests_switch entry_2 = false).
  { unfold os_sched_requests_switch; rewrite Hen.
    unfold sched_switch_byte_guard; fold (os_sched_selected entry_2) (os_sched_current entry_2).
    rewrite PreH1, Z.eqb_refl; reflexivity. }
  assert (Hreturn : os_sched_c_return environment.(task_stack_call_external) critical sg
    entry_2 scheduled_2 scheduled_2 (os_sched_prefix_state entry_2)).
  { unfold os_sched_c_return; rewrite Hswitch; auto. }
  pose proof (os_sched_ready_checkpoint_preserves_validity sg entry_2 PreH7) as Hvalid.
  Exists scheduled_2 (os_sched_prefix_state entry_2) entry_2 scheduled_2; entailer!.
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_stack_context; entailer!.
  unfold os_sched_prefix_state.
  rewrite <- (os_sched_prefix_merge_inv sg entry_2 PreH7 (proj1 PreH8)).
  rewrite PreH14.
  unfold os_sched_global_addresses, sched_new_global_addresses in PreH2.
  destruct PreH2 as [Hints [Hlocks [Hhigh [Hcur [Hptr [Htable [Hctr
    [Hunmap [Hgroup [Hrows Hhigh']]]]]]]]]].
  rewrite Hints, Hlocks, Hhigh, Hcur, Hptr, Htable, Hctr, Hgroup, Hrows.
  unfold os_sched_prefix_rep, os_sched_prefix_physical_rep; rewrite Hen.
  unfold os_sched_counter_stage; rewrite Hswitch.
  unfold sched_cache_cells, sched_physical_without_high,
    os_sched_work_frame, os_sched_ints, os_sched_locks, os_sched_group,
    os_sched_rows, os_sched_selected, os_sched_selected_tcb,
    os_sched_current, os_sched_counter, os_sched_table,
    task_public_storage, task_public_storage_without_prio_tbl, store_prio_tbl,
    UCOS2_raw_rep_missing_task_storage_sched, UCOS2_selected_rep.
  cbn [UCOS2_module_rep].
  rewrite sched_rows_array_equiv.
  entailer!.
  rewrite <- (interrupt_inv_merge_counters sg entry_2.(IntrState)).
  unfold store_int_state; entailer!.
Qed.

Lemma proof_of_OS_Sched_entail_wit_4_3 : OS_Sched_entail_wit_4_3.
Proof.
  left; intros.
  assert (Hlock : os_sched_locks entry_2 <> 0).
  { intro Hzero; rewrite Hzero in PreH1; exact (PreH1 eq_refl). }
  assert (Hen : os_sched_selection_enabled entry_2 = false).
  { unfold os_sched_selection_enabled; fold (os_sched_locks entry_2).
    rewrite (proj2 (Z.eqb_neq _ _) Hlock), Bool.andb_false_r; reflexivity. }
  destruct (os_sched_disabled_checkpoint_eq entry_2 Hen) as [Hswitch Hcheckpoint].
  assert (Hprefix : os_sched_prefix_state entry_2 = entry_2).
  { unfold os_sched_prefix_state; rewrite Hcheckpoint; apply replace_SchedS_put_back. }
  assert (Hreturn : os_sched_c_return environment.(task_stack_call_external) critical sg
    entry_2 scheduled_2 scheduled_2 entry_2).
  { unfold os_sched_c_return; rewrite Hswitch, Hprefix; auto. }
  Exists scheduled_2 entry_2 entry_2 scheduled_2; entailer!.
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_stack_context; entailer!.
  pose proof (proj2 (os_sched_work_cells_entry_equiv sg entry_2)) as Hcells.
  unfold os_sched_work_cells in Hcells.
  unfold os_sched_global_addresses in PreH3.
  destruct PreH3 as [Hints [Hlocks [Hhigh [Hcur [Hptr [Htable [Hctr Hnew]]]]]]].
  rewrite Hints, Hlocks, Hcur, Hptr, Htable, Hctr.
  sep_apply_l_atomic Hcells.
  unfold UCOS2_inv; entailer!.
Qed.

Lemma proof_of_OS_Sched_entail_wit_4_4 : OS_Sched_entail_wit_4_4.
Proof.
  left; intros.
  assert (Hint : os_sched_ints entry_2 <> 0).
  { intro Hzero; rewrite Hzero in PreH1; exact (PreH1 eq_refl). }
  assert (Hen : os_sched_selection_enabled entry_2 = false).
  { unfold os_sched_selection_enabled; fold (os_sched_ints entry_2).
    rewrite (proj2 (Z.eqb_neq _ _) Hint); reflexivity. }
  destruct (os_sched_disabled_checkpoint_eq entry_2 Hen) as [Hswitch Hcheckpoint].
  assert (Hprefix : os_sched_prefix_state entry_2 = entry_2).
  { unfold os_sched_prefix_state; rewrite Hcheckpoint; apply replace_SchedS_put_back. }
  assert (Hreturn : os_sched_c_return environment.(task_stack_call_external) critical sg
    entry_2 scheduled_2 scheduled_2 entry_2).
  { unfold os_sched_c_return; rewrite Hswitch, Hprefix; auto. }
  Exists scheduled_2 entry_2 entry_2 scheduled_2; entailer!.
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_stack_context; entailer!.
  pose proof (proj2 (os_sched_work_cells_entry_equiv sg entry_2)) as Hcells.
  unfold os_sched_work_cells in Hcells.
  unfold os_sched_global_addresses in PreH2.
  destruct PreH2 as [Hints [Hlocks [Hhigh [Hcur [Hptr [Htable [Hctr Hnew]]]]]]].
  rewrite Hints, Hlocks, Hcur, Hptr, Htable, Hctr.
  sep_apply_l_atomic Hcells.
  unfold UCOS2_inv; entailer!.
Qed.

Lemma proof_of_OS_Sched_return_wit_1 : OS_Sched_return_wit_1.
Proof.
  left; intros.
  assert (Hsource : kernel_call_task_source context before ->
    kernel_call_task_source scheduled entry).
  { intro Hinitial.
    apply (proj2 (task_tcb_init_stack_same_call_source_iff scheduled context entry PreH3)).
    exact (PreH4 Hinitial). }
  assert (Hstorage : os_sched_requests_switch entry = true ->
    os_sched_current_storage_binding sg scheduled entry).
  { intro Hswitch; exact (proj1 (proj2 PreH6 Hswitch)). }
  sep_apply_l_atomic (os_sched_continuation_restore_history_output_return
    environment critical saved_local sg context scheduled returned mask cpu_sr before entry final
    PreH9 PreH3 Hsource Hstorage PreH7 PreH8 PreH5).
  entailer!.
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_3_pure : OS_Sched_partial_solve_wit_3_pure.
Proof.
  left; intros.
  assert (Haddresses : sched_new_global_addresses sg
    (&("OSUnMapTbl")) (&("OSRdyGrp")) (&("OSRdyTbl")) (&("OSPrioHighRdy"))).
  { unfold os_sched_global_addresses in PreH3; tauto. }
  entailer!.
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_1 : OS_Sched_which_implies_wit_1.
Proof.
  left; intros.
  unfold os_sched_continuation_call_pre, os_sched_continuation_pre; Intros.
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_save_input_closed_world
    environment critical saved_local sg context mask before)).
  entailer!.
Qed.

