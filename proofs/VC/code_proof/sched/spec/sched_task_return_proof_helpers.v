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

Lemma os_sched_selected_work_cells_prefix_inv : forall sg entry,
  UCOS2_state_inv sg entry -> os_sched_selection_enabled entry = true ->
  entry.(SchedState).(readyList) <> nil ->
  os_sched_fields_work_cells sg entry (os_sched_selected entry) (os_sched_selected_tcb sg entry)
    (if os_sched_requests_switch entry
     then (os_sched_counter entry + 1) mod 4294967296 else os_sched_counter entry) |--
  UCOS2_fields_inv sg (os_sched_prefix_state entry) ** unmap_table_rep sg.
Proof.
  intros sg entry Hvalid Henabled Hnonempty.
  pose proof (proj1 (os_sched_selection_enabled_iff entry) Henabled) as [Hints Hlocks].
  assert (Hintr : interrupt_in_range entry.(IntrState)).
  { unfold interrupt_in_range; rewrite Hints, Hlocks; lia. }
  unfold os_sched_prefix_state.
  sep_apply_r_atomic (os_sched_fields_prefix_merge_inv sg entry Hvalid (fun _ => Hnonempty)).
  unfold os_sched_fields_work_cells, os_sched_fields_work_frame,
    os_sched_fields_remaining_task_storage_sched, os_sched_prefix_rep,
    os_sched_prefix_physical_rep, os_sched_counter_stage.
  rewrite Henabled.
  unfold sched_new_rep, sched_cache_cells, sched_physical_without_high,
    task_public_storage, task_public_storage_without_prio_tbl, store_prio_tbl,
    UCOS2_raw_rep_missing_task_storage_sched_flag, UCOS2_selected_rep.
  rewrite sched_rows_array_equiv.
  unfold os_sched_ints, os_sched_locks, os_sched_group, os_sched_rows,
    os_sched_selected, os_sched_selected_tcb, os_sched_current, os_sched_counter, os_sched_table.
  cbn [UCOS2_module_rep].
  destruct (os_sched_requests_switch entry);
    cbn [sched_increment_switch_counter curSchedPrio curTaskID ctxSwCtr isRunning];
    unfold interrupt_inv, store_int_state; entailer!.
Qed.

Lemma os_sched_selected_work_cells_masked : forall environment critical local active
  sg call saved acquired entry,
  UCOS2_state_inv sg entry -> os_sched_selection_enabled entry = true ->
  entry.(SchedState).(readyList) <> nil ->
  task_stack_live_coverage entry.(TskState) (task_stack_call_active_key call) ->
  os_sched_active_local_stable active ->
  critical_region_masked environment.(task_stack_call_platform) critical sg
    call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
  task_tcb_init_stack_context environment call ** os_sched_fields_capsules environment local entry **
  active call entry **
  os_sched_fields_work_cells sg entry (os_sched_selected entry) (os_sched_selected_tcb sg entry)
    (if os_sched_requests_switch entry
     then (os_sched_counter entry + 1) mod 4294967296 else os_sched_counter entry) |--
  kernel_continuation_call_masked environment.(task_stack_call_continuations) kernel_program_fields_inv
    local critical sg (task_stack_call_active_key call) call saved acquired (os_sched_prefix_state entry) **
  active call (os_sched_prefix_state entry).
Proof.
  intros environment critical local active sg call saved acquired entry Hvalid Henabled
    Hnonempty Hcoverage Hstable.
  sep_apply_l_atomic (os_sched_selected_work_cells_prefix_inv sg entry Hvalid Henabled Hnonempty).
  sep_apply_l_atomic (proj1 (os_sched_active_prefix_transport active call entry Hstable)).
  sep_apply_r_atomic (proj1 (os_sched_fields_restore_input_masked_world environment critical local
    sg call saved acquired (os_sched_prefix_state entry))).
  unfold os_sched_fields_restore_input, task_tcb_init_stack_context.
  assert (Hcapsules : os_sched_fields_capsules environment local (os_sched_prefix_state entry) =
    os_sched_fields_capsules environment local entry) by reflexivity.
  rewrite Hcapsules.
  change (task_stack_live_coverage (os_sched_prefix_state entry).(TskState)
    (task_stack_call_active_key call)) in Hcoverage.
  entailer!.
Qed.
