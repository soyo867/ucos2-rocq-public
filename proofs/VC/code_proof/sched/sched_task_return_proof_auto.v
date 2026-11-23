(** Prepared current canonical auto partition; 48-target migration; fresh check pending. *)
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

Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_entry_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_local_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_counter_entry_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_caller_control_spec.

Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_caller_control_spec.

Lemma proof_of_OS_Sched_safety_wit_1 : sched_task_return_goal.OS_Sched_safety_wit_1.
Proof.
  unfold OS_Sched_safety_wit_1; intros; split; cbv; easy.
Qed.

Lemma proof_of_OS_Sched_safety_wit_2 : sched_task_return_goal.OS_Sched_safety_wit_2.
Proof.
  unfold OS_Sched_safety_wit_2; intros; split; cbv; easy.
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_1_pure : sched_task_return_goal.OS_Sched_partial_solve_wit_1_pure.
Proof.
  unfold OS_Sched_partial_solve_wit_1_pure; intros.
  repeat (first [assumption | reflexivity | split |
    eapply FlagPendEntryControl.flag_pend_running_protocol_entry; eassumption]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_1 : sched_task_return_goal.OS_Sched_partial_solve_wit_1.
Proof.
  unfold OS_Sched_partial_solve_wit_1, OS_Sched_partial_solve_wit_1_aux.
  intros _; intros.
  repeat (first [assumption | reflexivity | split |
    eapply FlagPendEntryControl.flag_pend_running_protocol_entry; eassumption]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_2_pure : sched_task_return_goal.OS_Sched_partial_solve_wit_2_pure.
Proof.
  unfold OS_Sched_partial_solve_wit_2_pure; intros.
  repeat (first [assumption | reflexivity | split |
    eapply FlagPendEntryControl.flag_pend_running_protocol_entry; eassumption]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_2 : sched_task_return_goal.OS_Sched_partial_solve_wit_2.
Proof.
  unfold OS_Sched_partial_solve_wit_2, OS_Sched_partial_solve_wit_2_aux.
  intros _; intros.
  repeat (first [assumption | reflexivity | split |
    eapply FlagPendEntryControl.flag_pend_running_protocol_entry; eassumption]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_3_pure : sched_task_return_goal.OS_Sched_partial_solve_wit_3_pure.
Proof.
  unfold OS_Sched_partial_solve_wit_3_pure; intros.
  repeat (first [assumption | reflexivity | split |
    eapply FlagPendEntryControl.flag_pend_running_protocol_entry; eassumption]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_3 : sched_task_return_goal.OS_Sched_partial_solve_wit_3.
Proof.
  unfold OS_Sched_partial_solve_wit_3, OS_Sched_partial_solve_wit_3_aux.
  intros _; intros.
  repeat (first [assumption | reflexivity | split |
    eapply FlagPendEntryControl.flag_pend_running_protocol_entry; eassumption]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_4 : sched_task_return_goal.OS_Sched_partial_solve_wit_4.
Proof.
  unfold OS_Sched_partial_solve_wit_4, OS_Sched_partial_solve_wit_4_aux.
  intros _; intros.

  repeat (first [assumption | reflexivity | split |
    eapply FlagPendActiveCallerControl.flag_pend_caller_counters_zero_from_counters; eassumption |
    eapply FlagPendEntryControl.flag_pend_running_protocol_entry; eassumption]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_5_pure : sched_task_return_goal.OS_Sched_partial_solve_wit_5_pure.
Proof.
  unfold OS_Sched_partial_solve_wit_5_pure; intros.
  repeat (first [assumption | reflexivity | split |
    eapply FlagPendEntryControl.flag_pend_running_protocol_entry; eassumption]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_5 : sched_task_return_goal.OS_Sched_partial_solve_wit_5.
Proof.
  unfold OS_Sched_partial_solve_wit_5, OS_Sched_partial_solve_wit_5_aux.
  intros _; intros.
  repeat (first [assumption | reflexivity | split |
    eapply FlagPendEntryControl.flag_pend_running_protocol_entry; eassumption]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_6_pure : sched_task_return_goal.OS_Sched_partial_solve_wit_6_pure.
Proof.
  unfold OS_Sched_partial_solve_wit_6_pure; intros.
  repeat (first [assumption | reflexivity | split |
    eapply FlagPendEntryControl.flag_pend_running_protocol_entry; eassumption]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_6 : sched_task_return_goal.OS_Sched_partial_solve_wit_6.
Proof.
  unfold OS_Sched_partial_solve_wit_6, OS_Sched_partial_solve_wit_6_aux.
  intros _; intros.
  repeat (first [assumption | reflexivity | split |
    eapply FlagPendEntryControl.flag_pend_running_protocol_entry; eassumption]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_7 : sched_task_return_goal.OS_Sched_partial_solve_wit_7.
Proof.
  unfold OS_Sched_partial_solve_wit_7, OS_Sched_partial_solve_wit_7_aux.
  intros _ before mask context sg critical active local environment entry_heap save_caller save_scheduled
    save_entry save_local save_after_heap active_before cpu_sr PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
    Hrequires_control1 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18.
  assert (Hnew_globals : sched_new_global_addresses sg
    (&("OSUnMapTbl")) (&("OSRdyGrp")) (&("OSRdyTbl")) (&("OSPrioHighRdy"))).
  { unfold os_sched_global_addresses in *; tauto. }
  entailer!.
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_8 : sched_task_return_goal.OS_Sched_partial_solve_wit_8.
Proof.
  unfold OS_Sched_partial_solve_wit_8.
  intros before mask context sg critical active environment scheduled entry entry_local cpu_sr PreH1 PreH2 PreH3
    Hrequires_control1 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
    PreH17 PreH18 PreH19.
  sep_apply (PtrArray.full_split_to_missing_i
    (&("OSTCBPrioTbl")) (os_sched_selected entry) 64 (os_sched_table sg entry) 0 ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_9 : sched_task_return_goal.OS_Sched_partial_solve_wit_9.
Proof.
  unfold OS_Sched_partial_solve_wit_9; intros.
  repeat (first [assumption | reflexivity | split |
    eapply FlagPendEntryControl.flag_pend_running_protocol_entry; eassumption]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_10 : sched_task_return_goal.OS_Sched_partial_solve_wit_10.
Proof.
  unfold OS_Sched_partial_solve_wit_10, OS_Sched_partial_solve_wit_10_aux.
  intros _ before mask context sg critical active environment cpu_sr scheduled entry entry_local switch_heap PreH1
    PreH2 PreH3 Hrequires_control1 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12.
  destruct (proj1 (os_sched_selection_enabled_iff entry)
    (proj2 (proj2 PreH7))) as [Hints Hlocks].
  change (os_sched_ints entry = 0) in Hints.
  change (os_sched_locks entry = 0) in Hlocks.
  intros heap Howned; repeat (first [assumption | reflexivity | split]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_11 : sched_task_return_goal.OS_Sched_partial_solve_wit_11.
Proof.
  unfold OS_Sched_partial_solve_wit_11; intros.
  repeat (first [assumption | reflexivity | split |
    eapply FlagPendEntryControl.flag_pend_running_protocol_entry; eassumption]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_12_pure : sched_task_return_goal.OS_Sched_partial_solve_wit_12_pure.
Proof.
  unfold OS_Sched_partial_solve_wit_12_pure; intros.
  repeat (first [assumption | reflexivity | split |
    eapply FlagPendEntryControl.flag_pend_running_protocol_entry; eassumption]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_12 : sched_task_return_goal.OS_Sched_partial_solve_wit_12.
Proof.
  unfold OS_Sched_partial_solve_wit_12, OS_Sched_partial_solve_wit_12_aux.
  intros _; intros.
  repeat (first [assumption | reflexivity | split |
    eapply FlagPendEntryControl.flag_pend_running_protocol_entry; eassumption]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_13_pure : sched_task_return_goal.OS_Sched_partial_solve_wit_13_pure.
Proof.
  unfold OS_Sched_partial_solve_wit_13_pure; intros.
  repeat (first [assumption | reflexivity | split |
    eapply FlagPendEntryControl.flag_pend_running_protocol_entry; eassumption]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_13 : sched_task_return_goal.OS_Sched_partial_solve_wit_13.
Proof.
  unfold OS_Sched_partial_solve_wit_13, OS_Sched_partial_solve_wit_13_aux.
  intros _; intros.
  repeat (first [assumption | reflexivity | split |
    eapply FlagPendEntryControl.flag_pend_running_protocol_entry; eassumption]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_14 : sched_task_return_goal.OS_Sched_partial_solve_wit_14.
Proof.
  unfold OS_Sched_partial_solve_wit_14, OS_Sched_partial_solve_wit_14_aux.
  intros _; intros.

  repeat (first [assumption | reflexivity | split |
    eapply FlagPendActiveCallerControl.flag_pend_caller_counters_zero_from_counters; eassumption |
    eapply FlagPendEntryControl.flag_pend_running_protocol_entry; eassumption]).
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_15_pure : sched_task_return_goal.OS_Sched_partial_solve_wit_15_pure.
Proof.
  unfold OS_Sched_partial_solve_wit_15_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OS_Sched_partial_solve_wit_15 : sched_task_return_goal.OS_Sched_partial_solve_wit_15.
Proof.
  unfold OS_Sched_partial_solve_wit_15, OS_Sched_partial_solve_wit_15_aux.
  intros _; intros.
  entailer!.
Qed.
