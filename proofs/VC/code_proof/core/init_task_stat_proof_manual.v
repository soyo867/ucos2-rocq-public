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
From Ucos2Verify.VC.code.core Require Import init_task_stat_goal.
From Ucos2Verify.VC.code.core Require Import init_task_stat_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.core.spec.init_task_stat_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OS_InitTaskStat_return_wit_1 : OS_InitTaskStat_return_wit_1.
Proof.
  left; intros; Intros.
  assert (Hreturn : safeexec_lib.safeExec (eq current)
    (StateRelBasic.StateRelMonad.ret tt) X).
  { eapply init_task_stat_name_post_safe_return; eassumption. }
  unfold init_task_stat_post.
  Exists returned middle create_error current err.
  entailer!.
Qed. 

Lemma proof_of_OS_InitTaskStat_partial_solve_wit_2_pure : OS_InitTaskStat_partial_solve_wit_2_pure.
Proof.
  left; intros.
  rewrite sizeof_uint, <- PreH6, <- PreH7, <- PreH8.
  replace ((128 - 1) * 4) with 508 by reflexivity.
  replace (0 * 4) with 0 by reflexivity.
  rewrite Z.add_0_r.
  replace (Z.lor 1 2) with 3 by reflexivity.
  unfold init_task_stat_create_program in PreH5.
  pose proof (init_task_stat_create_arguments entry base) as Harguments.
  entailer!.
Qed. 

Lemma proof_of_OS_InitTaskStat_partial_solve_wit_4_pure : OS_InitTaskStat_partial_solve_wit_4_pure.
Proof.
  left; intros; entailer!.
Qed. 

Lemma proof_of_OS_InitTaskStat_which_implies_wit_1 : OS_InitTaskStat_which_implies_wit_1.
Proof.
  left; intros.
  rewrite (init_task_stat_entry_open environment critical saved_local sg entry base
    task_return lower old_frame upper call mask LitMap literals initial).
  Intros.
  assert (Hsafe : task_create_safe initial
    (init_task_stat_create_program environment critical sg entry base task_return
      lower old_frame upper call mask LitMap)
    (init_task_stat_create_postcondition environment critical sg entry base task_return
      lower old_frame upper call mask LitMap initial X)).
  { apply init_task_stat_safe_create; tauto. }
  entailer!; tauto.
Qed. 

Lemma proof_of_OS_InitTaskStat_which_implies_wit_2 : OS_InitTaskStat_which_implies_wit_2.
Proof.
  left; intros.
  sep_apply_l_atomic (task_create_ext_boot_phase_post_forget environment critical saved_local
    sg (init_task_stat_stack_region base) (init_task_stat_create_args entry base)
    task_return lower old_frame upper init_task_stat_empty_stack
    (task_create_stack_old_image lower old_frame upper) init_task_stat_empty_stack
    call mask initial create_error_2
    (init_task_stat_create_postcondition environment critical sg entry base task_return
      lower old_frame upper call mask LitMap initial X)).
  unfold init_task_stat_empty_stack, task_create_stack_old_image.
  sep_apply_l_atomic (init_task_stat_create_post_open environment critical saved_local
    sg entry base task_return lower old_frame upper call mask LitMap literals initial X
    create_error_2).
  Intros returned middle.
  assert (Hcreated : init_task_stat_created environment critical sg entry base task_return
    lower old_frame upper call mask LitMap initial X returned middle create_error_2) by tauto.
  assert (Hinv : UCOS2_state_inv sg middle).
  { unfold init_task_stat_created in Hcreated; tauto. }
  assert (Hread : readable_name middle.(NameState) (LitMap "uC/OS-II Stat")
    init_task_stat_name_chars).
  { unfold init_task_stat_created, init_task_stat_create_postcondition in Hcreated; tauto. }
  sep_apply_l_atomic (init_task_stat_name_call_split_literal
    (task_stack_call_platform environment) critical sg
    (os_sched_call_invocation returned) (os_sched_call_origin returned) mask middle
    (LitMap "uC/OS-II Stat") Hread).
  Exists returned middle create_error_2.
  entailer!; try tauto.
  repeat apply sepcon_cancel_end; entailer!.
Qed. 

Lemma proof_of_OSTaskNameSet_derive_borrowed_literal_spec_by_actual_spec : OSTaskNameSet_derive_borrowed_literal_spec_by_actual_spec.
Proof.
  intros perr pname prio X error_addr name request mask origin invocation before
    sg critical platform; Intros.
  Exists platform critical sg before invocation origin mask request name error_addr X.
  sep_apply_l_atomic (init_task_stat_name_call_merge_literal platform critical sg invocation
    origin mask before name).
  entailer!.
  apply (proj1 (derivable1s_wand_sepcon_adjoint _ _ _)); entailer!.
Qed. 

