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
From Ucos2Verify.VC.code.timer Require Import tmr_init_task_goal.
From Ucos2Verify.VC.code.timer Require Import tmr_init_task_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_init_task_timer_phase_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OSTmr_InitTask_return_wit_1 : OSTmr_InitTask_return_wit_1.
Proof.
  unfold OSTmr_InitTask_return_wit_1; left; intros.
  Intros.
  assert (Hphase : tmr_init_task_timer_phase_eq initial_phase_spec current).
  { assert (Hmiddle : tmr_init_task_timer_phase_eq initial_phase_spec middle)
      by (unfold tmr_init_task_phase_created in *; tauto).
    assert (Hname : tmr_init_task_timer_phase_eq middle current)
      by (eapply tmr_init_task_name_post_timer_phase_eq; eassumption).
    unfold tmr_init_task_timer_phase_eq in *; congruence. }
  unfold tmr_init_task_phase_post.
  Exists returned middle create_error receipt current err.
  entailer!.
  eapply tmr_init_task_name_post_safe_return; eassumption.
Qed.

Lemma proof_of_OSTmr_InitTask_partial_solve_wit_2_pure : OSTmr_InitTask_partial_solve_wit_2_pure.
Proof.
  unfold OSTmr_InitTask_partial_solve_wit_2_pure; left; intros.
  subst entry_phase_spec base_phase_spec task_return_phase_spec.
  rewrite sizeof_uint.
  replace ((128 - 1) * 4) with 508 by reflexivity.
  replace (0 * 4) with 0 by reflexivity.
  rewrite Z.add_0_r.
  replace (Z.lor 1 2) with 3 by reflexivity.
  entailer!; try assumption; try reflexivity;
    apply tmr_init_task_create_arguments.
Qed.

Lemma proof_of_OSTmr_InitTask_partial_solve_wit_4_pure : OSTmr_InitTask_partial_solve_wit_4_pure.
Proof.
  unfold OSTmr_InitTask_partial_solve_wit_4_pure; left; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSTmr_InitTask_which_implies_wit_1 : OSTmr_InitTask_which_implies_wit_1.
Proof.
  unfold OSTmr_InitTask_which_implies_wit_1; left; intros.
  rewrite (tmr_init_task_entry_open environment_phase_spec critical_phase_spec saved_local_phase_spec sg_phase_spec entry_phase_spec base_phase_spec
    task_return_phase_spec lower_phase_spec old_frame_phase_spec upper_phase_spec call_phase_spec mask_phase_spec LitMap_phase_spec literals_phase_spec initial_phase_spec).
  Intros.
  assert (Hread : readable_name initial_phase_spec.(NameState) (LitMap_phase_spec "uC/OS-II Tmr")
    tmr_init_task_name_chars) by tauto.
  pose proof (tmr_init_task_safe_create environment_phase_spec critical_phase_spec sg_phase_spec entry_phase_spec base_phase_spec task_return_phase_spec
    lower_phase_spec old_frame_phase_spec upper_phase_spec call_phase_spec mask_phase_spec LitMap_phase_spec initial_phase_spec X_phase_spec PreH1 Hread PreH2) as Hsafe.
  entailer!; tauto.
Qed.

Lemma proof_of_OSTmr_InitTask_which_implies_wit_2 : OSTmr_InitTask_which_implies_wit_2.
Proof.
  unfold OSTmr_InitTask_which_implies_wit_2; left; intros.
  unfold tmr_init_task_empty_stack, task_create_stack_old_image.
  rewrite (tmr_init_task_phase_create_post_open environment_phase_spec critical_phase_spec saved_local_phase_spec sg_phase_spec entry_phase_spec base_phase_spec
    task_return_phase_spec lower_phase_spec old_frame_phase_spec upper_phase_spec call_phase_spec mask_phase_spec LitMap_phase_spec literals_phase_spec initial_phase_spec X_phase_spec create_error_2 PreH1).
  Intros returned middle receipt.
  assert (Hcreated : tmr_init_task_created environment_phase_spec critical_phase_spec sg_phase_spec entry_phase_spec base_phase_spec task_return_phase_spec
    lower_phase_spec old_frame_phase_spec upper_phase_spec call_phase_spec mask_phase_spec LitMap_phase_spec initial_phase_spec X_phase_spec returned middle create_error_2)
    by (unfold tmr_init_task_phase_created in *; tauto).
  assert (Hread : readable_name middle.(NameState) (LitMap_phase_spec "uC/OS-II Tmr")
    tmr_init_task_name_chars).
  { unfold tmr_init_task_created, tmr_init_task_create_postcondition in Hcreated; tauto. }
  rewrite (tmr_init_task_name_call_split_literal environment_phase_spec.(task_stack_call_platform)
    critical_phase_spec sg_phase_spec returned.(os_sched_call_invocation) returned.(os_sched_call_origin)
    mask_phase_spec middle (LitMap_phase_spec "uC/OS-II Tmr") Hread).
  Exists returned middle create_error_2 receipt.
  entailer!; unfold tmr_init_task_created in Hcreated; try tauto.
  repeat apply sepcon_cancel_end; entailer!.
Qed.

Lemma proof_of_OSTmr_InitTask_derive_api_spec_by_phase_spec :
  OSTmr_InitTask_derive_api_spec_by_phase_spec.
Proof.
  unfold OSTmr_InitTask_derive_api_spec_by_phase_spec; intros.
  Exists environment_api_spec critical_api_spec saved_local_api_spec sg_api_spec
    entry_api_spec base_api_spec task_return_api_spec mask_api_spec
    lower_api_spec old_frame_api_spec upper_api_spec call_api_spec initial_api_spec
    LitMap_api_spec literals_api_spec X_api_spec.
  entailer!.
  apply_sepcon_adjoint; elim_emp.
  apply tmr_init_task_phase_post_forget.
Qed.

Lemma proof_of_OSTaskNameSet_derive_borrowed_literal_spec_by_actual_spec : OSTaskNameSet_derive_borrowed_literal_spec_by_actual_spec.
Proof.
  unfold OSTaskNameSet_derive_borrowed_literal_spec_by_actual_spec.
  intros perr pname prio X error_addr name request mask origin invocation before sg critical platform.
  Intros.
  Exists platform critical sg before invocation origin mask request name error_addr X.
  sep_apply_l_atomic (tmr_init_task_name_call_merge_literal platform critical sg
    invocation origin mask before name).
  entailer!.
  apply (proj1 (derivable1s_wand_sepcon_adjoint _ _ _)).
  Intros err current.
  Exists err current.
  entailer!.
Qed.

