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
From Ucos2Verify.VC.code.core Require Import init_task_idle_goal.
From Ucos2Verify.VC.code.core Require Import init_task_idle_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.core.spec.init_task_idle_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OS_InitTaskIdle_return_wit_1 : OS_InitTaskIdle_return_wit_1.
Proof.
  left; intros; Intros.
  unfold init_task_idle_post.
  Exists returned middle create_error current err.
  entailer!.
  eapply init_task_idle_name_post_safe_return; eassumption.
Qed. 

Lemma proof_of_OS_InitTaskIdle_partial_solve_wit_2_pure : OS_InitTaskIdle_partial_solve_wit_2_pure.
Proof.
  left; intros.
  pose proof (init_task_idle_create_arguments entry base) as Harguments.
  subst entry base task_return.
  unfold init_task_idle_create_program in PreH5.
  entailer!; try assumption; try reflexivity.
  all: replace (( &( "OSTaskIdleStk" ) ) + 0 * sizeof(UINT))
    with ( &( "OSTaskIdleStk" ) ) by lia.
  all: exact Harguments.
Qed. 

Lemma proof_of_OS_InitTaskIdle_partial_solve_wit_4_pure : OS_InitTaskIdle_partial_solve_wit_4_pure.
Proof.
  left; intros; entailer!; lia.
Qed. 

Lemma proof_of_OS_InitTaskIdle_which_implies_wit_1 : OS_InitTaskIdle_which_implies_wit_1.
Proof.
  left; intros.
  rewrite (init_task_idle_entry_open environment critical saved_local sg entry base
    task_return lower old_frame upper call mask LitMap literals initial).
  Intros.
  assert (Hsafe : task_create_safe initial
    (init_task_idle_create_program environment critical sg entry base task_return
      lower old_frame upper call mask LitMap)
    (init_task_idle_create_postcondition environment critical sg entry base task_return
      lower old_frame upper call mask LitMap initial X)).
  { apply init_task_idle_safe_create; [exact PreH1|tauto|exact PreH2]. }
  entailer!; try assumption.
Qed. 

Lemma proof_of_OS_InitTaskIdle_which_implies_wit_2 : OS_InitTaskIdle_which_implies_wit_2.
Proof.
  left; intros.
  unfold init_task_idle_empty_stack, task_create_stack_old_image.
  sep_apply_l_atomic (task_create_ext_boot_phase_post_forget environment critical
    saved_local sg (init_task_idle_stack_region base) (init_task_idle_create_args entry base)
    task_return lower old_frame upper nil (lower ++ old_frame ++ upper) nil
    call mask initial create_error_2
    (init_task_idle_create_postcondition environment critical sg entry base task_return
      lower old_frame upper call mask LitMap initial X)).
  rewrite (init_task_idle_create_post_open environment critical saved_local sg entry base
    task_return lower old_frame upper call mask LitMap literals initial X create_error_2).
  Intros returned middle.
  assert (Hcreated : init_task_idle_created environment critical sg entry base task_return
    lower old_frame upper call mask LitMap initial X returned middle create_error_2) by tauto.
  assert (Hread : readable_name middle.(NameState) (LitMap "uC/OS-II Idle") init_task_idle_name_chars).
  { unfold init_task_idle_created, init_task_idle_create_postcondition in Hcreated; tauto. }
  sep_apply_l_atomic (init_task_idle_name_call_split_literal environment.(task_stack_call_platform)
    critical sg returned.(os_sched_call_invocation) returned.(os_sched_call_origin)
    mask middle (LitMap "uC/OS-II Idle") Hread).
  Exists returned middle create_error_2.
  entailer!; unfold init_task_idle_created in Hcreated; try tauto.
  repeat apply sepcon_cancel_end; entailer!.
Qed. 

Lemma proof_of_OSTaskNameSet_derive_borrowed_literal_spec_by_actual_spec : OSTaskNameSet_derive_borrowed_literal_spec_by_actual_spec.
Proof.
  Unfold; intros; Intros.
  Exists platform_borrowed_literal_spec critical_borrowed_literal_spec
    sg_borrowed_literal_spec before_borrowed_literal_spec invocation_borrowed_literal_spec
    origin_borrowed_literal_spec mask_borrowed_literal_spec request_borrowed_literal_spec
    name_borrowed_literal_spec error_addr_borrowed_literal_spec X_borrowed_literal_spec.
  sep_apply_l_atomic (init_task_idle_name_call_merge_literal platform_borrowed_literal_spec
    critical_borrowed_literal_spec sg_borrowed_literal_spec invocation_borrowed_literal_spec
    origin_borrowed_literal_spec mask_borrowed_literal_spec before_borrowed_literal_spec
    name_borrowed_literal_spec).
  entailer!.
  apply (proj1 (derivable1s_wand_sepcon_adjoint _ _ _)).
  Intros err current; Exists err current; entailer!.
Qed. 

