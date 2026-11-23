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
From Ucos2Verify.VC.code.core Require Import init_task_idle_continuation_goal.
From Ucos2Verify.VC.code.core Require Import init_task_idle_continuation_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.core.spec.init_task_idle_continuation_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.


Require Import Ucos2Verify.VC.code.core.spec.init_task_idle_continuation_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OS_InitTaskIdle_return_wit_1 : OS_InitTaskIdle_return_wit_1.
Proof.
left; intros; Intros.
  assert (Hphase : initial.(TimerState).(timerInitPhase) = middle.(TimerState).(timerInitPhase)).
  { match goal with H : init_task_idle_continuation_phase_frame initial middle |- _ => exact H end. }
  sep_apply_r_atomic (init_task_idle_continuation_post_close environment critical saved_local sg entry base task_return
    lower old_frame upper call mask LitMap literals initial X returned middle create_error returned_2 current err
    ltac:(eassumption) Hphase ltac:(eassumption)); entailer!.
Qed.

Lemma proof_of_OS_InitTaskIdle_partial_solve_wit_2_pure : OS_InitTaskIdle_partial_solve_wit_2_pure.
Proof.
left; intros.
  pose proof (init_task_idle_create_arguments entry base) as Harguments.
  subst entry base task_return.
  unfold init_task_idle_continuation_create_program in PreH5.
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
  intros heap Hpre.
  pose proof (init_task_idle_continuation_name_api_pre_entry environment critical saved_local sg
    (init_task_idle_stack_region base) (init_task_idle_create_args entry base) task_return
    lower old_frame upper call mask initial LitMap literals heap Hpre) as [Hentry Hsame_pre].
  assert (Hsafe : task_create_ext_continuation_safe initial
    (init_task_idle_continuation_create_program environment critical sg entry base task_return
      lower old_frame upper call mask LitMap)
    (init_task_idle_continuation_create_postcondition environment critical sg entry base task_return
      lower old_frame upper call mask LitMap initial X)).
  { apply init_task_idle_continuation_safe_create; [exact PreH1|exact Hentry|tauto|exact PreH2]. }
  split; [exact PreH1|].
  split; [tauto|]. split; [tauto|]. split; [tauto|].
  split; [exact Hsafe|exact Hsame_pre].
Qed.

Lemma proof_of_OS_InitTaskIdle_which_implies_wit_2 : OS_InitTaskIdle_which_implies_wit_2.
Proof.
left; intros.
  unfold init_task_idle_empty_stack, task_create_stack_old_image.
  assert (Hstop : initial.(SchedState).(isRunning) = false) by exact PreH1.
  sep_apply_l_atomic (init_task_idle_continuation_create_post_open environment critical saved_local
    sg entry base task_return lower old_frame upper call mask LitMap literals initial X
    create_error_2 Hstop).
  Intros returned middle.
  assert (Hphase : init_task_idle_continuation_phase_frame initial middle).
  { unfold init_task_idle_continuation_phase_frame; tauto. }
  assert (Hcreated : init_task_idle_continuation_created environment critical sg entry base task_return
    lower old_frame upper call mask LitMap initial X returned middle create_error_2) by tauto.
  assert (Hread : readable_name middle.(NameState) (LitMap "uC/OS-II Idle") init_task_idle_name_chars).
  { unfold init_task_idle_continuation_created, init_task_idle_continuation_create_postcondition in Hcreated; tauto. }
  sep_apply_l_atomic (init_task_idle_continuation_split_literal environment critical saved_local sg returned
    mask middle (LitMap "uC/OS-II Idle") Hread).
  Exists returned middle create_error_2.
  unfold task_name_set_continuation_call_binding; entailer!; unfold init_task_idle_continuation_created in Hcreated; try tauto.
  repeat apply sepcon_cancel_end; entailer!.
Qed.

Lemma proof_of_OSTaskNameSet_derive_borrowed_literal_spec_by_actual_spec : OSTaskNameSet_derive_borrowed_literal_spec_by_actual_spec.
Proof.
Unfold; intros; Intros.
  Exists environment_borrowed_literal_spec critical_borrowed_literal_spec saved_local_borrowed_literal_spec
    platform_borrowed_literal_spec sg_borrowed_literal_spec before_borrowed_literal_spec call_borrowed_literal_spec
    invocation_borrowed_literal_spec origin_borrowed_literal_spec mask_borrowed_literal_spec
    request_borrowed_literal_spec name_borrowed_literal_spec error_addr_borrowed_literal_spec X_borrowed_literal_spec.
  sep_apply_l_atomic (init_task_idle_continuation_merge_literal environment_borrowed_literal_spec critical_borrowed_literal_spec
    saved_local_borrowed_literal_spec sg_borrowed_literal_spec call_borrowed_literal_spec mask_borrowed_literal_spec
    before_borrowed_literal_spec name_borrowed_literal_spec).
  entailer!.
  apply (proj1 (derivable1s_wand_sepcon_adjoint _ _ _)).
  Intros returned err current; Exists returned err current; entailer!.
Qed.
