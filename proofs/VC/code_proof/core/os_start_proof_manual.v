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
From Ucos2Verify.VC.code.core Require Import os_start_goal.
From Ucos2Verify.VC.code.core Require Import os_start_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.core.spec.os_start_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSStart_return_wit_1 : OSStart_return_wit_1.
Proof.
  left; intros frame X running entry env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6.
  assert (Hrunning : running <> 0).
  { intro Heq; subst running; change (0 <> 0) in PreH1; contradiction. }
  rewrite PreH4.
  apply os_start_nonzero_return_resources; assumption.
Qed.

Lemma proof_of_OSStart_partial_solve_wit_2_pure : OSStart_partial_solve_wit_2_pure.
Proof.
  left; intros frame X running entry env PreH1 PreH2 PreH3 PreH4 PreH5 PreH6.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range (&("OSRunning")) running).
  Intros.
  assert (Hpromoted : unsigned_last_nbits running 32 = running).
  { apply unsigned_last_nbits_eq.
    change (0 <= running < 4294967296).
    match goal with
    | Hrange : 0 <= running <= _ |- _ =>
        change (0 <= running <= 255) in Hrange; lia
    end. }
  rewrite Hpromoted in PreH1.
  entailer!.
Qed.

Lemma proof_of_OSStart_which_implies_wit_1 : OSStart_which_implies_wit_1.
Proof.
  left; intros frame X running entry env PreH1.
  rewrite PreH1.
  unfold os_start_pre, os_start_running_address, os_start_sg.
  entailer!.
Qed.

Lemma proof_of_OSStart_which_implies_wit_2 : OSStart_which_implies_wit_2.
Proof.
  left; intros frame X running entry env PreH1 PreH2 PreH3 PreH4.
  subst running.
  assert (Hstartup : os_start_startup env entry) by (apply PreH3; reflexivity).
  rewrite PreH1.
  unfold os_start_running_address, os_start_sg.
  sep_apply_l_atomic (os_start_zero_sched_resources env entry frame Hstartup).
  entailer!.
Qed.

Lemma proof_of_OSStart_which_implies_wit_3 : OSStart_which_implies_wit_3.
Proof.
  left; intros frame entry env PreH1.
  unfold os_start_global_addresses, sched_new_global_addresses in PreH1.
  destruct PreH1 as [[Hunmap [Hgroup [Hrows Hhigh]]]
    [Hpriority [Htable [Hcurrent [Hhigh_task Hrunning]]]]].
  rewrite Hhigh, Hpriority, Hcurrent, Hhigh_task, Htable.
  unfold os_start_sg.
  pose proof (os_start_select_cache_resources env entry frame) as Hselect.
  unfold os_start_priority in Hselect.
  sep_apply_l_atomic Hselect.
  unfold os_start_cache_cells.
  entailer!.
Qed.

Lemma proof_of_OSStart_which_implies_wit_4 : OSStart_which_implies_wit_4.
Proof.
  left; intros frame entry env PreH1.
  unfold os_start_global_addresses in PreH1.
  destruct PreH1 as [Hsched [Hpriority [Htable [Hcurrent [Hhigh_task Hrunning]]]]].
  rewrite Htable.
  fold (os_start_priority entry).
  sep_apply_l_atomic (os_start_table_split env entry frame).
  entailer!.
Qed.

Lemma proof_of_OSStart_which_implies_wit_5 : OSStart_which_implies_wit_5.
Proof.
  left; intros frame X entry env PreH1 PreH2 PreH3.
  unfold os_start_global_addresses, sched_new_global_addresses in PreH1.
  destruct PreH1 as [[Hunmap [Hgroup [Hrows Hhigh]]]
    [Hpriority [Htable [Hcurrent [Hhigh_task Hrunning]]]]].
  rewrite Hhigh, Hpriority, Hcurrent, Hhigh_task, Htable.
  fold (os_start_priority entry).
  sep_apply_l_atomic (os_start_table_merge env entry frame).
  sep_apply_r_atomic (os_start_complete_high_pre env entry X frame PreH3 PreH2).
  unfold os_start_cache_cells.
  entailer!.
Qed.

