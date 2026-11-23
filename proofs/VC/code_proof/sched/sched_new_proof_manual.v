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
From Ucos2Verify.VC.code.sched Require Import sched_new_goal.
From Ucos2Verify.VC.code.sched Require Import sched_new_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OS_SchedNew_safety_wit_1 : OS_SchedNew_safety_wit_1.
Proof.
  unfold OS_SchedNew_safety_wit_1; left; intros.
  rewrite unmap_table_Znth by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite signed_last_nbits_eq by (cbn; lia).
  entailer!; cbn in *; lia.
Qed.

Lemma proof_of_OS_SchedNew_safety_wit_2 : OS_SchedNew_safety_wit_2.
Proof.
  unfold OS_SchedNew_safety_wit_2; left; intros.
  rewrite signed_last_nbits_eq by (cbn; lia).
  entailer!; cbn in *; lia.
Qed.

Lemma proof_of_OS_SchedNew_entail_wit_1 : OS_SchedNew_entail_wit_1.
Proof.
  unfold OS_SchedNew_entail_wit_1; left; intros.
  rewrite unmap_table_Znth by lia.
  pose proof (unmap_in_range (Znth (unmap_value group) rows 0)).
  assert (Hrow_range : UCharArray.full (&("OSRdyTbl")) 8 rows |--
    coq_prop (0 <= Znth (unmap_value group) rows 0 < 256)).
  {
    sep_apply (UCharArray.full_split_to_missing_i
      (&("OSRdyTbl")) (unmap_value group) 8 rows 0); [|lia].
    prop_apply_p (store_uchar_range
      (&("OSRdyTbl") + unmap_value group * sizeof(UCHAR))
      (Znth (unmap_value group) rows 0)).
    Intros_p Hrow.
    apply derivable1s_coq_prop_r.
    change (0 <= Znth (unmap_value group) rows 0 <= 255) in Hrow.
    lia.
  }
  prop_apply_p Hrow_range.
  Intros_p Hrow.
  entailer!; lia.
Qed.

Lemma proof_of_OS_SchedNew_return_wit_1 : OS_SchedNew_return_wit_1.
Proof.
  unfold OS_SchedNew_return_wit_1; left; intros.
  rewrite unmap_table_Znth by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite signed_last_nbits_eq by (cbn; lia).
  rewrite unsigned_last_nbits_eq by (cbn; lia).
  unfold sched_new_rep, unmap_table_rep, sched_new_priority.
  rewrite <- PreH2.
  replace (2 ^ 3) with 8 by reflexivity.
  destruct PreH1 as (Hunmap & Hgroup & Hrows & Hhigh).
  rewrite <- Hunmap, <- Hgroup, <- Hrows, <- Hhigh.
  unfold sched_new_global_addresses.
  entailer!.
Qed.

Lemma proof_of_OS_SchedNew_which_implies_wit_1 : OS_SchedNew_which_implies_wit_1.
Proof.
  unfold OS_SchedNew_which_implies_wit_1; left; intros.
  unfold sched_new_rep, unmap_table_rep.
  pose proof (unmap_in_range group).
  prop_apply_p (store_uchar_range (g_OSRdyGrp sg) group).
  Intros_p Hgroup_range.
  change (0 <= group <= 255) in Hgroup_range.
  destruct PreH1 as (Hunmap & Hgroup & Hrows & Hhigh).
  rewrite <- Hunmap, <- Hgroup, <- Hrows, <- Hhigh.
  unfold sched_new_global_addresses.
  entailer!; lia.
Qed.
