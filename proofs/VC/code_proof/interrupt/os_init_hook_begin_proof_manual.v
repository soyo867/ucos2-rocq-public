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
From Ucos2Verify.VC.code.interrupt Require Import os_init_hook_begin_goal.
From Ucos2Verify.VC.code.interrupt Require Import os_init_hook_begin_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.interrupt.spec.os_init_hook_begin_spec.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope sac.

Lemma proof_of_OSInitHookBegin_entail_wit_1 : OSInitHookBegin_entail_wit_1.
Proof.
  unfold OSInitHookBegin_entail_wit_1; left; intros.
  rewrite sizeof_uint.
  entailer!.
Qed.

Lemma proof_of_OSInitHookBegin_entail_wit_2 : OSInitHookBegin_entail_wit_2.
Proof.
  unfold OSInitHookBegin_entail_wit_2; left; intros.
  assert (Hdone : 0 <= 1024 - size < Zlength initial) by lia.
  assert (Haddr : base + (4 * (1024 - size)) =
      base + ((1024 - size) * sizeof(UINT))).
  { rewrite sizeof_uint; ring. }
  rewrite Haddr.
  unfold os_init_hook_begin_stack_cell_rest.
  sep_apply (task_stack_clear_rep_merge_zero_cell
    base initial (1024 - size) Hdone).
  replace (1024 - (size - 1)) with (1024 - size + 1) by lia.
  rewrite sizeof_uint.
  entailer!.
Qed.

Lemma proof_of_OSInitHookBegin_return_wit_1 : OSInitHookBegin_return_wit_1.
Proof.
  unfold OSInitHookBegin_return_wit_1; left; intros.
  assert (Hsize : size = 0) by lia; subst size.
  subst retval.
  rewrite Z.rem_mod_nonneg in PreH5 by lia.
  assert (Hvalid : valid_task_stack_region (os_init_hook_begin_region base)).
  { apply (proj2 (os_init_hook_begin_region_valid_iff base)).
    repeat split; assumption. }
  assert (Htop : armv7a_exception_stack_aligned_top
      (os_init_hook_begin_region base) =
      Z.land (( &( "OS_CPU_ExceptStk" )) + 1024 * sizeof(UINT)) 4294967288).
  { rewrite (armv7a_exception_stack_aligned_top_source_mask
      (os_init_hook_begin_region base) Hvalid).
    unfold task_stack_region_end, os_init_hook_begin_region.
    simpl; rewrite PreH3; reflexivity. }
  assert (Hlen : List.length initial = Z.to_nat 1024).
  { rewrite <- PreH7, Zlength_correct, Nat2Z.id; reflexivity. }
  unfold os_init_hook_begin_post.
  unfold armv7a_exception_stack_initialized.
  rewrite Htop.
  rewrite task_stack_fragments_rep_complete.
  unfold task_stack_clear_rep.
  replace (1024 - 0) with (Zlength initial) by lia.
  rewrite task_stack_clear_words_complete.
  rewrite PreH7.
  unfold task_stack_storage.
  cbn [os_init_hook_begin_region stackRegionBase stackRegionWords].
  rewrite Hlen.
  entailer!.
Qed.

Lemma proof_of_OSInitHookBegin_which_implies_wit_1 : OSInitHookBegin_which_implies_wit_1.
Proof.
  unfold OSInitHookBegin_which_implies_wit_1; left; intros.
  unfold os_init_hook_begin_pre.
  Intros.
  match goal with
  | Hregion : valid_task_stack_region (os_init_hook_begin_region base) |- _ =>
      apply (proj1 (os_init_hook_begin_region_valid_iff base)) in Hregion;
      destruct Hregion as [Hbase [Halign Hbound]]
  end.
  prop_apply_p (task_stack_storage_length (os_init_hook_begin_region base) initial).
  Intros.
  assert (Hlength : Zlength initial = 1024) by assumption.
  rewrite task_stack_clear_rep_initial.
  unfold task_stack_storage.
  cbn [os_init_hook_begin_region stackRegionBase stackRegionWords].
  rewrite Hlength.
  rewrite Z.rem_mod_nonneg by lia.
  entailer!.
Qed.

Lemma proof_of_OSInitHookBegin_which_implies_wit_2 : OSInitHookBegin_which_implies_wit_2.
Proof.
  unfold OSInitHookBegin_which_implies_wit_2; left; intros.
  subst pstk.
  assert (Hdone : 0 <= 1024 - size < Zlength initial) by lia.
  assert (Haddr : base + (4 * (1024 - size)) =
      base + ((1024 - size) * sizeof(UINT))).
  { rewrite sizeof_uint; ring. }
  rewrite Haddr.
  unfold os_init_hook_begin_stack_cell_rest.
  sep_apply_l_atomic (task_stack_clear_rep_split_cell
    base initial (1024 - size) Hdone).
  sep_apply_l_atomic (UIntArray.mixedstoreA_to_undefstoreA base
    (1024 - size)
    (Znth (1024 - size) (task_stack_clear_words initial (1024 - size)) None)).
  unfold StoreUIntAsElement.undefstoreA.
  rewrite sizeof_uint.
  entailer!.
Qed.

