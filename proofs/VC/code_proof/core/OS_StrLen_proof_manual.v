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
From Ucos2Verify.VC.code.core Require Import OS_StrLen_goal.
From Ucos2Verify.VC.code.core Require Import OS_StrLen_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.core.spec.os_strlen_spec.
Local Open Scope Z_scope.
Local Open Scope sac.
Import UCOS2_C_Rules.
Local Open Scope sac.

Import ListNotations.

Lemma proof_of_OS_StrLen_entail_wit_1 : OS_StrLen_entail_wit_1.
Proof.
  unfold OS_StrLen_entail_wit_1.
  left; intros.
  pre_process.
  entailer!.
  - subst base_exact_frame_spec.
    change (sizeof(UCHAR)) with 1 in *.
    rewrite Z.mul_1_r in *.
    replace (psrc_pre + - psrc_pre) with 0 by ring.
    unfold os_strlen_bytes, os_strlen_source, os_strlen_loop_residual.
    sep_apply (UCharArray.full_split_to_seg psrc_pre 1
      (Z.of_nat (S (List.length chars_exact_frame_spec))) (chars_exact_frame_spec ++ [0]) ltac:(lia)).
    replace 1 with (0 + 1) by lia.
    rewrite (@sublist_single Z 0 0 (chars_exact_frame_spec ++ [0])).
    change (sublist 0 0 chars_exact_frame_spec) with (@nil Z).
    rewrite UCharArray.seg_empty.
    all: try lia.
    unfold UCharArray.seg.
    simpl.
    replace (psrc_pre + 0) with psrc_pre by lia.
    entailer!.
    change (0 <= 0 < Zlength (chars_exact_frame_spec ++ [0])).
    rewrite Zlength_app_cons.
    simpl.
    pose proof (Zlength_nonneg chars_exact_frame_spec) as Hnonneg.
    lia.
  - subst base_exact_frame_spec.
    change (sizeof(UCHAR)) with 1 in *.
    rewrite Z.mul_1_r in *.
    replace (psrc_pre + - psrc_pre) with 0 by ring.
    unfold kernel_u8.
    entailer!.
  - subst base_exact_frame_spec.
    change (sizeof(UCHAR)) with 1 in *.
    rewrite Z.mul_1_r in *.
    replace (psrc_pre + - psrc_pre) with 0 by ring.
    pose proof (Zlength_nonneg chars_exact_frame_spec) as Hnonneg.
    entailer!.
  - subst base_exact_frame_spec.
    change (sizeof(UCHAR)) with 1 in *.
    rewrite Z.mul_1_r in *.
    replace (psrc_pre + - psrc_pre) with 0 by ring.
    entailer!.
  - subst base_exact_frame_spec; exact PreH5.
Qed.

Lemma proof_of_OS_StrLen_entail_wit_2 : OS_StrLen_entail_wit_2.
Proof.
  unfold OS_StrLen_entail_wit_2.
  right; intros.
  repeat apply _derivable1_andp_intros.
  {

  change (sizeof(UCHAR)) with 1 in *.
  rewrite Z.mul_1_r in *.
  replace (psrc + 1 + - base_exact_frame_spec) with ((psrc - base_exact_frame_spec) + 1) by ring.
  replace (psrc + - base_exact_frame_spec) with (psrc - base_exact_frame_spec) in * by ring.
  unfold kernel_u8 in PreH7.
  unfold unsigned_last_nbits, kernel_u8.
  entailer!.
  replace (2 ^ 8)%Z with 256 by reflexivity.
  replace (psrc + 1 * 1 + - base_exact_frame_spec) with ((psrc - base_exact_frame_spec) + 1) by ring.
  rewrite PreH7.
  rewrite Z.add_mod_idemp_l by lia.
  reflexivity.

  }
  {

  change (sizeof(UCHAR)) with 1 in *.
  rewrite Z.mul_1_r in *.
  replace (psrc + 1 + - base_exact_frame_spec) with ((psrc - base_exact_frame_spec) + 1) by ring.
  replace (psrc + - base_exact_frame_spec) with (psrc - base_exact_frame_spec) in * by ring.
  assert (Hbefore : psrc - base_exact_frame_spec < Zlength chars_exact_frame_spec).
  { destruct (Z.eq_dec (psrc - base_exact_frame_spec) (Zlength chars_exact_frame_spec)) as [Heq|Hneq].
    - assert (Hterm := PreH1).
      replace (psrc + (-base_exact_frame_spec) * sizeof(UCHAR)) with (psrc - base_exact_frame_spec) in Hterm by
        (change (sizeof(UCHAR)) with 1; ring).
      unfold os_strlen_source in Hterm.
      rewrite Heq in Hterm.
      rewrite (app_Znth2 0 chars_exact_frame_spec [0] (Zlength chars_exact_frame_spec)) in Hterm by lia.
      replace (Zlength chars_exact_frame_spec - Zlength chars_exact_frame_spec) with 0 in Hterm by lia.
      change (0 <> 0) in Hterm; contradiction.
    - lia. }
  replace (psrc + 1 * 1 + - base_exact_frame_spec) with ((psrc - base_exact_frame_spec) + 1) by ring.
  entailer!.

  }
  {

  change (sizeof(UCHAR)) with 1 in *.
  rewrite Z.mul_1_r in *.
  replace (psrc + - base_exact_frame_spec) with (psrc - base_exact_frame_spec) in * by ring.
  assert (Hbefore : psrc - base_exact_frame_spec < Zlength chars_exact_frame_spec).
  { destruct (Z.eq_dec (psrc - base_exact_frame_spec) (Zlength chars_exact_frame_spec)) as [Heq|Hneq].
    - assert (Hterm := PreH1).
      replace (psrc + (-base_exact_frame_spec) * sizeof(UCHAR)) with (psrc - base_exact_frame_spec) in Hterm by
        (change (sizeof(UCHAR)) with 1; ring).
      unfold os_strlen_source in Hterm.
      rewrite Heq in Hterm.
      rewrite (app_Znth2 0 chars_exact_frame_spec [0] (Zlength chars_exact_frame_spec)) in Hterm by lia.
      replace (Zlength chars_exact_frame_spec - Zlength chars_exact_frame_spec) with 0 in Hterm by lia.
      change (0 <> 0) in Hterm; contradiction.
    - lia. }
  assert (Hi : 0 <= psrc - base_exact_frame_spec < Zlength chars_exact_frame_spec) by lia.
  assert (Hbyte : Znth (psrc - base_exact_frame_spec) (chars_exact_frame_spec ++ [0]) 0 =
      Znth (psrc - base_exact_frame_spec) chars_exact_frame_spec 0).
  { rewrite app_Znth1 by exact Hi; reflexivity. }
  replace psrc with (base_exact_frame_spec + (psrc - base_exact_frame_spec)) by ring.
  replace (base_exact_frame_spec + (psrc - base_exact_frame_spec) - base_exact_frame_spec) with (psrc - base_exact_frame_spec) by ring.
  unfold os_strlen_source.
  rewrite Hbyte.
  replace (base_exact_frame_spec + (psrc - base_exact_frame_spec)) with
    (base_exact_frame_spec + (psrc - base_exact_frame_spec) * sizeof(UCHAR)) by
      (change (sizeof(UCHAR)) with 1; ring).
  unfold os_strlen_loop_residual.
  sep_apply (UCharArray.seg_single base_exact_frame_spec (psrc - base_exact_frame_spec)
    (Znth (psrc - base_exact_frame_spec) chars_exact_frame_spec 0)).
  Intros.
  sep_apply os_strlen_seg_merge_reverse.
  all: try lia.
  entailer!.
  assert (Htotal : Z.of_nat (S (length chars_exact_frame_spec)) = Zlength (chars_exact_frame_spec ++ [0])).
  { rewrite Zlength_app_cons, Zlength_correct; lia. }
  rewrite Htotal.
  assert (Hlenplus : Zlength (chars_exact_frame_spec ++ [0]) = Zlength chars_exact_frame_spec + 1).
  { apply Zlength_app_cons. }
  assert (Hbound : psrc - base_exact_frame_spec + 2 <= Zlength (chars_exact_frame_spec ++ [0])).
  { rewrite Hlenplus; lia. }
  assert (Htail :
      sublist (psrc - base_exact_frame_spec + 1) (Zlength (chars_exact_frame_spec ++ [0])) (chars_exact_frame_spec ++ [0]) =
      [Znth (psrc - base_exact_frame_spec + 1) (chars_exact_frame_spec ++ [0]) 0] ++
    sublist (psrc - base_exact_frame_spec + 2) (Zlength (chars_exact_frame_spec ++ [0])) (chars_exact_frame_spec ++ [0])).
  { pose proof (sublist_split (psrc - base_exact_frame_spec + 1)
        (Zlength (chars_exact_frame_spec ++ [0])) (psrc - base_exact_frame_spec + 2) (chars_exact_frame_spec ++ [0])
        ltac:(lia)
        ltac:(split; [exact Hbound|lia])) as Hsplit.
    rewrite Hsplit.
    replace (psrc - base_exact_frame_spec + 2) with ((psrc - base_exact_frame_spec + 1) + 1) in * by lia.
    rewrite (sublist_single 0) by
      (try rewrite (Zlength_app_cons chars_exact_frame_spec 0);
       try rewrite Zlength_correct; lia).
    reflexivity. }
  rewrite Htail.
  rewrite (UCharArray.seg_unfold base_exact_frame_spec (psrc - base_exact_frame_spec + 1)
    (Zlength (chars_exact_frame_spec ++ [0]))
    (sublist (psrc - base_exact_frame_spec + 2) (Zlength (chars_exact_frame_spec ++ [0])) (chars_exact_frame_spec ++ [0]))
    (Znth (psrc - base_exact_frame_spec + 1) (chars_exact_frame_spec ++ [0]) 0)).
  replace (base_exact_frame_spec + (psrc - base_exact_frame_spec) * sizeof(UCHAR) + 1 * 1)
    with (base_exact_frame_spec + (psrc - base_exact_frame_spec + 1) * sizeof(UCHAR)) by
      (change (sizeof(UCHAR)) with 1; ring).
  replace (base_exact_frame_spec + (psrc - base_exact_frame_spec + 1) * sizeof(UCHAR) - base_exact_frame_spec)
    with (psrc - base_exact_frame_spec + 1) by
      (change (sizeof(UCHAR)) with 1; ring).
  replace (base_exact_frame_spec + (psrc - base_exact_frame_spec + 1) * sizeof(UCHAR) + - base_exact_frame_spec)
    with (psrc - base_exact_frame_spec + 1) in * by
      (change (sizeof(UCHAR)) with 1; ring).
  assert (Hprefix :
      sublist 0 (psrc - base_exact_frame_spec + 1) chars_exact_frame_spec =
      sublist 0 (psrc - base_exact_frame_spec) chars_exact_frame_spec ++ [Znth (psrc - base_exact_frame_spec) chars_exact_frame_spec 0]).
  { rewrite (sublist_split 0 (psrc - base_exact_frame_spec + 1) (psrc - base_exact_frame_spec) chars_exact_frame_spec)
      by lia.
    rewrite (sublist_single 0) by exact Hi.
    reflexivity. }
  rewrite Hprefix.
  replace (psrc - base_exact_frame_spec + 1 + 1) with (psrc - base_exact_frame_spec + 2) in * by lia.
  entailer!.

  }
Qed.

Lemma proof_of_OS_StrLen_return_wit_1 : OS_StrLen_return_wit_1.
Proof.
  unfold OS_StrLen_return_wit_1.
  right; intros.
  change (sizeof(UCHAR)) with 1 in *.
  repeat rewrite Z.mul_1_r in *.
  replace (psrc + - base_exact_frame_spec) with (psrc - base_exact_frame_spec) in * by ring.
  pureIntros.
  assert (Hend : psrc - base_exact_frame_spec = Zlength chars_exact_frame_spec).
  { eapply os_strlen_source_zero_end; [exact PreH4|lia|rewrite PreH1; reflexivity]. }
  rewrite Hend in *.
  subst entry_exact_frame_spec.
  assert (Hcursor : psrc = base_exact_frame_spec + Zlength chars_exact_frame_spec) by lia.
  rewrite Hcursor.
  unfold os_strlen_loop_residual, os_strlen_source, os_strlen_result.
  assert (Htotal : Z.of_nat (S (length chars_exact_frame_spec)) = Zlength chars_exact_frame_spec + 1)
    by (rewrite Zlength_correct; lia).
  rewrite Htotal.
  rewrite (sublist_self chars_exact_frame_spec (Zlength chars_exact_frame_spec) eq_refl).
  assert (Htail : sublist (Zlength chars_exact_frame_spec + 1) (Zlength chars_exact_frame_spec + 1)
      (chars_exact_frame_spec ++ [0]) = []).
  { apply Zsublist_nil; lia. }
  rewrite Htail.
  rewrite UCharArray.seg_empty.
  rewrite (app_Znth2 0 chars_exact_frame_spec [0] (Zlength chars_exact_frame_spec)) by lia.
  rewrite Z.sub_diag.
  change (Znth 0 [0] 0) with 0.
  replace (base_exact_frame_spec + Zlength chars_exact_frame_spec) with
      (base_exact_frame_spec + Zlength chars_exact_frame_spec * sizeof(UCHAR)) by
        (change (sizeof(UCHAR)) with 1; ring).
  pureIntros.
  sep_apply_l_atomic (UCharArray.seg_single base_exact_frame_spec (Zlength chars_exact_frame_spec) 0).
  sep_apply_l_atomic
    (os_strlen_seg_merge_reverse base_exact_frame_spec 0 (Zlength chars_exact_frame_spec)
      (Zlength chars_exact_frame_spec + 1) chars_exact_frame_spec [0] ltac:(lia)).
  sep_apply (UCharArray.seg_to_full base_exact_frame_spec 0 (Zlength chars_exact_frame_spec + 1)
    (chars_exact_frame_spec ++ [0])).
  entailer!.
  - unfold os_strlen_bytes.
    replace (base_exact_frame_spec + 0 * sizeof(UCHAR)) with base_exact_frame_spec by
      (change (sizeof(UCHAR)) with 1; ring).
    replace (Zlength chars_exact_frame_spec + 1 - 0) with (Zlength chars_exact_frame_spec + 1) by lia.
    replace (Z.of_nat (S (length chars_exact_frame_spec))) with (Zlength chars_exact_frame_spec + 1)
      by (symmetry; exact Htotal).
    entailer!.
  - unfold name_length_result.
    rewrite <- Zlength_correct.
    exact PreH7.
Qed.

Lemma proof_of_OS_StrLen_derive_no_wrap_spec_by_source_spec : OS_StrLen_derive_no_wrap_spec_by_source_spec.
Proof.
  unfold OS_StrLen_derive_no_wrap_spec_by_source_spec.
  intros.
  assert (Htt : (TT) ** (TT) |-- (TT)) by apply derivable1_truep_intros.
  apply derivable1_orp_elim; Intros.
  1: Exists entry_no_wrap_spec base_no_wrap_spec names_no_wrap_spec chars_no_wrap_spec
    (coq_prop (os_strlen_length_valid chars_no_wrap_spec) ** frame_no_wrap_spec).
  2: Exists entry_no_wrap_spec base_no_wrap_spec names_no_wrap_spec chars_no_wrap_spec frame_no_wrap_spec.
  all: match goal with |- _ |-- ?P ** (?Q -* ?R) =>
    assert (Hwand : emp |-- Q -* R)
  end.
  1,3: (apply_sepcon_adjoint; pre_process;
    apply derivable1_orp_elim; Intros retval;
    [Left | Right];
    Exists retval; unfold os_strlen_success, os_strlen_result in *;
    pureIntros; try sep_apply_l_atomic Htt; entailer!).
  all: sep_apply_r_atomic Hwand.
  - Left; entailer!.
  - Right; entailer!.
Qed.

Lemma proof_of_OS_StrLen_derive_source_spec_by_exact_frame_spec :
  OS_StrLen_derive_source_spec_by_exact_frame_spec.
Proof.
  unfold OS_StrLen_derive_source_spec_by_exact_frame_spec.
  intros.
  apply derivable1_orp_elim; Intros.
  (* The old non-NULL precondition owns a separate pure carrier.  Lend its
     heap as part of the exact-frame contract's frame, then retag that same
     returned carrier with the result fact.  The original frame is intact. *)
  1: Exists entry_source_spec base_source_spec names_source_spec chars_source_spec
    ((TT) ** frame_source_spec).
  2: Exists entry_source_spec base_source_spec names_source_spec chars_source_spec frame_source_spec.
  all: match goal with |- _ |-- ?P ** (?Q -* ?R) =>
    assert (Hwand : emp |-- Q -* R)
  end.
  1,3: (apply_sepcon_adjoint; pre_process;
    apply derivable1_orp_elim; Intros retval;
    [Left | Right];
    Exists retval; pureIntros; entailer!).
  all: sep_apply_r_atomic Hwand.
  - Left; entailer!.
  - Right; entailer!.
Qed.
