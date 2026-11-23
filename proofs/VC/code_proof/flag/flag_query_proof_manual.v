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
From Ucos2Verify.VC.code.flag Require Import flag_query_goal.
From Ucos2Verify.VC.code.flag Require Import flag_query_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.flag.spec.flag_query_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSFlagQuery_return_wit_1 : OSFlagQuery_return_wit_1.
Proof.
  unfold OSFlagQuery_return_wit_1; left; intros.
  pose proof PreH2 as Hadmission.
  destruct Hadmission as [Hz|[Hp [Hlayout [Haddress Hselected]]]]; [contradiction|].
  unfold time_get_restore_post; Intros current.
  destruct PreH7 as [Hacquire [Hvalid [_ Hmask]]].
  assert (Hprogram : flag_query_program critical sg invocation p view before
    (flagImageBits acquired, 0) current).
  { eapply flag_query_program_success; eauto. }
  pose proof (flag_query_safe_return critical sg invocation p view before current
    (flagImageBits acquired) 0 X Hprogram PreH22) as Hreturn.
  rewrite Hmask, PreH20.
  unfold flag_query_api_post; Exists (0 : Z) current.
  rewrite (flag_query_success_resources_equiv platform critical sg invocation origin mask
    p view current before observed Hp Hselected PreH5).
  entailer!.
Qed.

Lemma proof_of_OSFlagQuery_return_wit_2 : OSFlagQuery_return_wit_2.
Proof.
  unfold OSFlagQuery_return_wit_2; left; intros.
  pose proof PreH3 as Hadmission.
  destruct Hadmission as [Hz|[Hp [Hlayout [Haddress Hselected]]]]; [contradiction|].
  pose proof (flag_query_program_wrong_type critical sg invocation p view before observed
    Hp Hselected PreH2) as Hprogram.
  pose proof (flag_query_safe_return critical sg invocation p view before before
    0 1 X Hprogram PreH11) as Hreturn.
  rewrite PreH9; unfold flag_query_api_post; Exists (1 : Z) before; entailer!.
Qed.

Lemma proof_of_OSFlagQuery_return_wit_3 : OSFlagQuery_return_wit_3.
Proof.
  unfold OSFlagQuery_return_wit_3; left; intros.
  assert (Hp : p = 0) by lia; rewrite Hp in *.
  pose proof (flag_query_program_null critical sg invocation view before) as Hprogram.
  pose proof (flag_query_safe_return critical sg invocation 0 view before before
    0 110 X Hprogram PreH5) as Hreturn.
  rewrite PreH3; unfold flag_query_api_post; Exists (110 : Z) before; entailer!.
Qed.

Lemma proof_of_OSFlagQuery_partial_solve_wit_2_pure : OSFlagQuery_partial_solve_wit_2_pure.
Proof.
  unfold OSFlagQuery_partial_solve_wit_2_pure; left; intros.
  prop_apply (UCOS2_C_Rules.store_uchar_range
    (&(p # "os_flag_grp" ->ₛ "OSFlagType")) (flagImageType observed)).
  Intros.
  change (0 <= flagImageType observed <= 255) in H.
  assert (Hpromote : unsigned_last_nbits (flagImageType observed) 32 = flagImageType observed).
  { apply SimpleC.SL.IntLib.unsigned_last_nbits_eq; change (0 <= flagImageType observed < 4294967296); lia. }
  rewrite Hpromote in PreH1; entailer!.
Qed.

Lemma proof_of_OSFlagQuery_partial_solve_wit_3_pure : OSFlagQuery_partial_solve_wit_3_pure.
Proof.
  unfold OSFlagQuery_partial_solve_wit_3_pure; left; intros.
  prop_apply (UCOS2_C_Rules.store_uchar_range
    (&(p # "os_flag_grp" ->ₛ "OSFlagType")) (flagImageType observed)).
  Intros.
  change (0 <= flagImageType observed <= 255) in H.
  assert (Hpromote : unsigned_last_nbits (flagImageType observed) 32 = flagImageType observed).
  { apply SimpleC.SL.IntLib.unsigned_last_nbits_eq; change (0 <= flagImageType observed < 4294967296); lia. }
  rewrite Hpromote in PreH1; entailer!.
Qed.

Lemma proof_of_OSFlagQuery_which_implies_wit_1 : OSFlagQuery_which_implies_wit_1.
Proof.
  unfold OSFlagQuery_which_implies_wit_1; left; intros.
  pose proof PreH2 as Hadmission.
  destruct Hadmission as [Hz|[Hp [[Htype Hflags] [Haddress Hselected]]]]; [contradiction|].
  rewrite Htype.
  sep_apply_l_atomic (flag_query_type_split platform critical sg invocation origin mask
    p view before observed Hp Haddress Hselected).
  entailer!.
Qed.

Lemma proof_of_OSFlagQuery_which_implies_wit_2 : OSFlagQuery_which_implies_wit_2.
Proof.
  unfold OSFlagQuery_which_implies_wit_2; left; intros.
  pose proof PreH3 as Hadmission.
  destruct Hadmission as [Hz|[Hp [[Htype Hflags] [Haddress Hselected]]]]; [contradiction|].
  rewrite Htype.
  sep_apply_l_atomic (flag_query_type_merge platform critical sg invocation origin mask
    p view before observed Hp Haddress Hselected).
  entailer!.
Qed.

Lemma proof_of_OSFlagQuery_which_implies_wit_3 : OSFlagQuery_which_implies_wit_3.
Proof.
  unfold OSFlagQuery_which_implies_wit_3; left; intros.
  pose proof PreH3 as Hadmission.
  destruct Hadmission as [Hz|[Hp [[Htype Hflags] [Haddress Hselected]]]]; [contradiction|].
  rewrite Htype.
  sep_apply_l_atomic (flag_query_type_merge platform critical sg invocation origin mask
    p view before observed Hp Haddress Hselected).
  rewrite (flag_query_success_resources_equiv platform critical sg invocation origin mask
    p view before before observed Hp Hselected PreH2).
  entailer!.
Qed.

Lemma proof_of_OSFlagQuery_which_implies_wit_4 : OSFlagQuery_which_implies_wit_4.
Proof.
  unfold OSFlagQuery_which_implies_wit_4; left; intros.
  pose proof PreH3 as Hadmission.
  destruct Hadmission as [Hz|[Hp [[Htype Hflags] [Haddress Hselected]]]]; [contradiction|].
  pose proof PreH4 as Hacquire.
  destruct Hacquire as [Hinterval [Hvalid Hsaved]].
  destruct (flag_query_acquired_image sg p view entry_2 Haddress Hvalid) as [acquired Hacquired].
  sep_apply_l_atomic (flag_query_flags_split sg p view entry_2 acquired Haddress Hacquired).
  Intros.
  Exists acquired entry_2; rewrite Hflags; entailer!.
Qed.

Lemma proof_of_OSFlagQuery_which_implies_wit_5 : OSFlagQuery_which_implies_wit_5.
Proof.
  unfold OSFlagQuery_which_implies_wit_5; left; intros.
  pose proof PreH2 as Hadmission.
  destruct Hadmission as [Hz|[Hp [[Htype Hflags] [Haddress Hselected]]]]; [contradiction|].
  rewrite Hflags.
  sep_apply_l_atomic (flag_query_flags_merge sg p view entry acquired Haddress PreH3).
  entailer!.
Qed.

