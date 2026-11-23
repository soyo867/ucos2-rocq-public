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
From Ucos2Verify.VC.code.memory Require Import mem_name_get_goal.
From Ucos2Verify.VC.code.memory Require Import mem_name_get_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.memory.spec.mem_name_get_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSMemNameGet_entail_wit_1 : OSMemNameGet_entail_wit_1.
Proof.
  left; intros.
  subst pmem_pre pname_pre perr_pre.
  rewrite unsigned_last_nbits_eq in PreH4 by (change (0 <= task_name_get_nesting before < 4294967296); lia).
  assert (Hnest : task_name_get_nesting before = 0) by lia.
  assert (Herror : mem_name_get_early_error pe pn (task_name_get_nesting before) = None).
  { unfold mem_name_get_early_error; rewrite Hnest.
    rewrite (proj2 (Z.eqb_neq pe 0) PreH8), (proj2 (Z.eqb_neq pn 0) PreH7).
    reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSMemNameGet_return_wit_1 : OSMemNameGet_return_wit_1.
Proof.
  left; intros.
  unfold mem_query_restore_post; Intros current.
  destruct PreH1 as [Hacquire [Hbefore [Hacquired [Hsaved Hmask]]]].
  rewrite Hmask.
  assert (Heffect : mem_name_get_effect critical sg invocation pe pn view raw raw_chars
    before acquired current retval 0 (Some (memImageName image))).
  { unfold mem_name_get_effect; rewrite PreH15.
    split; [exact Hacquire|]. split; [assumption|].
    exists image, chars; auto. }
  pose proof (mem_name_get_safe_return critical sg invocation pe pn view raw raw_chars
    before acquired current retval 0 (Some (memImageName image)) X Heffect PreH18) as Hsafe.
  unfold mem_name_get_post; Exists acquired current 0 (Some (memImageName image)).
  unfold mem_name_get_guarded_source; rewrite PreH15.
  cbn [task_name_get_output_cell]; entailer!.
Qed.

Lemma proof_of_OSMemNameGet_return_wit_2 : OSMemNameGet_return_wit_2.
Proof.
  left; intros.
  assert (Hpe : pe <> 0) by congruence.
  assert (Hpn : pn <> 0) by congruence.
  rewrite unsigned_last_nbits_eq in PreH4 by (change (0 <= task_name_get_nesting before < 4294967296); lia).
  assert (Herror : mem_name_get_early_error pe pn (task_name_get_nesting before) = Some 17).
  { unfold mem_name_get_early_error.
    rewrite (proj2 (Z.eqb_neq pe 0) Hpe), (proj2 (Z.eqb_neq pn 0) Hpn).
    rewrite (proj2 (Z.ltb_lt 0 (task_name_get_nesting before)) ltac:(lia)); reflexivity. }
  assert (Heffect : mem_name_get_effect critical sg invocation pe pn view raw raw_chars
    before before before 0 17 None).
  { unfold mem_name_get_effect; rewrite Herror; auto. }
  pose proof (mem_name_get_safe_return critical sg invocation pe pn view raw raw_chars
    before before before 0 17 None X Heffect PreH14) as Hsafe.
  unfold mem_name_get_post; Exists before before 17 (@None Z); entailer!.
Qed.

Lemma proof_of_OSMemNameGet_return_wit_3 : OSMemNameGet_return_wit_3.
Proof.
  left; intros.
  assert (Hpe : pe <> 0) by congruence.
  assert (Hpn : pn = 0) by congruence.
  assert (Herror : mem_name_get_early_error pe pn (task_name_get_nesting before) = Some 12).
  { unfold mem_name_get_early_error.
    rewrite (proj2 (Z.eqb_neq pe 0) Hpe), Hpn; reflexivity. }
  assert (Heffect : mem_name_get_effect critical sg invocation pe pn view raw raw_chars
    before before before 0 12 None).
  { unfold mem_name_get_effect; rewrite Herror; auto. }
  pose proof (mem_name_get_safe_return critical sg invocation pe pn view raw raw_chars
    before before before 0 12 None X Heffect PreH8) as Hsafe.
  unfold mem_name_get_post; Exists before before 12 (@None Z); entailer!.
Qed.

Lemma proof_of_OSMemNameGet_return_wit_4 : OSMemNameGet_return_wit_4.
Proof.
  left; intros.
  assert (Hpe : pe = 0) by congruence.
  assert (Herror : mem_name_get_early_error pe pn (task_name_get_nesting before) = Some 96).
  { unfold mem_name_get_early_error; rewrite Hpe; reflexivity. }
  assert (Heffect : mem_name_get_effect critical sg invocation pe pn view raw raw_chars
    before before before 0 96 None).
  { unfold mem_name_get_effect; rewrite Herror; auto. }
  pose proof (mem_name_get_safe_return critical sg invocation pe pn view raw raw_chars
    before before before 0 96 None X Heffect PreH7) as Hsafe.
  unfold mem_name_get_post; Exists before before 96 (@None Z); entailer!.
Qed.

Lemma proof_of_OSMemNameGet_which_implies_wit_1 : OSMemNameGet_which_implies_wit_1.
Proof.
  left; intros; unfold mem_name_get_pre; entailer!.
Qed.

Lemma proof_of_OSMemNameGet_which_implies_wit_2 : OSMemNameGet_which_implies_wit_2.
Proof.
  left; intros.
  rewrite mutex_query_closed_equiv; unfold UCOS2_inv; Intros.
  rewrite task_name_get_raw_rep_split_nesting__resource_stages_strlen.
  unfold mem_name_get_addresses in PreH1; rewrite PreH1; entailer!.
Qed.

Lemma proof_of_OSMemNameGet_which_implies_wit_3 : OSMemNameGet_which_implies_wit_3.
Proof.
  left; intros.
  pose proof (store_uchar_with_range__resource_stages_strlen
    (g_OSIntNesting sg) (task_name_get_nesting before)) as Hrange.
  unfold mem_name_get_addresses in PreH1; rewrite PreH1 in Hrange.
  sep_apply_l_atomic Hrange.
  Intros.
  rewrite mutex_query_closed_equiv; unfold UCOS2_inv.
  rewrite task_name_get_raw_rep_split_nesting__resource_stages_strlen.
  rewrite PreH1; entailer!.
Qed.

Lemma proof_of_OSMemNameGet_which_implies_wit_4 : OSMemNameGet_which_implies_wit_4.
Proof.
  exact proof_of_OSMemNameGet_which_implies_wit_3.
Qed.

Lemma proof_of_OSMemNameGet_which_implies_wit_5 : OSMemNameGet_which_implies_wit_5.
Proof.
  left; intros.
  destruct (PreH1 PreH2) as [Hadmission [previous Hold]].
  unfold task_name_get_output_cell, mem_name_get_guarded_source; rewrite Hold, PreH2.
  Exists previous; entailer!.
Qed.

Lemma proof_of_OSMemNameGet_which_implies_wit_6 : OSMemNameGet_which_implies_wit_6.
Proof.
  left; intros raw_chars raw view pe before mask invocation sg critical acquired cpu_sr
    Hacquire Hadmission.
  destruct Hacquire as [Hinterval [Hbefore [Hacquired Hsaved]]].
  destruct (mem_name_get_acquired_selection critical sg invocation pe view raw raw_chars
    before acquired Hadmission Hbefore Hacquired Hinterval) as [image [chars Hselected]].
  Exists image chars.
  pose proof Hadmission as [[Henabled [Hnames [Haddress Haccess]]] Hraw].
  pose proof (mem_name_get_control_split sg pe view acquired image Henabled Hnames
    Haddress (proj1 Hselected)) as Hsplit.
  cbn [memory_control_cell] in Hsplit.
  unfold mem_name_get_source.
  sep_apply_l_atomic Hsplit.
  entailer!.
  unfold mem_query_acquire_facts; auto.
Qed.

Lemma proof_of_OSMemNameGet_which_implies_wit_7 : OSMemNameGet_which_implies_wit_7.
Proof.
  left; intros raw_chars raw view pe before invocation sg critical acquired image chars
    Hadmission Hselected.
  pose proof Hadmission as [[Henabled [Hnames [Haddress Haccess]]] Hraw].
  pose proof (mem_name_get_control_merge sg pe view acquired image Henabled Hnames
    Haddress (proj1 Hselected)) as Hmerge.
  cbn [memory_control_cell] in Hmerge.
  unfold mem_name_get_source.
  rewrite Hmerge.
  entailer!.
Qed.

Lemma proof_of_OSMemNameGet_which_implies_wit_8 : OSMemNameGet_which_implies_wit_8.
Proof.
  left; intros raw_chars raw view pe before mask invocation sg critical acquired image chars
    cpu_sr Hacquire Hselected.
  pose proof (proj1 (proj2 (proj2 Hacquire))) as Hacquired.
  pose proof (proj2 (proj2 Hselected)) as Hread.
  rewrite (mem_name_get_string_split sg pe view raw raw_chars acquired image chars
    Hacquired Hselected).
  entailer!.
Qed.

Lemma proof_of_OSMemNameGet_which_implies_wit_9 : OSMemNameGet_which_implies_wit_9.
Proof.
  left; intros; unfold mem_name_get_call_frame; entailer!.
Qed.

Lemma proof_of_OSMemNameGet_which_implies_wit_10 : OSMemNameGet_which_implies_wit_10.
Proof.
  left; intros; unfold mem_name_get_call_frame; entailer!.
Qed.

Lemma proof_of_OSMemNameGet_which_implies_wit_11 : OSMemNameGet_which_implies_wit_11.
Proof.
  left; intros raw_chars raw view pe before mask invocation sg critical acquired image chars
    cpu_sr Hacquire Hselected.
  pose proof (proj1 (proj2 (proj2 Hacquire))) as Hacquired.
  rewrite (mem_name_get_string_merge sg pe view raw raw_chars acquired image chars
    Hacquired Hselected).
  entailer!.
Qed.

Lemma proof_of_OS_StrLen_derive_mem_name_get_spec_by_source_spec : OS_StrLen_derive_mem_name_get_spec_by_source_spec.
Proof.
  exact mem_name_get_strlen_source_consequence.
Qed.

