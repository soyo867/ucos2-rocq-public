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
From Ucos2Verify.VC.code.flag Require Import flag_create_goal.
From Ucos2Verify.VC.code.flag Require Import flag_create_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.flag.spec.flag_create_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSFlagCreate_return_wit_1 : OSFlagCreate_return_wit_1.
Proof.
  left; intros.
  assert (Hprogram : flag_create_program critical sg invocation bits (LitMap "?")
    before (flag_create_free_head sg entry, 0) current).
  { eapply flag_create_effect_program with (entry := entry)
      (checkpoint := flag_create_checkpoint entry bits (LitMap "?"));
      [exact PreH13 | exact (proj1 PreH2) | exact PreH4 | exact PreH1]. }
  pose proof (flag_create_safe_return critical sg invocation bits (LitMap "?")
    before current (flag_create_free_head sg entry) 0 X Hprogram PreH31) as Hsafe.
  unfold flag_create_api_post; Exists 0 current.
  rewrite PreH28; entailer!.
Qed.

Lemma proof_of_OSFlagCreate_return_wit_2 : OSFlagCreate_return_wit_2.
Proof.
  left; intros.
  assert (Hprogram : flag_create_program critical sg invocation bits (LitMap "?")
    before (0, 114) current).
  { eapply flag_create_effect_program with (entry := entry_2) (checkpoint := entry_2);
      [exact PreH11 | exact (proj1 PreH2) | exact PreH4 | exact PreH1]. }
  pose proof (flag_create_safe_return critical sg invocation bits (LitMap "?")
    before current 0 114 X Hprogram PreH20) as Hsafe.
  unfold flag_create_api_post; Exists 114 current.
  rewrite PreH17; entailer!.
Qed.

Lemma proof_of_OSFlagCreate_return_wit_3 : OSFlagCreate_return_wit_3.
Proof.
  left; intros.
  pose proof (flag_create_program_isr critical sg invocation bits (LitMap "?")
    before PreH2) as Hprogram.
  pose proof (flag_create_safe_return critical sg invocation bits (LitMap "?")
    before before 0 16 X Hprogram PreH11) as Hsafe.
  unfold flag_create_api_post; Exists 16 before.
  rewrite PreH8; entailer!.
Qed.

Lemma proof_of_OSFlagCreate_partial_solve_wit_2_pure : OSFlagCreate_partial_solve_wit_2_pure.
Proof.
  left; intros.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range (&("OSIntNesting")) (flag_create_depth before)).
  Intros.
  match goal with H : 0 <= flag_create_depth before <= Byte.max_unsigned |- _ =>
    change (0 <= flag_create_depth before <= 255) in H end.
  rewrite (IntLib.unsigned_last_nbits_eq (flag_create_depth before) 32) in PreH1
    by (change (0 <= flag_create_depth before < 4294967296); lia).
  entailer!; lia.
Qed.

Lemma proof_of_OSFlagCreate_partial_solve_wit_3_pure : OSFlagCreate_partial_solve_wit_3_pure.
Proof.
  left; intros.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range (&("OSIntNesting")) (flag_create_depth before)).
  Intros.
  match goal with H : 0 <= flag_create_depth before <= Byte.max_unsigned |- _ =>
    change (0 <= flag_create_depth before <= 255) in H end.
  rewrite (IntLib.unsigned_last_nbits_eq (flag_create_depth before) 32) in PreH1
    by (change (0 <= flag_create_depth before < 4294967296); lia).
  entailer!; lia.
Qed.

Lemma proof_of_OSFlagCreate_partial_solve_wit_9_pure : OSFlagCreate_partial_solve_wit_9_pure.
Proof.
  left; intros; entailer!; lia.
Qed.

Lemma proof_of_OSFlagCreate_which_implies_wit_1 : OSFlagCreate_which_implies_wit_1.
Proof.
  right; intros; destruct PreH1 as [Haddr _].
  rewrite Haddr; apply flag_create_interrupt_split.
Qed.

Lemma proof_of_OSFlagCreate_which_implies_wit_2 : OSFlagCreate_which_implies_wit_2.
Proof.
  right; intros; destruct PreH1 as [Haddr _].
  rewrite Haddr; apply flag_create_interrupt_merge.
Qed.

Lemma proof_of_OSFlagCreate_which_implies_wit_3 : OSFlagCreate_which_implies_wit_3.
Proof.
  right; intros; destruct PreH1 as [Haddr _].
  rewrite Haddr; apply flag_create_interrupt_merge.
Qed.

Lemma proof_of_OSFlagCreate_which_implies_wit_4 : OSFlagCreate_which_implies_wit_4.
Proof.
  left; intros.
  pose proof PreH1 as [_ [Hfree _]].
  pose proof (flag_create_pool_split sg entry_2) as Hsplit.
  rewrite <- Hfree in Hsplit.
  sep_apply_l_atomic Hsplit.
  Exists entry_2; entailer!.
Qed.

Lemma proof_of_OSFlagCreate_which_implies_wit_5 : OSFlagCreate_which_implies_wit_5.
Proof.
  left; intros.
  pose proof PreH8 as [Hinterval [Hvalid Hsaved]].
  assert (Hnonempty : flagFree (FlagState entry) <> nil).
  { intros Hempty; apply PreH4; rewrite PreH3.
    unfold flag_create_free_head; rewrite Hempty; reflexivity. }
  destruct (flag_create_nonempty_slot sg entry Hvalid Hnonempty)
    as [id [rest [old Hslot]]].
  pose proof (flag_create_slot_head sg entry id rest old Hslot) as Hhead.
  assert (Hp : pgrp = flag_pool_addr sg id) by congruence.
  assert (Hname : flag_create_default_name entry (LitMap "?")).
  { apply (PreH7 entry); assumption. }
  pose proof PreH5 as [_ [_ [_ [_ [_ [Htype [Hwait [Hbits Hnameaddr]]]]]]]].
  pose proof (flag_create_fields_split sg entry id rest old
    _ _ PreH5 Hslot) as Hsplit.
  rewrite <- Hp in Hsplit.
  Exists rest old id.
  rewrite Htype, Hwait, Hbits, Hnameaddr.
  sep_apply_l_atomic Hsplit; entailer!.
Qed.

Lemma proof_of_OSFlagCreate_which_implies_wit_6 : OSFlagCreate_which_implies_wit_6.
Proof.
  left; intros.
  rewrite (flag_create_literal_split sg entry id old (LitMap "?") PreH1).
  entailer!.
Qed.

Lemma proof_of_OSFlagCreate_which_implies_wit_7 : OSFlagCreate_which_implies_wit_7.
Proof.
  left; intros.
  rewrite (flag_create_literal_merge sg entry id old (LitMap "?") PreH1).
  entailer!.
Qed.

Lemma proof_of_OSFlagCreate_which_implies_wit_8 : OSFlagCreate_which_implies_wit_8.
Proof.
  left; intros; subst pgrp.
  pose proof PreH5 as [_ [Hfree [_ [_ [_ [Htype [Hwait [Hbits Hname]]]]]]]].
  pose proof (flag_create_slot_head sg entry id rest old PreH6) as Hhead.
  pose proof (flag_create_fields_merge_updated sg entry id rest old bits (LitMap "?")
    _ _ PreH5 PreH6 ltac:(lia) PreH7) as Hmerge.
  rewrite <- Hfree, <- Hhead in Hmerge.
  rewrite Htype, Hwait, Hbits, Hname.
  sep_apply_l_atomic Hmerge; Intros; entailer!.
Qed.

Lemma proof_of_OSFlagCreate_which_implies_wit_9 : OSFlagCreate_which_implies_wit_9.
Proof.
  right; intros; destruct PreH1 as [_ [_ Hsaved]].
  unfold mbox_accept_cpu_restore_pre; entailer!.
Qed.

Lemma proof_of_OSFlagCreate_which_implies_wit_10 : OSFlagCreate_which_implies_wit_10.
Proof.
  left; intros.
  assert (Hvalid_view : flag_create_pool_frame sg entry |--
    coq_prop (UCOS2_state_inv sg entry)).
  { unfold flag_create_pool_frame; entailer!. }
  prop_apply_p Hvalid_view; Intros.
  match goal with Hvalid : UCOS2_state_inv sg entry |- _ =>
    pose proof (flag_create_head_zero sg entry _ _ PreH3 Hvalid ltac:(lia)) as Hempty end.
  pose proof (flag_create_empty_effect sg entry bits (LitMap "?") Hempty) as Heffect.
  pose proof PreH3 as [_ [Hfree _]].
  pose proof (flag_create_pool_merge sg entry) as Hmerge.
  rewrite <- Hfree, <- PreH2 in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!; subst pgrp; assumption.
Qed.

Lemma proof_of_OSFlagCreate_which_implies_wit_11 : OSFlagCreate_which_implies_wit_11.
Proof.
  right; intros; destruct PreH1 as [_ [_ Hsaved]].
  unfold mbox_accept_cpu_restore_pre; entailer!.
Qed.

