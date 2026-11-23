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
From Ucos2Verify.VC.code.memory Require Import mem_put_goal.
From Ucos2Verify.VC.code.memory Require Import mem_put_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.memory.spec.mem_put_spec.
Import UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OSMemPut_return_wit_1 : OSMemPut_return_wit_1.
Proof.
  unfold OSMemPut_return_wit_1; left; intros.
  destruct PreH2 as [Hpmem [Hpblk [Hacquire [Hprotected Hcode]]]].
  assert (Hprogram : mem_put_program critical sg invocation pmem_pre pblk_pre input before
    (mem_put_raw_result pmem_pre pblk_pre (mem_put_acquired_image acquired)) after).
  { unfold mem_put_program.
    rewrite (proj2 (Z.eqb_neq pmem_pre 0) Hpmem),
      (proj2 (Z.eqb_neq pblk_pre 0) Hpblk); simpl.
    exists entry, acquired, (mem_put_checkpoint entry input acquired); auto. }
  pose proof (mem_put_program_safe_return critical sg invocation pmem_pre pblk_pre input before
    (mem_put_raw_result pmem_pre pblk_pre (mem_put_acquired_image acquired)) after X
    PreH22 Hprogram) as Hreturn.
  unfold mem_put_api_post.
  Exists (mem_put_raw_result pmem_pre pblk_pre (mem_put_acquired_image acquired)) after.
  entailer!.
Qed.

Lemma proof_of_OSMemPut_return_wit_2 : OSMemPut_return_wit_2.
Proof.
  unfold OSMemPut_return_wit_2; left; intros.
  destruct PreH2 as [Hpmem [Hpblk [Hacquire [Hprotected Hcode]]]].
  assert (Hprogram : mem_put_program critical sg invocation pmem_pre pblk_pre input before
    (mem_put_raw_result pmem_pre pblk_pre (mem_put_acquired_image acquired)) after).
  { unfold mem_put_program.
    rewrite (proj2 (Z.eqb_neq pmem_pre 0) Hpmem),
      (proj2 (Z.eqb_neq pblk_pre 0) Hpblk); simpl.
    exists entry, acquired, entry; auto. }
  pose proof (mem_put_program_safe_return critical sg invocation pmem_pre pblk_pre input before
    (mem_put_raw_result pmem_pre pblk_pre (mem_put_acquired_image acquired)) after X
    PreH19 Hprogram) as Hreturn.
  unfold mem_put_api_post.
  Exists (mem_put_raw_result pmem_pre pblk_pre (mem_put_acquired_image acquired)) after.
  entailer!.
Qed.

Lemma proof_of_OSMemPut_return_wit_3 : OSMemPut_return_wit_3.
Proof.
  unfold OSMemPut_return_wit_3; left; intros; subst pblk_pre.
  assert (Ep : Z.eqb pmem_pre 0 = false) by (apply Z.eqb_neq; exact PreH2).
  assert (Hprogram : mem_put_program critical sg invocation pmem_pre 0 input before
    (mem_put_raw_result pmem_pre 0 (mem_put_input_image input)) before).
  { unfold mem_put_program; rewrite Ep; simpl; auto. }
  pose proof (mem_put_program_safe_return critical sg invocation pmem_pre 0 input before
    (mem_put_raw_result pmem_pre 0 (mem_put_input_image input)) before X PreH5 Hprogram) as Hreturn.
  pose proof (proj1 (mem_put_raw_null_block pmem_pre (mem_put_input_image input) PreH2)) as Hcode.
  unfold mem_put_api_post.
  Exists (mem_put_raw_result pmem_pre 0 (mem_put_input_image input)) before.
  unfold mem_put_input_resources, mem_put_result_resources; rewrite Ep; simpl.
  entailer!.
Qed.

Lemma proof_of_OSMemPut_return_wit_4 : OSMemPut_return_wit_4.
Proof.
  unfold OSMemPut_return_wit_4; left; intros; subst pmem_pre.
  assert (Hprogram : mem_put_program critical sg invocation 0 pblk_pre input before
    (mem_put_raw_result 0 pblk_pre (mem_put_input_image input)) before).
  { unfold mem_put_program; simpl; auto. }
  pose proof (mem_put_program_safe_return critical sg invocation 0 pblk_pre input before
    (mem_put_raw_result 0 pblk_pre (mem_put_input_image input)) before X PreH4 Hprogram) as Hreturn.
  pose proof (proj1 (mem_put_raw_null_control pblk_pre (mem_put_input_image input))) as Hcode.
  unfold mem_put_api_post.
  Exists (mem_put_raw_result 0 pblk_pre (mem_put_input_image input)) before.
  unfold mem_put_input_resources, mem_put_result_resources; simpl.
  entailer!.
Qed.

Lemma proof_of_OSMemPut_which_implies_wit_1 : OSMemPut_which_implies_wit_1.
Proof.
  unfold OSMemPut_which_implies_wit_1; left; intros.
  unfold mutex_query_closed; entailer!.
Qed.

Lemma proof_of_OSMemPut_which_implies_wit_2 : OSMemPut_which_implies_wit_2.
Proof.
  unfold OSMemPut_which_implies_wit_2; left; intros.
  rewrite (mem_put_acquire_count_cells critical sg invocation before entry pmem pblk input
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7).
  Intros acquired; Exists acquired; unfold mem_put_count_cells; entailer!.
Qed.

Lemma proof_of_OSMemPut_which_implies_wit_4 : OSMemPut_which_implies_wit_4.
Proof.
  unfold OSMemPut_which_implies_wit_4; left; intros.
  pose proof PreH2 as Hfacts.
  destruct Hfacts as [Hpmem [Hpblk [Hentry Hrest]]].
  assert (Hfull : memImageCount (mem_put_acquired_image acquired) <=
    memImageNFree (mem_put_acquired_image acquired)) by lia.
  pose proof (mem_put_acquired_completed critical sg invocation before entry pmem pblk input acquired
    PreH2) as Hcompleted.
  pose proof (proj1 (mem_put_raw_full pmem pblk (mem_put_acquired_image acquired)
    Hpmem Hpblk Hfull)) as Hcode.
  assert (Hcheckpoint : mem_put_checkpoint entry input acquired = entry).
  { unfold mem_put_checkpoint.
    rewrite (proj2 (Z.leb_le _ _) Hfull); reflexivity. }
  rewrite Hcode, Hcheckpoint in Hcompleted.
  pose proof (mem_put_full_reconstructs_resources critical sg invocation before entry pmem pblk input
    acquired PreH1 PreH2 Hfull) as Hmerge.
  unfold mem_put_count_cells in Hmerge; rewrite Hmerge; entailer!.
Qed.

Lemma proof_of_OSMemPut_which_implies_wit_5 : OSMemPut_which_implies_wit_5.
Proof.
  unfold OSMemPut_which_implies_wit_5; left; intros.
  unfold mbox_accept_cpu_restore_pre; entailer!.
Qed.

Lemma proof_of_OSMemPut_which_implies_wit_6 : OSMemPut_which_implies_wit_6.
Proof.
  unfold OSMemPut_which_implies_wit_6; left; intros.
  rewrite (mem_put_focus_success_word critical sg invocation before entry pmem pblk input acquired
    PreH1 PreH2).
  Intros first; Exists first; entailer!.
Qed.

Lemma proof_of_OSMemPut_which_implies_wit_7 : OSMemPut_which_implies_wit_7.
Proof.
  unfold OSMemPut_which_implies_wit_7; left; intros.
  pose proof PreH2 as Hfacts.
  destruct Hfacts as [Hpmem [Hpblk Hrest]].
  pose proof (mem_put_acquired_completed critical sg invocation before entry pmem pblk input acquired
    PreH2) as Hcompleted.
  pose proof (proj1 (mem_put_raw_success pmem pblk (mem_put_acquired_image acquired)
    Hpmem Hpblk PreH5)) as Hcode.
  rewrite Hcode in Hcompleted.
  rewrite (mem_put_success_reconstructs_resources critical sg invocation before entry pmem pblk input
    acquired PreH1 PreH2 PreH3 PreH4 PreH5 PreH6).
  entailer!.
Qed.

Lemma proof_of_OSMemPut_which_implies_wit_8 : OSMemPut_which_implies_wit_8.
Proof.
  unfold OSMemPut_which_implies_wit_8; left; intros.
  unfold mbox_accept_cpu_restore_pre; entailer!.
Qed.

