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
From Ucos2Verify.VC.code.memory Require Import mem_query_goal.
From Ucos2Verify.VC.code.memory Require Import mem_query_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.memory.spec.mem_query_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSMemQuery_return_wit_1 : OSMemQuery_return_wit_1.
Proof.
  left; intros.
  unfold mem_query_restore_post; Intros current.
  match goal with H : mem_query_acquire_facts _ _ _ _ _ _ _ |- _ =>
    rename H into Hacquire end.
  match goal with H : mem_query_selected _ _ _ |- _ =>
    rename H into Himage end.
  match goal with H : critical_region_interval _ _ _ entry current |- _ =>
    rename H into Hrestore end.
  destruct Hacquire as [Hinterval [Hbefore [Hentry [_ Hmask]]]].
  assert (Hprogram : mem_query_program critical sg invocation view pe pd before
    (0, Some (memory_query_snapshot image)) current).
  { eapply mem_query_program_success; eassumption. }
  pose proof (mem_query_api_safe_return critical sg invocation view pe pd
    before current 0 (Some (memory_query_snapshot image)) X Hprogram PreH9) as Hsafe.
  unfold mem_query_api_post.
  Exists (Some (memory_query_snapshot image)) current.
  cbn [mem_query_result_resources].
  rewrite Hmask, mem_query_used_machine_subtraction.
  unfold mem_query_output_rep.
  cbn [memory_query_snapshot nth].
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
Qed. 

Lemma proof_of_OSMemQuery_return_wit_2 : OSMemQuery_return_wit_2.
Proof.
  left; intros.
  subst pmem_pre; subst p_mem_data_pre; subst pd.
  pose proof (mem_query_program_null_output critical sg invocation view pe before PreH2)
    as Hprogram.
  pose proof (mem_query_api_safe_return critical sg invocation view pe 0
    before before 97 None X Hprogram PreH5) as Hsafe.
  unfold mem_query_api_post; Exists (@None (list Z)) before.
  cbn [mem_query_result_resources]; entailer!.
  apply derivable1_truep_intros.
Qed. 

Lemma proof_of_OSMemQuery_return_wit_3 : OSMemQuery_return_wit_3.
Proof.
  left; intros.
  subst pmem_pre; subst p_mem_data_pre; subst pe.
  pose proof (mem_query_program_null_control critical sg invocation view pd before)
    as Hprogram.
  pose proof (mem_query_api_safe_return critical sg invocation view 0 pd
    before before 96 None X Hprogram PreH4) as Hsafe.
  unfold mem_query_api_post; Exists (@None (list Z)) before.
  cbn [mem_query_result_resources]; entailer!.
  apply derivable1_truep_intros.
Qed. 

Lemma proof_of_OSMemQuery_which_implies_wit_1 : OSMemQuery_which_implies_wit_1.
Proof.
  left; intros.
  rewrite (mem_query_copy_frame_split_fields platform critical sg
    invocation origin mask cpu_sr before entry_2 view pe).
  Intros image; Exists entry_2 image; entailer!.
Qed. 

Lemma proof_of_OSMemQuery_which_implies_wit_2 : OSMemQuery_which_implies_wit_2.
Proof.
  left; intros.
  rewrite (mem_query_copy_frame_merge_fields platform critical sg
    invocation origin mask cpu_sr before entry view pe image).
  entailer!.
Qed. 

