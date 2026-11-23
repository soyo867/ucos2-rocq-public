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
From Ucos2Verify.VC.code.memory Require Import mem_name_set_goal.
From Ucos2Verify.VC.code.memory Require Import mem_name_set_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.memory.spec.mem_name_set_spec.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSMemNameSet_entail_wit_1 : OSMemNameSet_entail_wit_1.
Proof.
  left; intros; subst pmem_pre pname_pre perr_pre.
  destruct (mem_name_set_acquired_resources critical sg invocation pe name view
    before entry_2 PreH14 PreH15 PreH18 PreH17 PreH5 (proj1 PreH1))
    as [Hadmission [[image Himage] Hname]].
  pose proof Hadmission as [Henabled [Hnames [Haddress Haccess]]].
  Exists image entry_2.
  entailer!.
  exact (mem_name_set_source_split_field sg pe view entry_2 image
    Henabled Hnames Haddress Himage).
Qed.

Lemma proof_of_OSMemNameSet_entail_wit_2 : OSMemNameSet_entail_wit_2.
Proof.
  left; intros.
  destruct PreH5 as [Henabled [Hnames [Haddress Haccess]]].
  pose proof (proj1 (proj2 (proj2 PreH6))) as Hvalid.
  assert (Hstep : mem_name_set_step view name entry 0
    (mem_name_set_update view entry image name)).
  { exists image; repeat split; assumption || reflexivity. }
  entailer!.
  exact (mem_name_set_source_merge_updated_field sg pe view entry
    image name Henabled Hnames Hvalid Haddress PreH7 PreH8).
Qed.

Lemma proof_of_OSMemNameSet_return_wit_1 : OSMemNameSet_return_wit_1.
Proof.
  left; intros; subst pmem_pre pname_pre perr_pre.
  sep_apply_r_atomic (mem_name_set_isr_return platform critical sg invocation
    origin mask view pe name error_addr before X caller_frame
    PreH13 PreH14 ltac:(lia) PreH12).
  entailer!.
Qed.

Lemma proof_of_OSMemNameSet_return_wit_2 : OSMemNameSet_return_wit_2.
Proof.
  left; intros; subst pmem_pre pname_pre perr_pre; subst name.
  pose proof (mem_name_set_program_null_name critical sg invocation view pe
    before PreH7) as Hprogram.
  pose proof (mem_name_set_safe_return critical sg invocation view pe 0 before
    12 before X Hprogram PreH6) as Hreturn.
  unfold mem_name_set_api_post; Exists 12 before.
  unfold mem_name_set_return_resources.
  rewrite (proj2 (Z.eqb_neq _ _) PreH7); cbn.
  entailer!.
Qed.

Lemma proof_of_OSMemNameSet_return_wit_3 : OSMemNameSet_return_wit_3.
Proof.
  left; intros; subst pmem_pre pname_pre perr_pre; subst pe.
  pose proof (mem_name_set_program_null_control critical sg invocation view name
    before) as Hprogram.
  pose proof (mem_name_set_safe_return critical sg invocation view 0 name before
    96 before X Hprogram PreH5) as Hreturn.
  unfold mem_name_set_api_post; Exists 96 before.
  unfold mem_name_set_return_resources; cbn.
  entailer!.
Qed.

Lemma proof_of_OSMemNameSet_return_wit_4 : OSMemNameSet_return_wit_4.
Proof.
  left; intros.
  exact (mem_name_set_success_return platform critical sg invocation origin mask
    cpu_sr view pe name error_addr before entry
    (mem_name_set_update view entry image name) X caller_frame
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6).
Qed.

Lemma proof_of_OSMemNameSet_which_implies_wit_1 : OSMemNameSet_which_implies_wit_1.
Proof.
  left; intros.
  unfold mutex_query_closed; Intros.
  sep_apply_l_atomic (task_name_set_observation_split critical sg invocation before).
  Intros.
  unfold mem_name_set_nesting_address in PreH1.
  rewrite <- PreH1.
  entailer!.
Qed.

Lemma proof_of_OSMemNameSet_which_implies_wit_2 : OSMemNameSet_which_implies_wit_2.
Proof.
  left; intros.
  pose proof (task_name_set_observation_merge critical sg invocation before) as Hmerge.
  unfold mem_name_set_nesting_address in PreH1.
  rewrite <- PreH1 in Hmerge.
  unfold mutex_query_closed.
  sep_apply_l_atomic Hmerge.
  entailer!.
Qed.

Lemma proof_of_OSMemNameSet_which_implies_wit_3 : OSMemNameSet_which_implies_wit_3.
Proof.
  left; intros.
  pose proof (task_name_set_observation_merge critical sg invocation before) as Hmerge.
  unfold mem_name_set_nesting_address in PreH1.
  rewrite <- PreH1 in Hmerge.
  unfold mutex_query_closed.
  sep_apply_l_atomic Hmerge.
  entailer!.
Qed.

