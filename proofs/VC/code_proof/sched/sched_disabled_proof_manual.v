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
From Ucos2Verify.VC.code.sched Require Import sched_disabled_goal.
From Ucos2Verify.VC.code.sched Require Import sched_disabled_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_disabled_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OS_Sched_entail_wit_1 : OS_Sched_entail_wit_1.
Proof.
  unfold OS_Sched_entail_wit_1; left.
  intros before mask view sg critical platform external acquired_2 retval
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6.
  destruct (sched_disabled_interval_preserves_context critical sg view
    (os_execution_invocation view) before acquired_2 PreH4 PreH5 PreH1)
    as [Hacquired Hrely].
  pose proof (sched_disabled_context_rely_preserves_entry_source view sg
    before acquired_2 Hrely PreH6) as Hsource.
  pose proof (sched_disabled_entry_source_protected_identity view acquired_2
    Hsource) as Hidentity.
  sep_apply_l_atomic (critical_region_interval_open_invariant critical sg
    (os_execution_invocation view) before acquired_2 PreH1 PreH5).
  Exists acquired_2; entailer!.
Qed.

Lemma proof_of_OS_Sched_return_wit_1 : OS_Sched_return_wit_1.
Proof.
  unfold OS_Sched_return_wit_1; left.
  intros before mask view sg critical platform external acquired cpu_sr current
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9.
  destruct (sched_disabled_interval_preserves_context critical sg view
    (os_execution_invocation view) acquired current PreH3 PreH6 PreH1)
    as [Hcurrent Hafter].
  pose proof (sched_disabled_context_rely_preserves_entry_source view sg
    acquired current Hafter PreH8) as Hsource.
  pose proof (sched_disabled_context_rely_trans view sg before acquired current
    PreH7 Hafter) as Hrely.
  unfold sched_disabled_contextual_post, sched_disabled_closed.
  destruct PreH5 as [Hword Hmask]; rewrite Hmask.
  Exists cpu_sr acquired current; entailer!.
  split; assumption.
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_1 : OS_Sched_which_implies_wit_1.
Proof.
  unfold OS_Sched_which_implies_wit_1; left; intros.
  unfold sched_disabled_closed; entailer!.
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_2 : OS_Sched_which_implies_wit_2.
Proof.
  unfold OS_Sched_which_implies_wit_2; left.
  intros view sg acquired PreH1 PreH2.
  rewrite sched_disabled_inv_split_counters.
  destruct PreH1 as [Hintegers Hlocks].
  rewrite <- Hintegers, <- Hlocks.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range (&( "OSIntNesting" ))
    (os_sched_ints acquired)).
  prop_apply_p (UCOS2_C_Rules.store_uchar_range (&( "OSLockNesting" ))
    (os_sched_locks acquired)).
  unfold sched_disabled_counter_frame; Intros.
  assert (Hpositive : 0 < os_sched_ints acquired + os_sched_locks acquired).
  { apply sched_disabled_counters_positive_guard with (view := view); tauto. }
  entailer!; unfold sched_disabled_addresses in *; try tauto;
    change Byte.max_unsigned with 255 in *; lia.
Qed.

Lemma proof_of_OS_Sched_which_implies_wit_3 : OS_Sched_which_implies_wit_3.
Proof.
  unfold OS_Sched_which_implies_wit_3; left.
  intros sg acquired PreH1.
  rewrite sched_disabled_inv_split_counters.
  destruct PreH1 as [Hintegers Hlocks].
  rewrite <- Hintegers, <- Hlocks.
  entailer!; unfold sched_disabled_addresses; auto.
Qed.

