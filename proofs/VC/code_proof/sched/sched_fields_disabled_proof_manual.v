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
From Ucos2Verify.VC.code.sched Require Import sched_fields_disabled_goal.
From Ucos2Verify.VC.code.sched Require Import sched_fields_disabled_proof_auto.
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
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_disabled_spec.
Local Open Scope sac.

Lemma proof_of_OS_Sched_entail_wit_1 : OS_Sched_entail_wit_1.
Proof.
  unfold OS_Sched_entail_wit_1; left.
  intros frame before mask view sg local critical environment first_heap retval Haddresses.
  sep_apply_l_atomic (sched_fields_disabled_save_output_open environment critical sg view mask
    before local frame first_heap retval).
  Intros entered acquired entered_local saved_heap.
  Exists entered acquired entered_local saved_heap; entailer!; tauto.
Qed. 

Lemma proof_of_OS_Sched_return_wit_1 : OS_Sched_return_wit_1.
Proof.
  unfold OS_Sched_return_wit_1; left; intros.
  sep_apply_l_atomic (sched_fields_disabled_post_from_restore environment critical sg view mask
    before local frame cpu_sr entered acquired entered_local first_heap saved_heap restore_heap PreH12).
  entailer!.
Qed. 

Lemma proof_of_OS_Sched_return_wit_2 : OS_Sched_return_wit_2.
Proof.
  unfold OS_Sched_return_wit_2; left; intros.
  sep_apply_l_atomic (sched_fields_disabled_post_from_restore environment critical sg view mask
    before local frame cpu_sr entered acquired entered_local first_heap saved_heap restore_heap PreH11).
  entailer!.
Qed. 

Lemma proof_of_OS_Sched_which_implies_wit_1 : OS_Sched_which_implies_wit_1.
Proof.
  unfold OS_Sched_which_implies_wit_1; left; intros.
  apply sched_fields_heap_capture.
Qed. 

Lemma proof_of_OS_Sched_which_implies_wit_2 : OS_Sched_which_implies_wit_2.
Proof.
  unfold OS_Sched_which_implies_wit_2; left.
  intros sg critical environment entered acquired entered_local cpu_sr Haddresses Hsource.
  rewrite sched_fields_disabled_masked_split_counters.
  destruct Haddresses as [Hintegers Hlocks]; rewrite <- Hintegers, <- Hlocks.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range (&( "OSIntNesting" )) (os_sched_ints acquired)).
  prop_apply_p (UCOS2_C_Rules.store_uchar_range (&( "OSLockNesting" )) (os_sched_locks acquired)).
  unfold sched_fields_disabled_counter_frame; Intros.
  assert (Hpositive : 0 < os_sched_ints acquired + os_sched_locks acquired).
  { apply sched_disabled_counters_positive_guard with (view := entered); tauto. }
  entailer!; unfold sched_disabled_addresses in *; try tauto;
    change Byte.max_unsigned with 255 in *; lia.
Qed. 

Lemma proof_of_OS_Sched_which_implies_wit_3 : OS_Sched_which_implies_wit_3.
Proof.
  unfold OS_Sched_which_implies_wit_3; left.
  intros sg critical environment entered acquired entered_local cpu_sr Haddresses.
  rewrite sched_fields_disabled_masked_split_counters.
  destruct Haddresses as [Hintegers Hlocks]; rewrite <- Hintegers, <- Hlocks.
  entailer!; unfold sched_disabled_addresses; auto.
Qed. 

Lemma proof_of_OS_Sched_which_implies_wit_4 : OS_Sched_which_implies_wit_4.
Proof.
  unfold OS_Sched_which_implies_wit_4; left; intros.
  unfold sched_fields_disabled_restore_pre; entailer!; tauto.
Qed. 

Lemma proof_of_OS_Sched_which_implies_wit_5 : OS_Sched_which_implies_wit_5.
Proof.
  unfold OS_Sched_which_implies_wit_5; left; intros.
  apply sched_fields_heap_capture.
Qed. 

