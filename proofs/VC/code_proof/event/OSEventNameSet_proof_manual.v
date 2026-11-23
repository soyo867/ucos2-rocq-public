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
From Ucos2Verify.VC.code.event Require Import OSEventNameSet_goal.
From Ucos2Verify.VC.code.event Require Import OSEventNameSet_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.event.spec.event_name_set_call_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSEventNameSet_return_wit_1 : OSEventNameSet_return_wit_1.
Proof.
  left; intros.
  assert (Htype : event_name_type_allowed type_byte = false).
  { apply event_name_type_allowed_false_iff; lia. }
  pose proof (event_name_set_invalid_type_error pevent_pre pname_pre nesting type_byte
    PreH1 PreH2 PreH3 Htype) as Herror.
  Exists 1.
  unfold event_name_set_observation, event_name_set_final_name; rewrite Herror.
  rewrite (event_name_set_access_type_split _ _ _ _ _ _ _ PreH1 PreH2 PreH3).
  entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSEventNameSet_return_wit_2 : OSEventNameSet_return_wit_2.
Proof.
  left; intros; Exists 18.
  pose proof (event_name_set_isr_error pevent_pre pname_pre nesting type_byte
    PreH3 PreH2 ltac:(lia)) as Herror.
  unfold event_name_set_observation, event_name_set_final_name; rewrite Herror.
  entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSEventNameSet_return_wit_3 : OSEventNameSet_return_wit_3.
Proof.
  left; intros; subst pname_pre; Exists 12.
  pose proof (event_name_set_null_name_error pevent_pre nesting type_byte PreH2) as Herror.
  unfold event_name_set_observation, event_name_set_final_name; rewrite Herror.
  entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSEventNameSet_return_wit_4 : OSEventNameSet_return_wit_4.
Proof.
  left; intros; subst pevent_pre; Exists 4.
  unfold event_name_set_observation, event_name_set_final_name.
  rewrite event_name_set_null_event_error; entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSEventNameSet_return_wit_5 : OSEventNameSet_return_wit_5.
Proof.
  left; intros; Intros.
  match goal with H : event_name_type_supported type_byte |- _ => rename H into Htype end.
  unfold event_name_type_supported in Htype.
  pose proof (event_name_set_success_guard pevent_pre pname_pre nesting type_byte
    PreH1 PreH2 PreH3 Htype) as Hsuccess.
  Exists 0.
  unfold event_name_set_observation, event_name_set_final_name; rewrite Hsuccess.
  rewrite (event_name_set_access_type_split _ _ _ _ _ _ _ PreH1 PreH2 PreH3).
  rewrite (event_name_set_after_type_supported _ _ _ Htype); entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSEventNameSet_return_wit_6 : OSEventNameSet_return_wit_6.
Proof.
  left; intros; Intros.
  match goal with H : event_name_type_supported type_byte |- _ => rename H into Htype end.
  unfold event_name_type_supported in Htype.
  pose proof (event_name_set_success_guard pevent_pre pname_pre nesting type_byte
    PreH1 PreH2 PreH3 Htype) as Hsuccess.
  Exists 0.
  unfold event_name_set_observation, event_name_set_final_name; rewrite Hsuccess.
  rewrite (event_name_set_access_type_split _ _ _ _ _ _ _ PreH1 PreH2 PreH3).
  rewrite (event_name_set_after_type_supported _ _ _ Htype); entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSEventNameSet_return_wit_7 : OSEventNameSet_return_wit_7.
Proof.
  left; intros; Intros.
  match goal with H : event_name_type_supported type_byte |- _ => rename H into Htype end.
  unfold event_name_type_supported in Htype.
  pose proof (event_name_set_success_guard pevent_pre pname_pre nesting type_byte
    PreH1 PreH2 PreH3 Htype) as Hsuccess.
  Exists 0.
  unfold event_name_set_observation, event_name_set_final_name; rewrite Hsuccess.
  rewrite (event_name_set_access_type_split _ _ _ _ _ _ _ PreH1 PreH2 PreH3).
  rewrite (event_name_set_after_type_supported _ _ _ Htype); entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSEventNameSet_return_wit_8 : OSEventNameSet_return_wit_8.
Proof.
  left; intros; Intros.
  match goal with H : event_name_type_supported type_byte |- _ => rename H into Htype end.
  unfold event_name_type_supported in Htype.
  pose proof (event_name_set_success_guard pevent_pre pname_pre nesting type_byte
    PreH1 PreH2 PreH3 Htype) as Hsuccess.
  Exists 0.
  unfold event_name_set_observation, event_name_set_final_name; rewrite Hsuccess.
  rewrite (event_name_set_access_type_split _ _ _ _ _ _ _ PreH1 PreH2 PreH3).
  rewrite (event_name_set_after_type_supported _ _ _ Htype); entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSEventNameSet_which_implies_wit_1 : OSEventNameSet_which_implies_wit_1.
Proof.
  left; intros.
  rewrite (event_name_set_access_type_split _ _ _ _ _ _ _ PreH1 PreH2 PreH3).
  entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSEventNameSet_which_implies_wit_2 : OSEventNameSet_which_implies_wit_2.
Proof.
  left; intros.
  assert (Htype : event_name_type_allowed type_byte = true).
  { apply event_name_type_allowed_true_iff; lia. }
  rewrite (event_name_set_after_type_supported _ _ _ Htype).
  unfold event_name_type_supported; entailer!; try apply derivable1_truep_intros.
Qed.
