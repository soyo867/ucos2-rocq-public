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
From Ucos2Verify.VC.code.event Require Import OSEventNameGet_goal.
From Ucos2Verify.VC.code.event Require Import OSEventNameGet_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.event.spec.event_name_get_call_spec.
Require Import Ucos2Verify.lib.error_codes.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSEventNameGet_return_wit_1 : OSEventNameGet_return_wit_1.
Proof.
  unfold OSEventNameGet_return_wit_1; left; intros; Exists 0.
  assert (Hty : event_name_type_allowed type_byte = true)
    by (apply event_name_get_type_allowed_range; lia).
  assert (Herr : event_name_get_error pevent_pre pname_pre nesting type_byte = None)
    by (apply event_name_get_success_guard; assumption).
  unfold event_name_get_observation, event_name_get_output, event_name_get_final_output.
  rewrite Herr.
  rewrite (event_name_get_access_type_split pevent_pre pname_pre _ _ name nesting type_byte name chars)
    by assumption.
  unfold event_name_get_after_type, event_name_get_success_focus; rewrite Hty.
  cbn [encode_os_err_code]; entailer!.
Qed.

Lemma proof_of_OSEventNameGet_return_wit_2 : OSEventNameGet_return_wit_2.
Proof.
  unfold OSEventNameGet_return_wit_2; left; intros; Exists 0.
  assert (Hty : event_name_type_allowed type_byte = true)
    by (apply event_name_get_type_allowed_range; lia).
  assert (Herr : event_name_get_error pevent_pre pname_pre nesting type_byte = None)
    by (apply event_name_get_success_guard; assumption).
  unfold event_name_get_observation, event_name_get_output, event_name_get_final_output.
  rewrite Herr.
  rewrite (event_name_get_access_type_split pevent_pre pname_pre _ _ name nesting type_byte name chars)
    by assumption.
  unfold event_name_get_after_type, event_name_get_success_focus; rewrite Hty.
  cbn [encode_os_err_code]; entailer!.
Qed.

Lemma proof_of_OSEventNameGet_return_wit_3 : OSEventNameGet_return_wit_3.
Proof.
  unfold OSEventNameGet_return_wit_3; left; intros; Exists 0.
  assert (Hty : event_name_type_allowed type_byte = true)
    by (apply event_name_get_type_allowed_range; lia).
  assert (Herr : event_name_get_error pevent_pre pname_pre nesting type_byte = None)
    by (apply event_name_get_success_guard; assumption).
  unfold event_name_get_observation, event_name_get_output, event_name_get_final_output.
  rewrite Herr.
  rewrite (event_name_get_access_type_split pevent_pre pname_pre _ _ name nesting type_byte name chars)
    by assumption.
  unfold event_name_get_after_type, event_name_get_success_focus; rewrite Hty.
  cbn [encode_os_err_code]; entailer!.
Qed.

Lemma proof_of_OSEventNameGet_return_wit_4 : OSEventNameGet_return_wit_4.
Proof.
  unfold OSEventNameGet_return_wit_4; left; intros; Exists 0.
  assert (Hty : event_name_type_allowed type_byte = true)
    by (apply event_name_get_type_allowed_range; lia).
  assert (Herr : event_name_get_error pevent_pre pname_pre nesting type_byte = None)
    by (apply event_name_get_success_guard; assumption).
  unfold event_name_get_observation, event_name_get_output, event_name_get_final_output.
  rewrite Herr.
  rewrite (event_name_get_access_type_split pevent_pre pname_pre _ _ name nesting type_byte name chars)
    by assumption.
  unfold event_name_get_after_type, event_name_get_success_focus; rewrite Hty.
  cbn [encode_os_err_code]; entailer!.
Qed.

Lemma proof_of_OSEventNameGet_return_wit_5 : OSEventNameGet_return_wit_5.
Proof.
  unfold OSEventNameGet_return_wit_5; left; intros; Exists 1.
  assert (Hty : event_name_type_allowed type_byte = false).
  { destruct (event_name_type_allowed type_byte) eqn:Hty; [apply event_name_get_type_allowed_range in Hty; lia|reflexivity]. }
  assert (Herr : event_name_get_error pevent_pre pname_pre nesting type_byte = Some OS_ERR_EVENT_TYPE)
    by (apply event_name_get_invalid_type_error; assumption).
  unfold event_name_get_observation, event_name_get_output, event_name_get_final_output.
  rewrite Herr; cbn [encode_os_err_code].
  rewrite (event_name_get_access_type_split pevent_pre pname_pre _ _ name nesting type_byte output_old chars)
    by assumption.
  entailer!.
Qed.

Lemma proof_of_OSEventNameGet_return_wit_6 : OSEventNameGet_return_wit_6.
Proof.
  unfold OSEventNameGet_return_wit_6; left; intros; Exists 17.
  assert (Herr : event_name_get_error pevent_pre pname_pre nesting type_byte = Some OS_ERR_NAME_GET_ISR)
    by (apply event_name_get_isr_error; lia).
  unfold event_name_get_observation, event_name_get_output, event_name_get_final_output.
  rewrite Herr; cbn [encode_os_err_code].
  entailer!.
Qed.

Lemma proof_of_OSEventNameGet_return_wit_7 : OSEventNameGet_return_wit_7.
Proof.
  unfold OSEventNameGet_return_wit_7; left; intros; Exists 12.
  assert (Herr : event_name_get_error pevent_pre pname_pre nesting type_byte = Some OS_ERR_PNAME_NULL).
  { subst pname_pre; apply event_name_get_null_output_error; assumption. }
  unfold event_name_get_observation, event_name_get_output, event_name_get_final_output.
  rewrite Herr; cbn [encode_os_err_code].
  entailer!.
Qed.

Lemma proof_of_OSEventNameGet_return_wit_8 : OSEventNameGet_return_wit_8.
Proof.
  unfold OSEventNameGet_return_wit_8; left; intros; Exists 4.
  assert (Herr : event_name_get_error pevent_pre pname_pre nesting type_byte = Some OS_ERR_PEVENT_NULL).
  { subst pevent_pre; apply event_name_get_null_event_error. }
  unfold event_name_get_observation, event_name_get_output, event_name_get_final_output.
  rewrite Herr; cbn [encode_os_err_code].
  entailer!.
Qed.

Lemma proof_of_OSEventNameGet_which_implies_wit_1 : OSEventNameGet_which_implies_wit_1.
Proof.
  unfold OSEventNameGet_which_implies_wit_1; left; intros.
  rewrite event_name_get_access_type_split by assumption; entailer!.
Qed.

Lemma proof_of_OSEventNameGet_which_implies_wit_2 : OSEventNameGet_which_implies_wit_2.
Proof.
  unfold OSEventNameGet_which_implies_wit_2; left; intros.
  assert (Hty : event_name_type_allowed type_byte = true)
    by (apply event_name_get_type_allowed_range; lia).
  rewrite event_name_get_after_type_success by assumption.
  unfold event_name_get_request; Intros.
  specialize (H (event_name_get_success_guard pevent pname nesting type_byte PreH1 PreH2 PreH3 Hty)).
  entailer!.
Qed.

Lemma proof_of_OS_StrLen_derive_name_get_spec_by_source_spec : OS_StrLen_derive_name_get_spec_by_source_spec.
Proof.
  unfold OS_StrLen_derive_name_get_spec_by_source_spec; intros; Intros.
  subst entry_name_get_spec.
  destruct (Z.eqb psrc_pre 0) eqn:Hp.
  1: Exists psrc_pre psrc_pre names_name_get_spec chars_name_get_spec ((TT) ** frame_name_get_spec).
  2: Exists psrc_pre psrc_pre names_name_get_spec chars_name_get_spec frame_name_get_spec.
  all: match goal with |- _ |-- ?P ** (?Q -* ?R) =>
    assert (Hwand : emp |-- Q -* R)
  end.
  1,3: (apply_sepcon_adjoint; pre_process; apply derivable1_orp_elim; Intros retval;
    Exists retval; unfold event_name_get_result, event_name_get_length, event_name_get_name_bytes,
      os_strlen_result; rewrite Hp; entailer!; try congruence).
  all: rewrite <- Hwand, sepcon_emp_equiv.
  1: Right; unfold event_name_get_name_bytes; rewrite Hp;
    apply Z.eqb_eq in Hp; entailer!.
  all: Left; unfold event_name_get_name_bytes; rewrite Hp;
    apply Z.eqb_neq in Hp; unfold event_name_get_readable in *; entailer!; auto.
Qed.
