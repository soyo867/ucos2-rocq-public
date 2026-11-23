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
From Ucos2Verify.VC.code.sem Require Import accept_goal.
From Ucos2Verify.VC.code.sem Require Import accept_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_source_api_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSSemAccept_which_implies_wit_1 : OSSemAccept_which_implies_wit_1.
Proof.
  unfold OSSemAccept_which_implies_wit_1; left; intros.
  rewrite sem_accept_closed_equiv; Intros.
  match goal with H : sem_accept_call_input _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hinput end.
  destruct Hinput as [Hnull|[Hnonzero [Haddr [Hid [Hlookup Hprotocol]]]]]; [congruence|].
  sep_apply_l_atomic (sem_accept_type_split_full sg before eid observed Hlookup); Intros.
  match goal with H : event_core_fields_layout_prop _ _ _ _ _ |- _ =>
    pose proof H as [Htype [Hptr Hcnt]] end.
  rewrite Htype; unfold sem_accept_lookup; entailer!.
  - repeat apply derivable1s_emp_sepcon_unfold; apply derivable1_truep_intros.
  - unfold event_core_fields_layout_prop; auto.
Qed.

Lemma proof_of_OSSemAccept_which_implies_wit_2 : OSSemAccept_which_implies_wit_2.
Proof.
  unfold OSSemAccept_which_implies_wit_2; left; intros; Intros.
  match goal with H : sem_accept_call_input _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hinput end.
  destruct Hinput as [Hnull|[Hnonzero [Haddr [Hid [Hlookup Hprotocol]]]]]; [congruence|].
  assert (Hsem : eventType observed = OS_EVENT_TYPE_SEM).
  { destruct (eventType observed); cbn in *; congruence. }
  specialize (Hprotocol Hsem).
  match goal with H : event_core_fields_layout_prop _ _ _ _ _ |- _ =>
    pose proof H as [Htype [Hptr Hcnt]] end.
  rewrite Htype.
  match goal with H : UCOS2_state_inv sg before |- _ =>
    sep_apply_l_atomic (sem_accept_type_merge_full sg before eid observed H Hlookup) end.
  unfold sem_accept_lookup; entailer!.
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1_truep_intros].
  all: try solve [unfold event_core_fields_layout_prop; auto].
Qed.

Lemma proof_of_OSSemAccept_which_implies_wit_3 : OSSemAccept_which_implies_wit_3.
Proof.
  unfold OSSemAccept_which_implies_wit_3; left; intros; Intros.
  match goal with H : sem_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as [Hinterval [Hvalid [Hsaved [Hbefore [Hlookup [Hobserved [Hsem Hgen]]]]]]] end.
  match goal with H : event_core_fields_layout_prop _ _ _ _ _ |- _ =>
    pose proof H as [Htype [Hptr Hcnt]] end.
  sep_apply_l_atomic (sem_accept_count_split_full sg entry_2 eid current_2 Hlookup Hsem); Intros.
  Exists entry_2 current_2; rewrite Hcnt; entailer!.
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1_truep_intros].
  all: try solve [unfold event_core_fields_layout_prop; auto].
Qed.

Lemma proof_of_OSSemAccept_which_implies_wit_4 : OSSemAccept_which_implies_wit_4.
Proof.
  unfold OSSemAccept_which_implies_wit_4; left; intros; Intros.
  match goal with H : sem_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as [Hinterval [Hvalid [Hsaved [Hbefore [Hlookup [Hobserved [Hsem Hgen]]]]]]] end.
  match goal with H : event_core_fields_layout_prop _ _ _ _ _ |- _ =>
    pose proof H as [Htype [Hptr Hcnt]] end.
  rewrite Hcnt.
  sep_apply_l_atomic (sem_accept_count_merge_checkpoint sg entry_2 eid current_2 Hvalid Hlookup Hsem).
  Exists entry_2 current_2.
  pose proof (sem_accept_checkpoint_preserves_validity sg entry_2 eid current_2
    Hvalid Hlookup Hsem) as Hcheckpoint.
  unfold sem_accept_source_api_restore_pre.
  sep_apply_l_atomic (derivable1_truep_intros (TT ** TT)); entailer!.
Qed.

Lemma proof_of_OSSemAccept_return_wit_3 : OSSemAccept_return_wit_3.
Proof.
  unfold OSSemAccept_return_wit_3; left; intros; Intros.
  assert (Hpe : pe = 0) by congruence.
  assert (Hsem : sem_accept_source_api_post critical sg invocation pe before 0 before).
  { rewrite Hpe; apply sem_accept_source_api_null_return. }
  pose proof (sem_accept_source_api_safe_return _ _ _ _ _ _ _ _ PreH3 Hsem) as Hexec.
  Exists before.
  repeat sep_apply_l_atomic (derivable1_truep_intros (TT ** TT)); entailer!.
Qed.

Lemma proof_of_OSSemAccept_return_wit_4 : OSSemAccept_return_wit_4.
Proof.
  unfold OSSemAccept_return_wit_4; left; intros; Intros.
  assert (Hpe : pe = 0) by congruence.
  assert (Hsem : sem_accept_source_api_post critical sg invocation pe before 0 before).
  { rewrite Hpe; apply sem_accept_source_api_null_return. }
  pose proof (sem_accept_source_api_safe_return _ _ _ _ _ _ _ _ PreH4 Hsem) as Hexec.
  Exists before.
  repeat sep_apply_l_atomic (derivable1_truep_intros (TT ** TT)); entailer!.
Qed.

Lemma proof_of_OSSemAccept_return_wit_1 : OSSemAccept_return_wit_1.
Proof.
  unfold OSSemAccept_return_wit_1; left; intros; Intros.
  assert (Hsem : sem_accept_source_api_post critical sg invocation pe before
    (encode_event_cnt_value current) after_2).
  { rewrite PreH2; eapply sem_accept_source_api_restored_return; eassumption. }
  pose proof (sem_accept_source_api_safe_return _ _ _ _ _ _ _ _ PreH6 Hsem) as Hexec.
  Exists after_2.
  repeat sep_apply_l_atomic (derivable1_truep_intros (TT ** TT)); entailer!.
Qed.

Lemma proof_of_OSSemAccept_return_wit_2 : OSSemAccept_return_wit_2.
Proof.
  unfold OSSemAccept_return_wit_2; left; intros; Intros.
  assert (Hnonzero : pe <> 0) by congruence.
  assert (Htype : eventType observed <> OS_EVENT_TYPE_SEM).
  { intro Htype; rewrite Htype in PreH1; vm_compute in PreH1; congruence. }
  assert (Hsem : sem_accept_source_api_post critical sg invocation pe before 0 before).
  { eapply sem_accept_source_api_wrong_type_return; eauto. }
  pose proof (sem_accept_source_api_safe_return _ _ _ _ _ _ _ _ PreH5 Hsem) as Hexec.
  match goal with H : event_core_fields_layout_prop _ _ _ _ _ |- _ =>
    pose proof H as [Htypeaddr [Hptr Hcnt]] end.
  rewrite Htypeaddr.
  unfold sem_accept_lookup in *.
  match goal with Hvalid : UCOS2_state_inv sg before,
                  Hlookup : inUsedEventStates (EventState before) eid = Some observed |- _ =>
    sep_apply_l_atomic (sem_accept_type_merge_full sg before eid observed Hvalid Hlookup) end.
  Exists before; rewrite sem_accept_closed_equiv.
  repeat sep_apply_l_atomic (derivable1_truep_intros (TT ** TT)); entailer!.
Qed.

Lemma proof_of_OSSemAccept_entail_wit_1_1 : OSSemAccept_entail_wit_1_1.
Proof.
  unfold OSSemAccept_entail_wit_1_1; left; intros; Intros.
  Exists entry_2 current.
  unfold sem_accept_stored_count.
  assert (Hpositive : (0 <? encode_event_cnt_value current) = true) by (apply Z.ltb_lt; lia).
  rewrite Hpositive; entailer!; try congruence.
  apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSSemAccept_entail_wit_1_2 : OSSemAccept_entail_wit_1_2.
Proof.
  unfold OSSemAccept_entail_wit_1_2; left; intros; Intros.
  Exists entry_2 current.
  unfold sem_accept_stored_count.
  assert (Hpositive : (0 <? encode_event_cnt_value current) = false) by (apply Z.ltb_ge; lia).
  rewrite Hpositive; entailer!; try congruence.
  apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSSemAccept_partial_solve_wit_2_pure : OSSemAccept_partial_solve_wit_2_pure.
Proof.
  unfold OSSemAccept_partial_solve_wit_2_pure; left; intros; Intros.
  assert (Htype : encode_event_type (eventType observed) = 3).
  { destruct (eventType observed); vm_compute in PreH1 |- *; congruence. }
  entailer!; congruence.
Qed.
