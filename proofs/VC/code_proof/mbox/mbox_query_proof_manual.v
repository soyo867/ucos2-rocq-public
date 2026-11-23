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
From Ucos2Verify.VC.code.mbox Require Import mbox_query_goal.
From Ucos2Verify.VC.code.mbox Require Import mbox_query_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_query_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSMboxQuery_entail_wit_1_2 : OSMboxQuery_entail_wit_1_2.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range (&(pe # "os_event" ->ₛ "OSEventType"))
    (event_slot_type_value before.(EventState) eid)).
  entailer!.
Qed.

Lemma proof_of_OSMboxQuery_entail_wit_2 : OSMboxQuery_entail_wit_2.
Proof.
  left; intros; entailer!.
Qed.

Lemma proof_of_OSMboxQuery_entail_wit_3 : OSMboxQuery_entail_wit_3.
Proof.
  left; intros; entailer!; lia.
Qed.

Lemma proof_of_OSMboxQuery_return_wit_1 : OSMboxQuery_return_wit_1.
Proof.
  left; intros; unfold mbox_query_restore_post; Intros returned.
  match goal with H : mbox_query_acquire_facts _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as [Hacquire [_ [Hsaved _]]] end.
  destruct Hsaved as [_ Hmask].
  assert (Hprogram : mbox_query_program critical sg invocation eid pe pd before
    (0, Some snapshot) returned).
  { eapply mbox_query_program_success with (entry := entry); eauto; congruence. }
  pose proof (mbox_query_api_safe_return critical sg invocation eid pe pd before
    returned 0 (Some snapshot) X Hprogram PreH15) as Hsafe.
  unfold mbox_query_api_post; Exists (Some snapshot) returned.
  cbn [mbox_query_output_post]; rewrite Hmask.
  assert (Htrue : (TT ** TT) |-- TT) by entailer!.
  repeat sep_apply_l_atomic Htrue.
  entailer!.
Qed.

Lemma proof_of_OSMboxQuery_return_wit_2 : OSMboxQuery_return_wit_2.
Proof.
  left; intros; Intros.
  rewrite PreH7.
  sep_apply_l_atomic (mbox_query_type_merge_full sg before eid ltac:(assumption)).
  assert (Hprogram : mbox_query_program critical sg invocation eid pe pd before
    (1, None) before).
  { apply mbox_query_program_wrong_type; congruence. }
  pose proof (mbox_query_api_safe_return critical sg invocation eid pe pd before
    before 1 None X Hprogram PreH12) as Hsafe.
  unfold mbox_query_api_post; Exists (@None MboxQuerySnapshot) before.
  cbn [mbox_query_output_post].
  rewrite mutex_query_closed_equiv.
  assert (Htrue : (TT ** TT) |-- TT) by entailer!.
  repeat sep_apply_l_atomic Htrue.
  entailer!.
Qed.

Lemma proof_of_OSMboxQuery_return_wit_3 : OSMboxQuery_return_wit_3.
Proof.
  left; intros; Intros.
  assert (Hpd : pd = 0) by congruence.
  assert (Hprogram : mbox_query_program critical sg invocation eid pe pd before
    (9, None) before).
  { rewrite Hpd; apply mbox_query_program_null_output; congruence. }
  pose proof (mbox_query_api_safe_return critical sg invocation eid pe pd before
    before 9 None X Hprogram PreH5) as Hsafe.
  unfold mbox_query_api_post; Exists (@None MboxQuerySnapshot) before.
  cbn [mbox_query_output_post]; entailer!.
Qed.

Lemma proof_of_OSMboxQuery_return_wit_4 : OSMboxQuery_return_wit_4.
Proof.
  left; intros; Intros.
  assert (Hpe : pe = 0) by congruence.
  assert (Hprogram : mbox_query_program critical sg invocation eid pe pd before
    (4, None) before).
  { rewrite Hpe; apply mbox_query_program_null_event. }
  pose proof (mbox_query_api_safe_return critical sg invocation eid pe pd before
    before 4 None X Hprogram PreH4) as Hsafe.
  unfold mbox_query_api_post; Exists (@None MboxQuerySnapshot) before.
  cbn [mbox_query_output_post]; entailer!.
Qed.

Lemma proof_of_OSMboxQuery_which_implies_wit_1 : OSMboxQuery_which_implies_wit_1.
Proof.
  left; intros; Intros.
  match goal with H : mbox_query_call_input _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hinput end.
  unfold mbox_query_call_input in Hinput.
  destruct Hinput as [Hnull|[[Hnonnull Hnull]|[Hpe [Hpd [Haddr [Hid [Hslot Hprotocol]]]]]]];
    try contradiction.
  rewrite mutex_query_closed_equiv.
  sep_apply_l_atomic (mbox_query_type_split_full sg before eid observed Hslot).
  rewrite PreH3; entailer!.
  repeat apply sepcon_cancel_end; entailer!.
Qed.

Lemma proof_of_OSMboxQuery_which_implies_wit_2 : OSMboxQuery_which_implies_wit_2.
Proof.
  left; intros; Intros.
  match goal with H : mbox_query_call_input _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hinput end.
  unfold mbox_query_call_input in Hinput.
  destruct Hinput as [Hnull|[[Hnonnull Hnull]|[Hpe [Hpd [Haddr [Hid [Hslot Hprotocol]]]]]]];
    try contradiction.
  destruct (mbox_query_public_slot_is_mbox before eid observed Hslot PreH3)
    as [Hlookup Htype].
  specialize (Hprotocol PreH3).
  rewrite PreH4.
  sep_apply_l_atomic (mbox_query_type_merge_full sg before eid ltac:(assumption)).
  unfold critical_region_outside.
  rewrite critical_region_outside_without_running_rep.
  rewrite <- UCOS2_raw_rep_split_running.
  unfold UCOS2_inv; rewrite Htype; entailer!.
  entailer!.
Qed.

Lemma proof_of_OSMboxQuery_which_implies_wit_3 : OSMboxQuery_which_implies_wit_3.
Proof.
  left; intros; Intros.
  match goal with H : mbox_query_acquire_facts _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hacquire end.
  match goal with H : mbox_query_layout _ _ _ |- _ => pose proof H as Hlayout end.
  pose proof Hacquire as [_ [Hvalid [_ [_ [Hlookup [_ [Htype _]]]]]]].
  destruct (mbox_query_current_fields sg entry_2 eid current_2 Hvalid Hlookup Htype)
    as [message Hmessage].
  sep_apply_l_atomic (mbox_query_fields_split_full sg entry_2 eid current_2 message
    Hlookup Htype Hmessage).
  Intros.
  destruct Hlayout as [[[Htypeaddr [Hptraddr Hcntaddr]] [Hgrpaddr Htbladdr]] Houtputaddr].
  prop_apply_p (mbox_query_event_table_bounds sg eid current_2).
  prop_apply_p (mbox_query_output_table_bounds
    (&(pd # "os_mbox_data" ->ₛ "OSEventTbl"))
    (&(pd # "os_mbox_data" ->ₛ "OSEventGrp")) Houtputaddr).
  Exists entry_2 current_2 message (mbox_message_ptr message)
    (encode_event_wait_grp current_2.(waitList) entry_2.(TskState))
    (encode_event_wait_tbl_values_or current_2 entry_2.(TskState)).
  unfold mbox_query_copy_frame, mbox_query_read_facts.
  rewrite PreH1, Hptraddr, Hgrpaddr, Htbladdr.
  Intros.
  assert (Htrue : (TT ** TT) |-- TT) by entailer!.
  repeat sep_apply_l_atomic Htrue.
  entailer!.
Qed.

Lemma proof_of_OSMboxQuery_which_implies_wit_4 : OSMboxQuery_which_implies_wit_4.
Proof.
  left; intros; apply mbox_query_output_table_init.
Qed.

Lemma proof_of_OSMboxQuery_which_implies_wit_5 : OSMboxQuery_which_implies_wit_5.
Proof.
  left; intros rows i psrc pevent pdest p_mbox_data Hi Hbound Hlen Hsrc Hdest.
  subst psrc pdest; rewrite sizeof_uchar; rewrite Z.mul_1_r.
  unfold store_osprio_array, store_osprio_array_missing_i.
  sep_apply (store_array_split_to_missing_i Z oseventtbl_element_store
    (&(pevent # "os_event" ->ₛ "OSEventTbl")) i OS_EVENT_TBL_SIZE rows 0
    ltac:(unfold OS_EVENT_TBL_SIZE; lia)).
  sep_apply (mbox_query_output_table_split
    (&(p_mbox_data # "os_mbox_data" ->ₛ "OSEventTbl")) rows i
    ltac:(unfold OS_EVENT_TBL_SIZE; lia)).
  unfold oseventtbl_element_store, sizeof_OS_PRIO; rewrite Z.mul_1_r.
  entailer!.
Qed.

Lemma proof_of_OSMboxQuery_which_implies_wit_6 : OSMboxQuery_which_implies_wit_6.
Proof.
  left; intros rows i pevent p_mbox_data Hi Hbound Hlen.
  rewrite sizeof_uchar; rewrite !Z.mul_1_r.
  sep_apply (mbox_query_output_table_merge
    (&(p_mbox_data # "os_mbox_data" ->ₛ "OSEventTbl")) rows i ltac:(lia)).
  unfold store_osprio_array, store_osprio_array_missing_i.
  unfold oseventtbl_element_store, sizeof_OS_PRIO.
  pose proof (store_array_missing_i_merge_to_array Z oseventtbl_element_store
    (&(pevent # "os_event" ->ₛ "OSEventTbl")) i OS_EVENT_TBL_SIZE
    (Znth i rows 0) rows ltac:(unfold OS_EVENT_TBL_SIZE; lia)) as Hmerge.
  unfold oseventtbl_element_store, sizeof_OS_PRIO in Hmerge.
  rewrite Z.mul_1_r, replace_Znth_Znth in Hmerge.
  sep_apply Hmerge; entailer!.
Qed.

Lemma proof_of_OSMboxQuery_which_implies_wit_7 : OSMboxQuery_which_implies_wit_7.
Proof.
  left; intros rows i p_mbox_data Hlower Hupper Hlen.
  sep_apply (mbox_query_output_table_complete
    (&(p_mbox_data # "os_mbox_data" ->ₛ "OSEventTbl")) rows i
    Hlen ltac:(unfold OS_EVENT_TBL_SIZE; lia)).
  entailer!.
Qed.

Lemma proof_of_OSMboxQuery_which_implies_wit_8 : OSMboxQuery_which_implies_wit_8.
Proof.
  left; intros; unfold mbox_query_copy_frame; Intros.
  match goal with H : mbox_query_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hacquire Hread] end.
  destruct Hread as [Hvalid [Hlookup [Htype [Hmessage [Hpointer [Hgroup Hrows]]]]]].
  match goal with H : mbox_query_layout _ _ _ |- _ =>
    destruct H as [[[Htypeaddr [Hptraddr Hcntaddr]] [Hgrpaddr Htbladdr]] Houtputaddr] end.
  subst pointer grp rows.
  rewrite PreH1, Hptraddr, Hgrpaddr, Htbladdr.
  sep_apply_l_atomic (mbox_query_fields_merge_full sg entry eid current message
    Hvalid Hlookup Htype Hmessage).
  assert (Hsnapshot : mbox_query_critical eid entry
    (mbox_query_snapshot entry.(TskState) current message) entry).
  { split; [reflexivity|]. exists current, message; repeat split; assumption || reflexivity. }
  Exists (mbox_query_snapshot entry.(TskState) current message).
  unfold mbox_query_output_fields_rep.
  cbn [mbox_query_snapshot mbox_query_wait_group mbox_query_wait_rows mbox_query_message].
  entailer!.
  entailer!.
Qed.

