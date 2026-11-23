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
From Ucos2Verify.VC.code.mbox Require Import mbox_accept_goal.
From Ucos2Verify.VC.code.mbox Require Import mbox_accept_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_accept_spec.
Import UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OSMboxAccept_entail_wit_1 : OSMboxAccept_entail_wit_1.
Proof.
  left; intros.
  assert (Hrange : 0 <= event_slot_type_value (EventState before) eid <= 255).
  { unfold event_slot_type_value.
    destruct (inUsedEventStates (EventState before) eid) as [e|].
    - destruct (eventType e); cbn; lia.
    - cbn; lia. }
  entailer!.
Qed.

Lemma proof_of_OSMboxAccept_return_wit_1 : OSMboxAccept_return_wit_1.
Proof.
  left; intros.
  pose proof (mbox_accept_restored_return critical sg invocation pe before
    entry_2 checkpoint (mbox_message_ptr m) after_2 PreH2 PreH1) as Hpost.
  pose proof (mbox_accept_safe_return critical sg invocation pe before
    (mbox_message_ptr m) after_2 X PreH25 Hpost) as Hsafe.
  Exists after_2; entailer!.
Qed.

Lemma proof_of_OSMboxAccept_return_wit_2 : OSMboxAccept_return_wit_2.
Proof.
  left; intros.
  pose proof (mbox_accept_wrong_type_return critical sg invocation pe before eid
    PreH7 PreH1 PreH9 PreH2) as Hpost.
  pose proof (mbox_accept_safe_return critical sg invocation pe before 0 before X
    PreH17 Hpost) as Hsafe.
  Exists before; entailer!.
Qed.

Lemma proof_of_OSMboxAccept_return_wit_3 : OSMboxAccept_return_wit_3.
Proof.
  left; intros.
  assert (Hpe : pe = 0) by lia.
  rewrite Hpe in *.
  pose proof (mbox_accept_null_return critical sg invocation before) as Hpost.
  pose proof (mbox_accept_safe_return critical sg invocation 0 before 0 before X
    PreH5 Hpost) as Hsafe.
  Exists before; entailer!.
Qed.

Lemma proof_of_OSMboxAccept_which_implies_wit_1 : OSMboxAccept_which_implies_wit_1.
Proof.
  left; intros.
  pose proof PreH3 as Hinput.
  destruct Hinput as [Hzero|[Hnonzero [Haddr [Hid [Hpublic Hprotocol]]]]];
    [contradiction|].
  pose proof PreH2 as [_ [_ [_ [_ [Htype Hptr]]]]].
  rewrite mutex_query_closed_equiv.
  sep_apply_l_atomic (mbox_accept_type_split_full sg before eid Hpublic).
  Intros.
  rewrite Htype, Haddr.
  rewrite Haddr in PreH3.
  entailer!.
Qed.

Lemma proof_of_OSMboxAccept_which_implies_wit_2 : OSMboxAccept_which_implies_wit_2.
Proof.
  left; intros.
  pose proof PreH2 as [_ [_ [_ [_ [Htype Hptr]]]]].
  rewrite Htype, PreH3, mutex_query_closed_equiv.
  sep_apply_l_atomic (mbox_accept_type_merge_full sg before eid PreH1).
  entailer!.
Qed.

Lemma proof_of_OSMboxAccept_which_implies_wit_3 : OSMboxAccept_which_implies_wit_3.
Proof.
  left; intros.
  pose proof PreH4 as Hinput.
  destruct Hinput as [Hzero|[Hnonzero [Haddr [Hid [Hpublic Hprotocol]]]]];
    [contradiction|].
  assert (Hsuccess : mbox_accept_success_input critical sg invocation pe before eid).
  { unfold mbox_accept_success_input.
    split; [exact Hnonzero|]. split; [exact Haddr|].
    split; [exact Hid|]. split; [exact PreH3|].
    split; [exact (Hprotocol PreH6)|].
    unfold event_slot_type_value in PreH6.
    destruct (inUsedEventStates (EventState before) eid) as [observed|] eqn:Hlookup;
      [|discriminate].
    exists observed; split; [exact Hlookup|].
    apply mbox_accept_encoded_type; exact PreH6. }
  pose proof PreH2 as [_ [_ [_ [_ [Htype Hptr]]]]].
  rewrite Htype, PreH5, mutex_query_closed_equiv.
  rewrite PreH5 in Hsuccess.
  sep_apply_l_atomic (mbox_accept_type_merge_full sg before eid PreH3).
  entailer!.
Qed.

Lemma proof_of_OSMboxAccept_which_implies_wit_4 : OSMboxAccept_which_implies_wit_4.
Proof.
  left; intros.
  destruct PreH2 as [Hnonzero [Haddr [Hid [Hbefore [Hprotocol
    [observed [Hobserved Hobserved_type]]]]]]].
  destruct (mutex_query_handle_interval_preserves_identity critical sg invocation
    eid before entry_2 observed Hprotocol PreH3 Hbefore Hobserved)
    as [current [Hcurrent [Hgeneration Hcurrent_type]]].
  rewrite Hobserved_type in Hcurrent_type.
  destruct (mbox_accept_current_payload sg entry_2 eid current PreH4 Hcurrent
    Hcurrent_type) as [m Hmessage].
  assert (Hacquired : mbox_accept_acquired critical sg invocation pe mask cpu_sr
    before entry_2 eid observed current m).
  { unfold mbox_accept_acquired; repeat first [assumption | split]. }
  pose proof PreH1 as [_ [_ [_ [_ [Htype Hptr]]]]].
  Exists entry_2 observed current m.
  unfold mbox_accept_message_frame.
  rewrite Hptr, Haddr, UCOS2_inv_split_event_queue.
  rewrite Haddr in Hacquired.
  Intros.
  sep_apply_l_atomic (event_raw_rep_split_eid sg (TskState entry_2)
    (EventState entry_2) eid current Hcurrent).
  sep_apply_l_atomic (mbox_rep_split_message sg (TskState entry_2) eid current m
    Hcurrent_type Hmessage).
  entailer!.
Qed.

Lemma proof_of_OSMboxAccept_which_implies_wit_5 : OSMboxAccept_which_implies_wit_5.
Proof.
  left; intros.
  unfold mbox_accept_message_frame; Intros.
  match goal with H : mbox_accept_acquired _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as [Hnonzero [Haddr [Hid [Hentry [Hsaved [Hobserved
      [Hobserved_type [Hinterval [Hcurrent [Hcurrent_type [Hgeneration Hmessage]]]]]]]]]]]
  end.
  assert (Htaken : mbox_accept_taken critical sg invocation pe before entry_2
    (mbox_accept_update entry_2 eid current m) pmsg).
  { split; [exact Hnonzero|]. exists eid, observed, current, m.
    repeat first [assumption | reflexivity | split]. }
  pose proof (mbox_accept_update_preserves_validity sg entry_2 eid current m
    Hentry Hcurrent Hcurrent_type) as Hcheckpoint.
  pose proof PreH2 as [_ [_ [_ [_ [Htype Hptr]]]]].
  Exists entry_2 (mbox_accept_update entry_2 eid current m).
  unfold mbox_accept_cpu_restore_pre.
  rewrite Hptr, PreH1.
  rewrite PreH1 in Htaken.
  sep_apply_l_atomic (mbox_accept_message_merge_updated sg entry_2 eid current m
    Hentry Hcurrent Hcurrent_type).
  entailer!.
Qed.

