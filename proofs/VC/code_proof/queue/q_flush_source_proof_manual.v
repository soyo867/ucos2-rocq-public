Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.Strings.String Coq.Lists.List.
Require Import Coq.micromega.Psatz.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From Ucos2Verify.VC.code.queue Require Import q_flush_source_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.VC.code.queue.spec.q_flush_call_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

Lemma proof_of_OSQFlush_entail_wit_1 : OSQFlush_entail_wit_1.
Proof.
  unfold OSQFlush_entail_wit_1; right; intros.
  unfold event_slot_type_value.
  destruct (before.(EventState).(inUsedEventStates) eid) as [e|];
    [destruct e.(eventType)|]; cbn [encode_event_type]; entailer!.
Qed.

Lemma proof_of_OSQFlush_return_wit_1 : OSQFlush_return_wit_1.
Proof.
  unfold OSQFlush_return_wit_1; left; intros.
  unfold q_flush_restore_post; Intros after.
  destruct H as [Hfacts Hinterval].
  assert (Hnonnull : pe <> 0) by congruence.
  pose proof (q_flush_call_success critical sg invocation pe before eid observed mask retval
    entry_2 current_2 Hnonnull PreH2 PreH6 Hfacts) as Hprotected.
  pose proof (q_flush_api_success critical sg invocation pe before
    (q_flush_state entry_2 eid current_2) after Hprotected Hinterval) as Hsem.
  pose proof (q_flush_api_safe_return critical sg invocation pe before 0
    after X Hsem PreH23) as Hsafe.
  Exists after; unfold q_flush_api_post; entailer!.
Qed.

Lemma proof_of_OSQFlush_return_wit_2 : OSQFlush_return_wit_2.
Proof.
  unfold OSQFlush_return_wit_2; left; intros; Intros.
  assert (Hnonnull : pe <> 0) by congruence.
  match goal with Hprofile : q_flush_profile sg, Hid : valid_event_id sg eid,
    Hvalid : UCOS2_state_inv sg before, Hslot : q_flush_public_slot before eid observed |- _ =>
    pose proof (q_flush_call_wrong_type critical sg invocation pe before eid observed
      Hnonnull PreH6 Hid Hslot PreH1) as Hprotected;
    pose proof (q_flush_api_error critical sg invocation pe before 1 before ltac:(lia) Hprotected) as Hsem;
    pose proof (q_flush_api_safe_return critical sg invocation pe before 1 before X Hsem PreH16) as Hsafe;
    rewrite PreH6 in Hsem;
    rewrite PreH6;
    sep_apply_l_atomic (q_flush_type_merge sg before eid Hprofile Hid Hvalid)
  end.
  Exists before; unfold q_flush_api_post; rewrite mutex_query_closed_equiv; entailer!.
Qed.

Lemma proof_of_OSQFlush_return_wit_3 : OSQFlush_return_wit_3.
Proof.
  unfold OSQFlush_return_wit_3; left; intros; Intros.
  assert (Hpe : pe = 0) by congruence; rewrite Hpe in *.
  pose proof (q_flush_call_null critical sg invocation before) as Hprotected.
  pose proof (q_flush_api_error critical sg invocation 0 before 4 before ltac:(lia) Hprotected) as Hsem.
  pose proof (q_flush_api_safe_return critical sg invocation 0 before 4 before X Hsem PreH5) as Hsafe.
  Exists before; unfold q_flush_api_post; entailer!.
Qed.

Lemma proof_of_OSQFlush_which_implies_wit_1 : OSQFlush_which_implies_wit_1.
Proof.
  unfold OSQFlush_which_implies_wit_1; left; intros; Intros.
  match goal with Hinput : q_flush_call_input critical sg invocation pe before eid observed,
    Hprofile : q_flush_profile sg |- _ =>
    pose proof Hinput as Hdomain;
    destruct Hdomain as [Hzero|[Hnonzero [Haddr [Hid [Hslot Hprotocol]]]]];
      [contradiction|];
    rewrite mutex_query_closed_equiv;
    sep_apply_l_atomic (sem_query_type_split_full sg before eid observed Hslot);
    subst pe; rewrite (q_flush_type_layout sg eid Hprofile Hid)
  end.
  unfold q_flush_type_frame; entailer!.
Qed.

Lemma proof_of_OSQFlush_which_implies_wit_2 : OSQFlush_which_implies_wit_2.
Proof.
  unfold OSQFlush_which_implies_wit_2; left; intros; Intros.
  match goal with Hinput : q_flush_call_input critical sg invocation pe before eid observed,
    Hprofile : q_flush_profile sg, Hid : valid_event_id sg eid,
    Hvalid : UCOS2_state_inv sg before, Hslot : q_flush_public_slot before eid observed |- _ =>
    destruct (q_flush_public_slot_is_queue before eid observed Hslot PreH8) as [Hlookup Htype];
    destruct Hinput as [Hzero|[Hnonzero [Haddr [Hid' [Hslot' Hprotocol]]]]];
      [contradiction|];
    specialize (Hprotocol PreH8);
    rewrite PreH6;
    sep_apply_l_atomic (q_flush_type_merge sg before eid Hprofile Hid Hvalid)
  end.
  unfold q_flush_save_pre; entailer!.
Qed.

Lemma proof_of_OSQFlush_which_implies_wit_3 : OSQFlush_which_implies_wit_3.
Proof.
  unfold OSQFlush_which_implies_wit_3; left; intros; Intros.
  rewrite PreH4.
  match goal with Hfacts : q_flush_acquire_facts _ _ _ _ _ _ _ _ _ _,
    Hprofile : q_flush_profile sg, Hid : valid_event_id sg eid |- _ =>
    sep_apply_l_atomic (q_flush_acquired_pointer_split platform critical sg invocation origin mask cpu_sr
      before entry_2 eid observed current_2 Hfacts Hprofile Hid)
  end.
  Intros q; Exists entry_2 current_2 q; entailer!.
Qed.

Lemma proof_of_OSQFlush_which_implies_wit_4 : OSQFlush_which_implies_wit_4.
Proof.
  unfold OSQFlush_which_implies_wit_4; left; intros; rewrite PreH1, PreH2.
  sep_apply_l_atomic (q_flush_pointer_to_stores platform critical sg invocation origin mask cpu_sr
    before entry_2 eid observed current_2 q_2).
  Intros free slots; Exists entry_2 current_2 free slots q_2.
  unfold q_flush_source_fields; entailer!.
Qed.

Lemma proof_of_OSQFlush_which_implies_wit_5 : OSQFlush_which_implies_wit_5.
Proof.
  unfold OSQFlush_which_implies_wit_5; left; intros.
  unfold q_flush_store_context; Intros.
  destruct H as [Hfacts [Hprofile [Hid Hbase]]]; subst pq.
  pose proof (q_flush_source_fields_merge_global sg entry_2 eid current_2 q free slots
    (q_flush_readonly_storage sg q slots) Hprofile) as Hmerge.
  unfold q_flush_source_fields in Hmerge; sep_apply_l_atomic Hmerge.
  Exists entry_2 current_2 (qcb_addr sg q.(qID)); unfold q_flush_restore_pre; entailer!.
Qed.
