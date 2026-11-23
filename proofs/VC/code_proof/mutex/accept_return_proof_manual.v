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
From Ucos2Verify.VC.code.mutex Require Import accept_return_goal.
From Ucos2Verify.VC.code.mutex Require Import accept_return_proof_auto_checked.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_accept_return_spec.
Local Open Scope sac.

Lemma proof_of_OSMutexAccept_safety_wit_5 : OSMutexAccept_safety_wit_5.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  prop_apply_p (store_ushort_range (&(pe # "os_event" ->ₛ "OSEventCnt")) cnt).
  entailer!.
Qed.

Lemma proof_of_OSMutexAccept_entail_wit_1 : OSMutexAccept_entail_wit_1.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  prop_apply_p (store_uchar_range (&(pe # "os_event" ->ₛ "OSEventType")) (event_slot_type_value (EventState before) eid)).
  entailer!.
Qed.

Lemma proof_of_OSMutexAccept_entail_wit_2 : OSMutexAccept_entail_wit_2.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  prop_apply_p (store_uchar_range (&("OSIntNesting")) isr).
  entailer!.
Qed.

Lemma proof_of_OSMutexAccept_entail_wit_3_1 : OSMutexAccept_entail_wit_3_1.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  prop_apply_p (store_uchar_range (&("pcp")) (Z.shiftr cnt 8)).
  prop_apply_p (store_uint_range (&("cpu_sr")) retval).
  Intros.
  match goal with Hrange : 0 <= Z.shiftr cnt 8 <= Byte.max_unsigned |- _ =>
    change (0 <= Z.shiftr cnt 8 <= 255) in Hrange end.
  match goal with Hrange : 0 <= retval <= Int.max_unsigned |- _ =>
    change (0 <= retval <= 4294967295) in Hrange end.
  assert (Hcast : unsigned_last_nbits (Z.shiftr cnt 8) 32 = Z.shiftr cnt 8).
  { apply mutex_accept_u32_of_byte; lia. }
  assert (Hcode : mutex_accept_pcp_code (Z.shiftr cnt 8) (curPrio task) = 0).
  { apply mutex_accept_pcp_code_none; left; congruence. }
  entailer!.
Qed.

Lemma proof_of_OSMutexAccept_entail_wit_3_2 : OSMutexAccept_entail_wit_3_2.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  prop_apply_p (store_uint_range (&("cpu_sr")) retval).
  assert (Hcode : mutex_accept_pcp_code (Z.shiftr cnt 8) (curPrio task) = 0).
  { apply mutex_accept_pcp_code_none; right; lia. }
  entailer!.
Qed.

Lemma proof_of_OSMutexAccept_return_wit_1 : OSMutexAccept_return_wit_1.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  assert (Hprogram : mutex_accept_public_program critical sg invocation pe before (0, 0) entry).
  { left; eapply (mutex_accept_call_protected_return critical sg invocation pe before eid observed mask retval entry current); try eassumption; lia. }
  sep_apply_l_atomic (mutex_accept_call_return_complete environment platform critical saved_local sg context
    invocation origin mask pe before 0 0 entry X Hprogram ltac:(auto) ltac:(assumption)).
  Intros after.
  Exists 0 after; unfold mutex_accept_return_post_prop.
  assert (Htruep : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  repeat sep_apply_l_atomic Htruep.
  subst pd; entailer!.
Qed.

Lemma proof_of_OSMutexAccept_return_wit_2 : OSMutexAccept_return_wit_2.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  assert (Hprogram : mutex_accept_public_program critical sg invocation pe before (120, 1) (mutex_accept_owned_state entry eid current m tid (curPrio task))).
  { left; eapply (mutex_accept_call_protected_return critical sg invocation pe before eid observed mask retval entry current); try eassumption; lia. }
  sep_apply_l_atomic (mutex_accept_call_return_complete environment platform critical saved_local sg context
    invocation origin mask pe before 120 1 (mutex_accept_owned_state entry eid current m tid (curPrio task)) X Hprogram ltac:(auto) ltac:(assumption)).
  Intros after.
  Exists 120 after; unfold mutex_accept_return_post_prop.
  assert (Htruep : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  repeat sep_apply_l_atomic Htruep.
  subst pd; entailer!.
Qed.

Lemma proof_of_OSMutexAccept_return_wit_3 : OSMutexAccept_return_wit_3.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  assert (Hprogram : mutex_accept_public_program critical sg invocation pe before (0, 1) (mutex_accept_owned_state entry eid current m tid (curPrio task))).
  { left; eapply (mutex_accept_call_protected_return critical sg invocation pe before eid observed mask retval entry current); try eassumption; lia. }
  sep_apply_l_atomic (mutex_accept_call_return_complete environment platform critical saved_local sg context
    invocation origin mask pe before 0 1 (mutex_accept_owned_state entry eid current m tid (curPrio task)) X Hprogram ltac:(auto) ltac:(assumption)).
  Intros after.
  Exists 0 after; unfold mutex_accept_return_post_prop.
  assert (Htruep : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  repeat sep_apply_l_atomic Htruep.
  subst pd; entailer!.
Qed.

Lemma proof_of_OSMutexAccept_return_wit_4 : OSMutexAccept_return_wit_4.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  assert (Hprogram : mutex_accept_public_program critical sg invocation pe before (0, 1) (mutex_accept_owned_state entry eid current m tid (curPrio task))).
  { left; eapply (mutex_accept_call_protected_return critical sg invocation pe before eid observed mask retval entry current); try eassumption; lia. }
  sep_apply_l_atomic (mutex_accept_call_return_complete environment platform critical saved_local sg context
    invocation origin mask pe before 0 1 (mutex_accept_owned_state entry eid current m tid (curPrio task)) X Hprogram ltac:(auto) ltac:(assumption)).
  Intros after.
  Exists 0 after; unfold mutex_accept_return_post_prop.
  assert (Htruep : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  repeat sep_apply_l_atomic Htruep.
  subst pd; entailer!.
Qed.

Lemma proof_of_OSMutexAccept_return_wit_5 : OSMutexAccept_return_wit_5.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  assert (Htype : eventType observed = OS_EVENT_TYPE_MUTEX).
  { apply mutex_accept_encoded_type_is_mutex; assumption. }
  assert (Hprogram : mutex_accept_public_program critical sg invocation pe before (2, 0) before).
  { left; eapply mutex_accept_call_isr_return; try eassumption; lia. }
  assert (Hreturn : mutex_accept_return_program critical sg invocation pe before (2, 0) before).
  { eapply mutex_accept_return_early; [exact Hprogram | lia | lia]. }
  assert (Hsafe : safeExec (LastSeen before) (return 0) X).
  { eapply mutex_accept_return_safe_return; eassumption. }
  Exists 2 before; unfold mutex_accept_return_post_prop.
  assert (Htruep : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  repeat sep_apply_l_atomic Htruep.
  subst pd; entailer!.
Qed.

Lemma proof_of_OSMutexAccept_return_wit_6 : OSMutexAccept_return_wit_6.
Proof.
  pre_process.
  assert (Hinput : mutex_accept_public_input critical sg invocation pe before eid observed) by assumption.
  destruct (mutex_accept_public_input_slot critical sg invocation pe before eid observed Hinput ltac:(lia))
    as [Haddr [Hid [Hslot Hprotocol]]].
  assert (Hprogram : mutex_accept_public_program critical sg invocation pe before (1, 0) before).
  { eapply mutex_accept_public_wrong_type_return; try eassumption; lia. }
  assert (Hreturn : mutex_accept_return_program critical sg invocation pe before (1, 0) before).
  { eapply mutex_accept_return_early; [exact Hprogram | lia | lia]. }
  assert (Hsafe : safeExec (LastSeen before) (return 0) X).
  { eapply mutex_accept_return_safe_return; eassumption. }
  Exists 1 before; unfold mutex_accept_return_post_prop.
  assert (Htruep : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  repeat sep_apply_l_atomic Htruep.
  subst pd; entailer!.
Qed.

Lemma proof_of_OSMutexAccept_return_wit_7 : OSMutexAccept_return_wit_7.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  assert (Hprogram : mutex_accept_public_program critical sg invocation pe before (4, 0) before).
  { replace pe with 0 by lia; left; apply mutex_accept_call_null_return. }
  assert (Hreturn : mutex_accept_return_program critical sg invocation pe before (4, 0) before).
  { eapply mutex_accept_return_early; [exact Hprogram | lia | lia]. }
  assert (Hsafe : safeExec (LastSeen before) (return 0) X).
  { eapply mutex_accept_return_safe_return; eassumption. }
  Exists 4 before; unfold mutex_accept_return_post_prop.
  assert (Htruep : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  repeat sep_apply_l_atomic Htruep.
  subst pd; entailer!.
Qed.

Lemma proof_of_OSMutexAccept_return_wit_8 : OSMutexAccept_return_wit_8.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  assert (Hprogram : mutex_accept_public_program critical sg invocation pe before (4, 0) before).
  { replace pe with 0 by lia; left; apply mutex_accept_call_null_return. }
  assert (Hreturn : mutex_accept_return_program critical sg invocation pe before (4, 0) before).
  { eapply mutex_accept_return_early; [exact Hprogram | lia | lia]. }
  assert (Hsafe : safeExec (LastSeen before) (return 0) X).
  { eapply mutex_accept_return_safe_return; eassumption. }
  Exists 4 before; unfold mutex_accept_return_post_prop.
  assert (Htruep : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  repeat sep_apply_l_atomic Htruep.
  subst pd; entailer!.
Qed.

Lemma proof_of_OSMutexAccept_partial_solve_wit_8_pure : OSMutexAccept_partial_solve_wit_8_pure.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  prop_apply_p (store_ushort_range (&(pe # "os_event" ->ₛ "OSEventCnt")) cnt).
  Intros.
  assert (Hcast : unsigned_last_nbits (Z.shiftr cnt 8) 8 = Z.shiftr cnt 8).
  { apply mutex_accept_high_byte_cast; lia. }
  entailer!.
Qed.

Lemma proof_of_OSMutexAccept_partial_solve_wit_9_pure : OSMutexAccept_partial_solve_wit_9_pure.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  prop_apply_p (store_uchar_range ((tcb_field_address (task_slot_addr sg tid) TCBPrio)) (curPrio task)).
  prop_apply_p (store_uchar_range (&("pcp")) (Z.shiftr cnt_2 8)).
  Intros.
  match goal with Hrange : 0 <= curPrio task <= Byte.max_unsigned |- _ =>
    change (0 <= curPrio task <= 255) in Hrange end.
  match goal with Hrange : 0 <= Z.shiftr cnt_2 8 <= Byte.max_unsigned |- _ =>
    change (0 <= Z.shiftr cnt_2 8 <= 255) in Hrange end.
  assert (Hprio : unsigned_last_nbits (curPrio task) 16 = curPrio task).
  { apply mutex_accept_u16_of_byte; lia. }
  assert (Hpcp : unsigned_last_nbits (Z.shiftr cnt_2 8) 32 = Z.shiftr cnt_2 8).
  { apply mutex_accept_u32_of_byte; lia. }
  rewrite Hprio; entailer!; congruence.
Qed.

Lemma proof_of_OSMutexAccept_partial_solve_wit_11_pure : OSMutexAccept_partial_solve_wit_11_pure.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  prop_apply_p (store_uchar_range ((tcb_field_address (task_slot_addr sg tid) TCBPrio)) (curPrio task)).
  Intros.
  match goal with Hrange : 0 <= curPrio task <= Byte.max_unsigned |- _ =>
    change (0 <= curPrio task <= 255) in Hrange end.
  assert (Hprio : unsigned_last_nbits (curPrio task) 16 = curPrio task).
  { apply mutex_accept_u16_of_byte; lia. }
  rewrite Hprio; entailer!; congruence.
Qed.

Lemma proof_of_OSMutexAccept_partial_solve_wit_12_pure : OSMutexAccept_partial_solve_wit_12_pure.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  prop_apply_p (store_uchar_range ((tcb_field_address (task_slot_addr sg tid) TCBPrio)) (curPrio task)).
  Intros.
  match goal with Hrange : 0 <= curPrio task <= Byte.max_unsigned |- _ =>
    change (0 <= curPrio task <= 255) in Hrange end.
  assert (Hprio : unsigned_last_nbits (curPrio task) 16 = curPrio task).
  { apply mutex_accept_u16_of_byte; lia. }
  rewrite Hprio; entailer!; congruence.
Qed.

Lemma proof_of_OSMutexAccept_which_implies_wit_1 : OSMutexAccept_which_implies_wit_1.
Proof.
  pre_process.
  assert (Hinput : mutex_accept_public_input critical sg invocation pe before eid observed) by assumption.
  destruct (mutex_accept_public_input_slot critical sg invocation pe before eid observed Hinput PreH1)
    as [Haddr [Hid [Hslot Hprotocol]]].
  assert (Hlayout : event_core_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventType")) (&(pe # "os_event" ->ₛ "OSEventPtr"))
    (&(pe # "os_event" ->ₛ "OSEventCnt"))) by assumption.
  rewrite mutex_accept_closed_equiv.
  sep_apply_l_atomic (sem_query_type_split_full sg before eid observed Hslot).
  pose proof Hlayout as [Htypeaddr _]; rewrite Htypeaddr in Hlayout |- *.
  entailer!.
  assert (Htruep : (TT ** TT) --||-- TT).
  { split; [apply derivable1_truep_intros|].
    apply sepcon_cancel_res_emp; apply derivable1_truep_intros. }
  repeat rewrite Htruep; apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexAccept_which_implies_wit_2 : OSMutexAccept_which_implies_wit_2.
Proof.
  pre_process.
  assert (Htruep_merge : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  repeat sep_apply_l_atomic Htruep_merge.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  match goal with Hlayout : event_core_fields_layout_prop _ _ _ _ _ |- _ =>
    destruct Hlayout as [Htypeaddr _]; rewrite Htypeaddr end.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid Hvalid).
  rewrite mutex_accept_closed_equiv; entailer!.
Qed.

Lemma proof_of_OSMutexAccept_which_implies_wit_3 : OSMutexAccept_which_implies_wit_3.
Proof.
  pre_process.
  assert (Htruep_merge : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  assert (Htruep_equiv : (TT ** TT) --||-- TT).
  { split; [exact Htruep_merge|].
    apply sepcon_cancel_res_emp; apply derivable1_truep_intros. }
  repeat sep_apply_l_atomic Htruep_merge.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  assert (Hslot : sem_query_public_slot before eid observed) by assumption.
  destruct (mutex_accept_public_slot_is_mutex before eid observed Hslot ltac:(assumption))
    as [Hlookup Htype].
  assert (Hencoded : encode_event_type (eventType observed) = 4) by (rewrite Htype; reflexivity).
  assert (Hlayout : event_core_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventType")) (&(pe # "os_event" ->ₛ "OSEventPtr"))
    (&(pe # "os_event" ->ₛ "OSEventCnt"))) by assumption.
  pose proof Hlayout as [Htypeaddr _]; rewrite Htypeaddr in Hlayout |- *.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid Hvalid).
  sep_apply_l_atomic (mutex_accept_interrupt_split_full sg before).
  assert (Haddr : os_int_nesting_addr sg (&("OSIntNesting"))) by assumption.
  assert (Hisr : isr = intNesting (IntrState before)) by assumption.
  unfold os_int_nesting_addr in Haddr; rewrite Haddr, Hisr.
  unfold mutex_accept_interrupt_frame, os_int_nesting_addr; entailer!.
  all: try solve [repeat rewrite Htruep_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSMutexAccept_which_implies_wit_4 : OSMutexAccept_which_implies_wit_4.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  assert (Htruep_merge : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  repeat sep_apply_l_atomic Htruep_merge.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  assert (Haddr : os_int_nesting_addr sg (&("OSIntNesting"))) by assumption.
  unfold os_int_nesting_addr in Haddr; rewrite Haddr.
  rewrite PreH1; unfold mutex_accept_interrupt_frame.
  sep_apply_l_atomic (mutex_accept_interrupt_merge_full sg before (intNesting (IntrState before)) Hvalid eq_refl).
  rewrite mutex_accept_closed_equiv; entailer!.
Qed.

Lemma proof_of_OSMutexAccept_which_implies_wit_5 : OSMutexAccept_which_implies_wit_5.
Proof.
  pre_process.
  assert (Htruep_merge : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  assert (Htruep_equiv : (TT ** TT) --||-- TT).
  { split; [exact Htruep_merge|].
    apply sepcon_cancel_res_emp; apply derivable1_truep_intros. }
  repeat sep_apply_l_atomic Htruep_merge.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  assert (Hinput : mutex_accept_public_input critical sg invocation pe before eid observed) by assumption.
  destruct (mutex_accept_public_input_slot critical sg invocation pe before eid observed Hinput ltac:(lia))
    as [Hpe [Hid [Hslot Hprotocol]]].
  assert (Hlookup : mutex_accept_lookup before eid observed) by assumption.
  assert (Htype : event_slot_type_value (EventState before) eid = 4).
  { unfold event_slot_type_value; unfold mutex_accept_lookup in Hlookup; rewrite Hlookup; assumption. }
  assert (Hhandle : mutex_accept_handle_protocol critical sg invocation eid).
  { apply Hprotocol; [exact Htype|lia]. }
  assert (Hsource : kernel_call_task_source context before).
  { match goal with H : mutex_accept_call_admission _ _ _ _ |- _ =>
      apply H; [lia|exact Htype|lia] end. }
  assert (Haddr : os_int_nesting_addr sg (&("OSIntNesting"))) by assumption.
  assert (Hisr : isr = intNesting (IntrState before)) by assumption.
  unfold os_int_nesting_addr in Haddr; rewrite Haddr.
  rewrite Hisr; unfold mutex_accept_interrupt_frame.
  sep_apply_l_atomic (mutex_accept_interrupt_merge_full sg before (intNesting (IntrState before)) Hvalid eq_refl); entailer!.
  all: try solve [repeat rewrite Htruep_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSMutexAccept_which_implies_wit_6 : OSMutexAccept_which_implies_wit_6.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  assert (Htruep_merge : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  assert (Htruep_equiv : (TT ** TT) --||-- TT).
  { split; [exact Htruep_merge|].
    apply sepcon_cancel_res_emp; apply derivable1_truep_intros. }
  repeat sep_apply_l_atomic Htruep_merge.
  assert (Hfacts : mutex_accept_acquire_facts critical sg invocation eid mask cpu_sr before entry_2 observed current_2) by assumption.
  pose proof Hfacts as [_ [Hvalid [_ [_ [Hlookup [_ [Htype _]]]]]]].
  sep_apply_l_atomic (mutex_accept_event_fields_split_full sg entry_2 eid current_2 Hlookup Htype).
  Intros m.
  Exists m (encode_event_cnt_value current_2) (encode_event_ptr_value sg current_2) entry_2 current_2.
  assert (Hlayout : event_core_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventType")) (&(pe # "os_event" ->ₛ "OSEventPtr"))
    (&(pe # "os_event" ->ₛ "OSEventCnt"))) by assumption.
  pose proof Hlayout as [_ [Hptraddr Hcntaddr]]; rewrite Hptraddr, Hcntaddr in Hlayout |- *.
  entailer!.
  all: try solve [repeat rewrite Htruep_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSMutexAccept_which_implies_wit_7 : OSMutexAccept_which_implies_wit_7.
Proof.
  pre_process.
  assert (Hfacts : mutex_accept_call_acquire_facts critical sg invocation eid mask cpu_sr before entry_2 observed current_2) by assumption.
  destruct (proj2 Hfacts) as [tid [task Hcurrent]].
  sep_apply_l_atomic (mutex_accept_current_fields_split sg entry_2 eid current_2 tid task Hcurrent).
  Exists tid task m_2 cnt_2 ptr_2 entry_2 current_2.
  assert (Haddr : os_tcb_cur_addr sg (&("OSTCBCur"))) by assumption.
  unfold os_tcb_cur_addr in Haddr; rewrite Haddr.
  cbn [tcb_field_address]; entailer!.
  apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexAccept_which_implies_wit_8 : OSMutexAccept_which_implies_wit_8.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  assert (Htruep_merge : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  assert (Htruep_equiv : (TT ** TT) --||-- TT).
  { split; [exact Htruep_merge|].
    apply sepcon_cancel_res_emp; apply derivable1_truep_intros. }
  repeat sep_apply_l_atomic Htruep_merge.
  assert (Hfacts : mutex_accept_acquire_facts critical sg invocation eid mask cpu_sr before entry observed current) by assumption.
  assert (Hsnapshot : mutex_accept_event_snapshot sg entry eid current m cnt ptr) by assumption.
  assert (Hcurrent : mutex_accept_current_task sg entry tid task) by assumption.
  pose proof Hfacts as [_ [Hvalid _]].
  pose proof Hsnapshot as [Hlookup [Htype [Hm [Hcount Hptr]]]].
  pose proof Hcurrent as [Hcur [Htask Hbounds]].
  destruct (mutex_accept_available_snapshot sg entry eid current m cnt ptr Hvalid Hsnapshot PreH2)
    as [Hnone [Horig [Hencoded Hpcprange]]].
  prop_apply_p (store_uchar_range (tcb_field_address (task_slot_addr sg tid) TCBPrio) (curPrio task)).
  Intros.
  match goal with Hrange : 0 <= curPrio task <= Byte.max_unsigned |- _ =>
    change (0 <= curPrio task <= 255) in Hrange end.
  assert (Hcntrange : 0 <= cnt <= 65535) by lia.
  assert (Hprange : 0 <= curPrio task <= 255) by lia.
  assert (Hcast : unsigned_last_nbits (Z.shiftr cnt 8) 8 = Z.shiftr cnt 8)
    by (apply mutex_accept_high_byte_cast; exact Hcntrange).
  assert (Hbits : Z.lor (Z.land cnt 65280) (curPrio task) = mfPCP m * 256 + curPrio task).
  { rewrite mutex_accept_replace_low_byte; lia. }
  assert (Hresult : mutex_accept_protected_result sg eid entry current 120 1
    (mutex_accept_owned_state entry eid current m tid (curPrio task))).
  { exists m; split; [exact Hm|]; right; split; [rewrite <- Hcount; exact PreH2|].
    exists tid, task; split; [exact Hcur|]; split; [exact Htask|].
    split; [reflexivity|]; split; [reflexivity|].
    left; repeat split; try reflexivity; unfold decode_PCP_from_cnt; rewrite <- Hcount, Hcast, <- PreH3; assumption. }
  match goal with Hlayout : event_core_fields_layout_prop _ _ _ _ _ |- _ =>
    destruct Hlayout as [_ [Hptraddr Hcntaddr]]; rewrite Hptraddr, Hcntaddr end.
  assert (Haddr : os_tcb_cur_addr sg (&("OSTCBCur"))) by assumption.
  unfold os_tcb_cur_addr in Haddr; rewrite Haddr, Hbits.
  sep_apply_l_atomic (mutex_accept_acquire_merge_full sg entry eid current m tid task
    Hvalid Hlookup Htype Hm Hnone Hcurrent).
  rewrite <- (mutex_accept_call_support_event_update environment saved_local sg context
    entry eid current m tid (curPrio task)).
  entailer!.
  all: try solve [repeat rewrite Htruep_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSMutexAccept_which_implies_wit_9 : OSMutexAccept_which_implies_wit_9.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  assert (Htruep_merge : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  assert (Htruep_equiv : (TT ** TT) --||-- TT).
  { split; [exact Htruep_merge|].
    apply sepcon_cancel_res_emp; apply derivable1_truep_intros. }
  repeat sep_apply_l_atomic Htruep_merge.
  assert (Hfacts : mutex_accept_acquire_facts critical sg invocation eid mask cpu_sr before entry observed current) by assumption.
  assert (Hsnapshot : mutex_accept_event_snapshot sg entry eid current m cnt ptr) by assumption.
  assert (Hcurrent : mutex_accept_current_task sg entry tid task) by assumption.
  pose proof Hfacts as [_ [Hvalid _]].
  pose proof Hsnapshot as [Hlookup [Htype [Hm [Hcount Hptr]]]].
  pose proof Hcurrent as [Hcur [Htask Hbounds]].
  destruct (mutex_accept_available_snapshot sg entry eid current m cnt ptr Hvalid Hsnapshot PreH2)
    as [Hnone [Horig [Hencoded Hpcprange]]].
  prop_apply_p (store_uchar_range (tcb_field_address (task_slot_addr sg tid) TCBPrio) (curPrio task)).
  Intros.
  match goal with Hrange : 0 <= curPrio task <= Byte.max_unsigned |- _ =>
    change (0 <= curPrio task <= 255) in Hrange end.
  assert (Hcntrange : 0 <= cnt <= 65535) by lia.
  assert (Hprange : 0 <= curPrio task <= 255) by lia.
  assert (Hcast : unsigned_last_nbits (Z.shiftr cnt 8) 8 = Z.shiftr cnt 8)
    by (apply mutex_accept_high_byte_cast; exact Hcntrange).
  assert (Hbits : Z.lor (Z.land cnt 65280) (curPrio task) = mfPCP m * 256 + curPrio task).
  { rewrite mutex_accept_replace_low_byte; lia. }
  assert (Hresult : mutex_accept_protected_result sg eid entry current 0 1
    (mutex_accept_owned_state entry eid current m tid (curPrio task))).
  { exists m; split; [exact Hm|]; right; split; [rewrite <- Hcount; exact PreH2|].
    exists tid, task; split; [exact Hcur|]; split; [exact Htask|].
    split; [reflexivity|]; split; [reflexivity|].
    right; split; [|reflexivity]; unfold decode_PCP_from_cnt; rewrite <- Hcount, Hcast, <- PreH3; apply mutex_accept_pcp_code_none_inv; exact PreH4. }
  match goal with Hlayout : event_core_fields_layout_prop _ _ _ _ _ |- _ =>
    destruct Hlayout as [_ [Hptraddr Hcntaddr]]; rewrite Hptraddr, Hcntaddr end.
  assert (Haddr : os_tcb_cur_addr sg (&("OSTCBCur"))) by assumption.
  unfold os_tcb_cur_addr in Haddr; rewrite Haddr, Hbits.
  sep_apply_l_atomic (mutex_accept_acquire_merge_full sg entry eid current m tid task
    Hvalid Hlookup Htype Hm Hnone Hcurrent).
  rewrite <- (mutex_accept_call_support_event_update environment saved_local sg context
    entry eid current m tid (curPrio task)).
  entailer!.
  all: try solve [repeat rewrite Htruep_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSMutexAccept_which_implies_wit_10 : OSMutexAccept_which_implies_wit_10.
Proof.
  pre_process.
  unfold mutex_accept_call_acquire_facts in *.
  repeat match goal with
  | H : mutex_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H
  end.
  assert (Htruep_merge : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  assert (Htruep_equiv : (TT ** TT) --||-- TT).
  { split; [exact Htruep_merge|].
    apply sepcon_cancel_res_emp; apply derivable1_truep_intros. }
  repeat sep_apply_l_atomic Htruep_merge.
  assert (Hfacts : mutex_accept_acquire_facts critical sg invocation eid mask cpu_sr before entry observed current) by assumption.
  assert (Hsnapshot : mutex_accept_event_snapshot sg entry eid current m cnt ptr) by assumption.
  pose proof Hfacts as [_ [Hvalid _]].
  pose proof Hsnapshot as [Hlookup [Htype [Hm [Hcnt Hptr]]]].
  assert (Hresult : mutex_accept_protected_result sg eid entry current 0 0 entry).
  { exists m; split; [exact Hm|]; left; split; [congruence|auto]. }
  match goal with Hlayout : event_core_fields_layout_prop _ _ _ _ _ |- _ =>
    destruct Hlayout as [_ [Hptraddr Hcntaddr]]; rewrite Hptraddr, Hcntaddr end.
  sep_apply_l_atomic (mutex_accept_event_fields_merge_full sg entry eid current cnt ptr Hvalid Hlookup Hcnt Hptr).
  entailer!.
  all: try solve [repeat rewrite Htruep_equiv; apply derivable1_truep_intros].
Qed.
