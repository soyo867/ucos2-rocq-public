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
From Ucos2Verify.VC.code.queue Require Import q_pend_goal.
From Ucos2Verify.VC.code.queue Require Import q_pend_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.queue.spec.q_pend_api_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

Require Import Ucos2Verify.VC.code.queue.spec.q_accept_proof_helpers.
Require Import Ucos2Verify.VC.code.queue.spec.q_query_proof_helpers.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Import TaskStateDef.

Lemma proof_of_OSQPend_entail_wit_1 : OSQPend_entail_wit_1.
Proof.
  pre_process.
  prop_apply_p (store_uint_range (&( "timeout" )) timeout_pre).
  prop_apply_p (store_uchar_range (&(pe # "os_event" ->ₛ "OSEventType"))
    (event_slot_type_value before.(EventState) eid)); entailer!.
Qed.

Lemma proof_of_OSQPend_which_implies_wit_4 : OSQPend_which_implies_wit_4.
Proof.
  pre_process; unfold q_pend_save_output; Intros entered entry.
  match goal with H : q_pend_save_phase_observation _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hphase; destruct H as [Hhistory [Hsaved [current [Hfacts Hempty]]]] end.
  pose proof Hfacts as [_ [Hvalid [_ [_ [Hlookup [_ [Htype _]]]]]]].
  destruct (q_query_current_fields sg entry eid current Hvalid Hlookup Htype)
    as [q [Hq Hqvalid]].
  unfold q_pend_masked_frame.
  sep_apply_l_atomic (q_accept_pointer_split sg entry eid current q Hlookup Htype Hq).
  Intros.
  pose proof (q_pend_call_history_same_call _ _ _ _ _ _ _ _ Hhistory)
    as [Hinv [Horigin Hstack]].
  pose proof PreH1 as [_ [_ [Hevents Hqueues]]]; destruct (Hevents eid PreH2) as [Htypeaddr Hptr].
  rewrite PreH3, Hptr, Hinv, Horigin.
  Exists current q entered entry.
  unfold q_pend_first_owner, q_accept_pointer_context; entailer!.
Qed.

Lemma proof_of_OSQPend_which_implies_wit_12 : OSQPend_which_implies_wit_12.
Proof.
  pre_process; unfold q_pend_restore_output; Intros released unmasked.
  match goal with H : q_pend_call_history _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hhistory [[owned [Howned Hclients]] Hphase]] end.
  subst environment.
  assert (Hcheckpoint : q_pend_scheduling_checkpoint external (Some owned) critical sg context
    before entry eid ticks waiting released unmasked).
  { exists entered; split; assumption. }
  assert (Hadmitted : q_pend_sched_admitted (Some owned) critical) by (exists owned; auto).
  unfold sem_pend_continuation_save_input, sem_pend_optional_continuation_resources; Intros.
  match goal with H : task_stack_call_external _ = _ /\ _ |- _ =>
    destruct H as [Hexternal [Hplatform Hcoverage]] end.
  subst external platform.
  rewrite mutex_query_closed_equiv.
  Exists released unmasked.
  unfold q_pend_continuation_phase_sched_input, sem_pend_continuation_sched_input,
    os_sched_continuation_pre, kernel_continuation_call_closed,
    kernel_continuation_inv, task_tcb_init_continuation_capsules.
  rewrite kernel_program_inv_split_unmap.
  unfold kernel_call_execution_owned; entailer!.
Qed.

Lemma proof_of_OSQPend_which_implies_wit_13 : OSQPend_which_implies_wit_13.
Proof.
  pre_process; unfold q_pend_continuation_phase_sched_output; Intros scheduled selected.
  match goal with H : kernel_stack_call_same_call _ _ /\ _ |- _ =>
    destruct H as [Hsame [Hselected Hhistory]] end.
  destruct PreH1 as [entered Hreleased].
  assert (Hcheckpoint : q_pend_scheduled_checkpoint external environment critical sg context
    before eid ticks scheduled selected).
  { exists entered, entry, waiting, released, unmasked; auto. }
  Exists scheduled selected.
  unfold q_pend_save_input, q_pend_save_phase_pre; entailer!.
Qed.

Lemma proof_of_OSQPend_which_implies_wit_14 : OSQPend_which_implies_wit_14.
Proof.
  pre_process; unfold q_pend_save_output; Intros resumed resume_entry.
  match goal with H : q_pend_save_phase_observation _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as [Hhistory [Hsaved [Howned [Hwait [node Hnode]]]]] end.
  assert (Hcheckpoint : q_pend_resume_checkpoint external environment critical sg context
    before eid ticks resumed resume_entry).
  { exists scheduled, selected; auto. }
  pose proof Hnode as [Hvalid [Hcurrent [Hlookup Hrest]]].
  pose proof (q_pend_cleanup_split sg resume_entry context.(os_sched_call_stack).(stackLeaseSlot)
    node Hvalid Hcurrent Hlookup) as Hsplit.
  cbn [tcb_cell tcb_field_address] in Hsplit.
  sep_apply_l_atomic Hsplit.
  rewrite PreH2.
  Exists context.(os_sched_call_stack).(stackLeaseSlot) node resumed resume_entry; entailer!.
Qed.


Lemma proof_of_OSQPend_entail_wit_2 : OSQPend_entail_wit_2.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&( "OSIntNesting" )) before.(IntrState).(intNesting)); entailer!.
Qed.

Lemma proof_of_OSQPend_entail_wit_3 : OSQPend_entail_wit_3.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&( "OSLockNesting" )) before.(IntrState).(lockNesting)); entailer!.
Qed.

Lemma proof_of_OSQPend_entail_wit_4 : OSQPend_entail_wit_4.
Proof.
  pre_process.
  prop_apply_p (store_uint_range (&( "timeout" )) ticks); Intros.
  prop_apply_p (store_uint_range (&( "cpu_sr" )) retval); Intros.
  prop_apply_p (store_uint_range (&(((task_slot_addr sg tid)) # "os_tcb" ->ₛ "OSTCBDly")) old.(dly)); Intros.
  prop_apply_p (store_uchar_range (&(((task_slot_addr sg tid)) # "os_tcb" ->ₛ "OSTCBStat"))
    (encode_task_status old.(stat))); entailer!.
Qed.

Lemma proof_of_OSQPend_entail_wit_5_1 : OSQPend_entail_wit_5_1.
Proof.
  pre_process.
  pose proof (q_pend_resume_cleanup_ok sg resume_entry_2 eid resume_tid_2 node
    (encode_msg node.(msg)) PreH3 (eq_sym PreH66) eq_refl) as Hcleanup.
  Exists 0 resume_entry_2 resume_tid_2 node resumed_2 resume_entry_2; subst perr_pre; entailer!.
Qed.

Lemma proof_of_OSQPend_entail_wit_5_2 : OSQPend_entail_wit_5_2.
Proof.
  pre_process.
  pose proof (q_pend_resume_cleanup_abort sg resume_entry_2 eid resume_tid_2 node_2
    PreH3 (eq_sym PreH67)) as Hcleanup.
  Exists 14 resume_entry_2 resume_tid_2 node_2 resumed_2 resume_entry_2; subst perr_pre; entailer!.
Qed.

Lemma proof_of_OSQPend_partial_solve_wit_9_pure : OSQPend_partial_solve_wit_9_pure.
Proof.
  pre_process; unfold q_accept_next_out, Ucos2Verify.lib.event.sizeof_ptr;
  destruct (Z.eqb (queue_out_addr q + 4) (queue_end_addr q)) eqn:Hwrap;
  [apply Z.eqb_eq in Hwrap|apply Z.eqb_neq in Hwrap]; entailer!.
Qed.

Lemma proof_of_OSQPend_partial_solve_wit_10_pure : OSQPend_partial_solve_wit_10_pure.
Proof.
  pre_process; unfold q_accept_next_out, Ucos2Verify.lib.event.sizeof_ptr;
  destruct (Z.eqb (queue_out_addr q + 4) (queue_end_addr q)) eqn:Hwrap;
  [apply Z.eqb_eq in Hwrap|apply Z.eqb_neq in Hwrap]; entailer!.
Qed.

Lemma proof_of_OSQPend_partial_solve_wit_15_pure : OSQPend_partial_solve_wit_15_pure.
Proof.
  pre_process.
  match goal with H : os_sched_global_addresses _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as [_ [_ [_ [_ [_ [_ [_ [_ [Hgrp Htbl]]]]]]]]] end.
  entailer!.
Qed.

Lemma proof_of_OSQPend_which_implies_wit_1 : OSQPend_which_implies_wit_1.
Proof.
  pre_process.
  match goal with H : q_pend_api_input _ _ _ _ _ _ _ |- _ =>
    pose proof H as [Hzero|[_ [Haddr [Hid [Hslot Hprotocol]]]]] end; [contradiction|].
  unfold sem_pend_continuation_save_input; rewrite mutex_query_closed_equiv.
  change (sem_query_public_slot before eid observed) in Hslot.
  sep_apply_l_atomic (sem_query_type_split_full sg before eid observed Hslot).
  match goal with H : event_core_fields_layout_prop _ _ _ _ _ |- _ =>
    pose proof H as [Htype Hfields] end.
  rewrite Htype; entailer!; unfold event_core_fields_layout_prop in *; tauto.
Qed.

Lemma proof_of_OSQPend_which_implies_wit_2 : OSQPend_which_implies_wit_2.
Proof.
  pre_process.
  match goal with H : event_core_fields_layout_prop _ _ _ _ _ |- _ =>
    pose proof H as [Htype Hfields] end.
  rewrite Htype.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid PreH1).
  sep_apply_l_atomic (sem_pend_interrupt_split sg before).
  match goal with H : os_sched_global_addresses _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as [Hint [Hlock Hrest]] end.
  rewrite Htype in PreH3.
  rewrite Hint, Hlock in PreH2.
  rewrite Hint, Hlock; entailer!.
Qed.

Lemma proof_of_OSQPend_which_implies_wit_3 : OSQPend_which_implies_wit_3.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&( "OSIntNesting" )) before.(IntrState).(intNesting)); Intros.
  prop_apply_p (store_uchar_range (&( "OSLockNesting" )) before.(IntrState).(lockNesting)); Intros.
  assert (Hint0 : before.(IntrState).(intNesting) = 0) by lia.
  assert (Hlock0 : before.(IntrState).(lockNesting) = 0) by lia.
  assert (Hprefix : q_pend_api_prefix pe before eid).
  { unfold q_pend_api_prefix; rewrite Hint0, Hlock0, PreH5.
    split; [apply q_pend_precritical_clear; assumption|auto]. }
  pose proof PreH8 as [Hint [Hlock Hrest]]; rewrite Hint, Hlock in PreH8; rewrite Hint, Hlock.
  sep_apply_l_atomic (sem_pend_interrupt_merge sg before PreH1).
  unfold q_pend_save_input, q_pend_save_phase_pre, sem_pend_continuation_save_input.
  rewrite mutex_query_closed_equiv; entailer!.
Qed.

Lemma proof_of_OSQPend_which_implies_wit_5 : OSQPend_which_implies_wit_5.
Proof.
  pre_process.
  unfold q_accept_pointer_context; Intros.
  match goal with H : q_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hfacts [Hprofile [Hid Hq]]] end.
  pose proof Hfacts as [_ [Hvalid [_ [_ [Hlookup [_ [Htype _]]]]]]].
  destruct (q_query_current_fields sg entry_2 eid current_2 Hvalid Hlookup Htype) as [q0 [Hq0 Hqvalid]].
  assert (q0 = q_2) by congruence; subst q0.
  pose proof Hprofile as [_ [_ [Hevents Hqueues]]].
  destruct (Hevents eid Hid) as [Htypeaddr Hptr].
  rewrite PreH2, Hptr.
  sep_apply_l_atomic (q_accept_pointer_merge sg entry_2 eid current_2 q_2 Hvalid Hlookup Htype Hq).
  sep_apply_l_atomic (q_query_queue_split sg entry_2 eid current_2 q_2 Hlookup Hq).
  Intros free slots.
  pose proof Hqvalid as [Hqid _].
  sep_apply_l_atomic (proj1 (q_accept_qcb_cells_equiv sg pq q_2 PreH1 (Hqueues _ Hqid))).
  Exists current_2 free slots entered_2 entry_2 q_2.
  pose proof (queue_entries_in_range sg current_2.(waitList) q_2 Hqvalid) as Hbounds.
  unfold q_accept_store_context, q_accept_store_facts, q_accept_qcb_cells; entailer!.
Qed.

Lemma proof_of_OSQPend_which_implies_wit_6 : OSQPend_which_implies_wit_6.
Proof.
  pre_process.
  unfold q_accept_store_context; Intros.
  match goal with H : q_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hfacts Hstore] end.
  pose proof Hstore as [Hprofile [Hid [Hbase [Hq [Hqvalid [Hbinding [Hpart Hslots]]]]]]].
  assert (Hpop : exists message next, queue_dequeue_front q_2 = Some (message, next)).
  { unfold queue_dequeue_front; destruct q_2.(qMessages) as [|message rest] eqn:Hmessages; [|eauto].
    unfold queue_entries in PreH1; rewrite Hmessages, Zlength_nil in PreH1; lia. }
  destruct Hpop as [message [next Hpop]].
  sep_apply_l_atomic (queue_buffer_split_head sg current_2.(waitList) q_2 slots_2 message next Hqvalid Hpop).
  Intros.
  match goal with Hmodel : queue_slots_model q_2 slots_2 |- _ =>
    pose proof (queue_dequeue_front_head_slot sg current_2.(waitList) q_2 slots_2 message next Hqvalid Hmodel Hpop) as Hhead end.
  pose proof (queue_entries_in_range sg current_2.(waitList) q_2 Hqvalid) as Hbounds.
  Exists current_2 next free_2 slots_2 message entered_2 entry_2 q_2.
  unfold q_accept_dequeue_context, q_accept_store_context, q_accept_head_slot; entailer!.
Qed.

Lemma proof_of_OSQPend_which_implies_wit_7 : OSQPend_which_implies_wit_7.
Proof.
  pre_process.
  unfold q_accept_dequeue_context, q_accept_store_context, q_accept_head_slot; Intros.
  match goal with H : queue_dequeue_front _ = _ /\ _ |- _ => destruct H as [Hpop Hhead] end.
  match goal with H : q_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H as [Hfacts Hstore] end.
  match goal with H : 0 < queue_entries _ /\ _ |- _ => destruct H as [Hcount Hmodel] end.
  pose proof Hstore as [_ [_ [_ [_ [Hqvalid _]]]]].
  assert (Hqvalid' : q_query_queue_valid sg q_2) by (exists current_2.(waitList); exact Hqvalid).
  assert (Hread : q_query_read_message q_2 slots_2 message).
  { unfold q_query_read_message; rewrite (proj2 (Z.ltb_lt _ _) Hcount); exact Hhead. }
  pose proof (q_query_head_merge sg q_2 slots_2 message Hqvalid' Hcount Hread) as Hmerge.
  unfold q_query_head_slot in Hmerge.
  assert (Hmerge' : queue_out_addr q_2 # Ptr |-> message **
      PtrArray.mixed_missing_i q_2.(qStart) q_2.(qOutIndex) 0 q_2.(qSize) slots_2 |-- queue_buffer_rep q_2 slots_2).
  { sep_apply_r_atomic Hmerge; entailer!. }
  sep_apply_l_atomic Hmerge'.
  pose proof (queue_entries_in_range sg current_2.(waitList) q_2 Hqvalid) as Hbounds.
  Exists current_2 next_2 free_2 slots_2 entered_2 entry_2 q_2 message; entailer!.
Qed.

Lemma proof_of_OSQPend_which_implies_wit_10 : OSQPend_which_implies_wit_10.
Proof.
  pre_process.
  pose proof (proj1 (proj2 PreH1)) as Hentry.
  rewrite PreH2.
  pose proof (q_pend_wait_prefix_split_call sg entry eid current tid old ticks Hentry) as Hsplit.
  cbn [tcb_cell tcb_field_address] in Hsplit.
  sep_apply_l_atomic Hsplit; entailer!.
Qed.

Lemma proof_of_OSQPend_which_implies_wit_15 : OSQPend_which_implies_wit_15.
Proof.
  pre_process; unfold q_pend_masked_frame; rewrite PreH5.
  pose proof PreH1 as [Hvalid [_ [Hnode _]]].
  pose proof (sem_pend_task_priority_in_range sg resume_entry resume_tid node Hvalid Hnode) as Hpriority.
  rewrite Z.quot_div_nonneg by lia.
  sep_apply_l_atomic (q_pend_remove_call_cleanup_split external platform environment saved_local
    sg resumed resume_entry eid current resume_tid node PreH1 PreH2 PreH3 PreH4).
  Intros.
  Exists (event_task_remove_state resume_entry eid current resume_tid node) (task_set_event_ptr node None).
  cbn [task_set_event_ptr stat statPend eventPtr msg encode_event_link tcb_cell tcb_field_address]; entailer!.
Qed.

Lemma proof_of_OSQPend_which_implies_wit_16 : OSQPend_which_implies_wit_16.
Proof.
  pre_process.
  pose proof PreH1 as [Hvalid [_ [Hnode _]]].
  pose proof (sem_pend_task_priority_in_range sg resume_entry resume_tid node Hvalid Hnode) as Hpriority.
  rewrite Z.quot_div_nonneg by lia.
  destruct (q_pend_resume_timeout_lookup sg resume_entry eid resume_tid node PreH1 PreH2 PreH3)
    as [Htimeout [current [He Hin]]].
  pose proof (q_pend_resume_split_remove_call sg resume_entry eid resume_tid node current
    PreH1 He PreH4) as Hsplit.
  cbn [tcb_cell tcb_field_address] in Hsplit.
  sep_apply_l_atomic Hsplit.
  Exists current; entailer!.
Qed.

Lemma proof_of_OSQPend_which_implies_wit_17 : OSQPend_which_implies_wit_17.
Proof.
  pre_process.
  pose proof PreH1 as [Hentry Hresult].
  unfold q_pend_masked_frame; rewrite PreH3.
  pose proof (q_pend_cleanup_continuations_merge external platform environment saved_local
    sg resumed cleaning resume_tid node Hentry) as Hmerge.
  cbn [tcb_cell tcb_field_address] in Hmerge.
  sep_apply_l_atomic Hmerge.
  Exists (message_pend_cleanup_state sg cleaning resume_tid node).
  unfold q_pend_restore_input, q_pend_masked_frame; entailer!.
Qed.

Lemma proof_of_OSQPend_return_wit_7 : OSQPend_return_wit_7.
Proof.
  pre_process.
  assert (Hapi : q_pend_api_program external environment critical sg context pe eid ticks mask
    before (OS_ERR_PEVENT_NULL, 0) before).
  { apply q_pend_api_early_return; rewrite PreH12; apply q_pend_precritical_null. }
  assert (Hsafe : q_pend_return_safe before 0 OS_ERR_PEVENT_NULL X).
  { eapply q_pend_api_safe_return; eassumption. }
  unfold q_pend_api_post; Exists context before OS_ERR_PEVENT_NULL.
  unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call.
  cbn [encode_os_err_code]; subst perr_pre; entailer!.
Qed.

Lemma proof_of_OSQPend_return_wit_6 : OSQPend_return_wit_6.
Proof.
  pre_process.
  assert (Hapi : q_pend_api_program external environment critical sg context pe eid ticks mask
    before (OS_ERR_EVENT_TYPE, 0) before).
  { apply q_pend_api_early_return; apply q_pend_precritical_type; assumption. }
  assert (Hsafe : q_pend_return_safe before 0 OS_ERR_EVENT_TYPE X).
  { eapply q_pend_api_safe_return; eassumption. }
  pose proof PreH8 as [Htype Hfields]; rewrite Htype.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid PreH13).
  unfold q_pend_api_post; Exists context before OS_ERR_EVENT_TYPE.
  unfold sem_pend_continuation_save_input.
  rewrite mutex_query_closed_equiv.
  unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call.
  cbn [encode_os_err_code]; subst perr_pre; entailer!.
Qed.

Lemma proof_of_OSQPend_return_wit_5 : OSQPend_return_wit_5.
Proof.
  pre_process.
  assert (Hapi : q_pend_api_program external environment critical sg context pe eid ticks mask
    before (OS_ERR_PEND_ISR, 0) before).
  { apply q_pend_api_early_return; rewrite PreH7; apply q_pend_precritical_isr; lia. }
  assert (Hsafe : q_pend_return_safe before 0 OS_ERR_PEND_ISR X).
  { eapply q_pend_api_safe_return; eassumption. }
  pose proof PreH4 as [Hint [Hlock Hrest]]; rewrite Hint, Hlock.
  sep_apply_l_atomic (sem_pend_interrupt_merge sg before PreH6).
  unfold q_pend_api_post; Exists context before OS_ERR_PEND_ISR.
  unfold sem_pend_continuation_save_input; rewrite mutex_query_closed_equiv.
  unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call.
  cbn [encode_os_err_code]; subst perr_pre; entailer!.
Qed.

Lemma proof_of_OSQPend_return_wit_4 : OSQPend_return_wit_4.
Proof.
  pre_process.
  assert (Hint0 : before.(IntrState).(intNesting) = 0) by lia.
  assert (Hapi : q_pend_api_program external environment critical sg context pe eid ticks mask
    before (OS_ERR_PEND_LOCKED, 0) before).
  { apply q_pend_api_early_return; rewrite PreH10, Hint0; apply q_pend_precritical_locked; lia. }
  assert (Hsafe : q_pend_return_safe before 0 OS_ERR_PEND_LOCKED X).
  { eapply q_pend_api_safe_return; eassumption. }
  pose proof PreH7 as [Hint [Hlock Hrest]]; rewrite Hint, Hlock.
  sep_apply_l_atomic (sem_pend_interrupt_merge sg before PreH9).
  unfold q_pend_api_post; Exists context before OS_ERR_PEND_LOCKED.
  unfold sem_pend_continuation_save_input; rewrite mutex_query_closed_equiv.
  unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call.
  cbn [encode_os_err_code]; subst perr_pre; entailer!.
Qed.


Lemma proof_of_OSQPend_return_wit_2 : OSQPend_return_wit_2.
Proof.
  pre_process; unfold q_pend_restore_output; Intros returned after.
  match goal with H : q_pend_call_history _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hhistory _] end.
  assert (Hapi : q_pend_api_program external environment critical sg context pe eid ticks mask
    before (OS_ERR_NONE, message) after).
  { eapply q_pend_immediate_checkpoint_return; eassumption. }
  assert (Hsafe : q_pend_return_safe after message OS_ERR_NONE X).
  { eapply q_pend_api_safe_return; eassumption. }
  pose proof (q_pend_call_history_same_call _ _ _ _ _ _ _ _ (proj1 PreH1)) as Hfirst.
  pose proof (q_pend_call_history_same_call _ _ _ _ _ _ _ _ Hhistory) as Hlast.
  assert (Hsame : kernel_stack_call_same_call returned context).
  { clear - Hfirst Hlast.
    unfold kernel_stack_call_same_call in *; intuition congruence. }
  unfold q_pend_api_post; Exists returned after OS_ERR_NONE.
  cbn [encode_os_err_code]; subst perr_pre; entailer!.
Qed.

Lemma proof_of_OSQPend_return_wit_3 : OSQPend_return_wit_3.
Proof.
  pre_process; unfold q_pend_restore_output; Intros returned after.
  match goal with H : q_pend_call_history _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hhistory _] end.
  assert (Hapi : q_pend_api_program external environment critical sg context pe eid ticks mask
    before (OS_ERR_NONE, message) after).
  { eapply q_pend_immediate_checkpoint_return; eassumption. }
  assert (Hsafe : q_pend_return_safe after message OS_ERR_NONE X).
  { eapply q_pend_api_safe_return; eassumption. }
  pose proof (q_pend_call_history_same_call _ _ _ _ _ _ _ _ (proj1 PreH1)) as Hfirst.
  pose proof (q_pend_call_history_same_call _ _ _ _ _ _ _ _ Hhistory) as Hlast.
  assert (Hsame : kernel_stack_call_same_call returned context).
  { clear - Hfirst Hlast.
    unfold kernel_stack_call_same_call in *; intuition congruence. }
  unfold q_pend_api_post; Exists returned after OS_ERR_NONE.
  cbn [encode_os_err_code]; subst perr_pre; entailer!.
Qed.

Lemma proof_of_OSQPend_return_wit_1 : OSQPend_return_wit_1.
Proof.
  pre_process; unfold q_pend_restore_output; Intros returned after.
  match goal with H : q_pend_call_history _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hhistory _] end.
  destruct PreH1 as [error [Hcode Hresume]].
  assert (Hapi : q_pend_api_program external environment critical sg context pe eid ticks mask
    before (error, pmsg) after).
  { eapply q_pend_resume_checkpoint_return; eassumption. }
  assert (Hsafe : q_pend_return_safe after pmsg error X).
  { eapply q_pend_api_safe_return; eassumption. }
  pose proof (q_pend_call_history_same_call _ _ _ _ _ _ _ _ Hhistory) as Hlast.
  destruct PreH4 as [scheduled [selected [Hscheduled Hacquire]]].
  destruct Hscheduled as [entered [entry [waiting [released [unmasked [Hreleased Hschedule]]]]]].
  destruct Hreleased as [[Hfirst Hwait] Hrelease].
  pose proof (q_pend_call_history_same_call _ _ _ _ _ _ _ _ Hfirst) as Hsame1.
  pose proof (q_pend_call_history_same_call _ _ _ _ _ _ _ _ Hrelease) as Hsame2.
  pose proof (q_pend_call_history_same_call _ _ _ _ _ _ _ _ Hacquire) as Hsame3.
  destruct environment as [owned|]; [|contradiction].
  destruct Hschedule as [sched_entered [sched_entry [sched_resumed [sched_exit
    [Hsave [Hbody Hrestore]]]]]].
  pose proof (proj1 (proj2 Hsave)) as Hsame4.
  pose proof (proj1 (proj2 Hrestore)) as Hsame5.
  pose proof (os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hbody) as Hsamebody.
  assert (Hsame : kernel_stack_call_same_call returned context).
  { clear - Hsame1 Hsame2 Hsame3 Hsame4 Hsame5 Hsamebody Hlast.
    unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *;
      intuition congruence. }
  unfold q_pend_api_post; Exists returned after error; subst code; entailer!.
Qed.


Lemma proof_of_OSQPend_which_implies_wit_8 : OSQPend_which_implies_wit_8.
Proof.
  pre_process.
  unfold q_pend_first_owner, q_accept_dequeue_context, q_accept_store_context; Intros.
  match goal with H : queue_dequeue_front _ = _ /\ _ |- _ => destruct H as [Hpop Hhead] end.
  match goal with H : q_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hfacts Hstore] end.
  match goal with H : q_pend_save_phase_observation _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as [Hhistory [Hsaved Hacquire]] end.
  pose proof Hfacts as [_ [Hvalid [_ [_ [Hlookup [_ [Htype _]]]]]]].
  pose proof Hstore as [Hprofile [Hid [Hbase [Hq [Hqvalid [Hbinding [Hpart Hslots]]]]]]].
  pose proof Hqvalid as [Hqid _]; pose proof Hprofile as [_ [_ [_ Hqueues]]].
  pose proof (proj1 (q_accept_qcb_dequeue_equiv sg pq q Hbase (Hqueues _ Hqid))) as Hcells.
  unfold q_accept_qcb_cells in Hcells; sep_apply_l_atomic Hcells.
  assert (Hstore' : q_accept_store_facts sg entry_2 eid current q free slots (qcb_addr sg q.(qID)))
    by (rewrite <- Hbase; exact Hstore).
  sep_apply_l_atomic (q_accept_dequeue_merge sg entry_2 eid current q next message slots free
    Hvalid Hlookup Htype Hstore' Hpop).
  assert (Hcount : 0 < queue_entries q).
  { unfold queue_dequeue_front in Hpop; destruct q.(qMessages) eqn:Hmessages; [discriminate|].
    unfold queue_entries; rewrite Hmessages, Zlength_cons; pose proof (Zlength_nonneg l); lia. }
  assert (Hfirst : q_pend_first_critical sg eid ticks entry_2 (QueuePendImmediate message)
    (q_accept_after entry_2 eid current next slots)).
  { exists current, q; split; [exact Hlookup|]. split; [exact Hq|].
    rewrite (proj2 (Z.ltb_lt _ _) Hcount).
    exists message, next, slots; repeat split; assumption || reflexivity. }
  assert (Hcheckpoint : q_pend_immediate_checkpoint external environment critical sg context
    before entered_2 entry_2 eid ticks message (q_accept_after entry_2 eid current next slots)).
  { split; assumption. }
  pose proof (q_pend_call_history_same_call _ _ _ _ _ _ _ _ Hhistory) as [Hinv [Horigin Hstack]].
  Exists entered_2 entry_2 (q_accept_after entry_2 eid current next slots).
  unfold q_pend_restore_input, q_pend_masked_frame.
  rewrite Hinv, Horigin.
  unfold sem_pend_optional_continuation_resources, task_tcb_init_continuation_capsules;
    destruct environment; cbn [q_accept_after replace_EventS TskState]; entailer!.
Qed.

Lemma proof_of_OSQPend_which_implies_wit_9 : OSQPend_which_implies_wit_9.
Proof.
  pre_process.
  unfold q_pend_first_owner, q_accept_store_context; Intros.
  match goal with H : q_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hfacts Hstore] end.
  match goal with H : q_pend_save_phase_observation _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hphase; destruct H as [Hhistory [Hsaved [acquired [Hacquire Hempty]]]] end.
  pose proof Hfacts as [_ [Hvalid [_ [_ [Hlookup [_ [Htype _]]]]]]].
  pose proof Hacquire as [_ [_ [_ [_ [Hfound _]]]]].
  assert (acquired = current_2) by congruence; subst acquired.
  pose proof Hstore as [Hprofile [Hid [Hbase [Hq [Hqvalid [Hbinding [Hpart Hslots]]]]]]].
  destruct (Hempty q Hq PreH1) as [[owned [Howned Hclients]] [Hstage Hblocking]].
  pose proof Hstage as [Hsource [Hrunning [node [Hready [Hgeneration
    [Hnonidle [Hnull [Hmulti Hflag]]]]]]]].
  pose proof Hready as [Hnode [Hcur [Hprio [Hin Heffective]]]].
  pose proof (sched_current_ready_at_implies_current_consistency _ _ _ _ Hready) as Hcache.
  assert (Hentry : q_pend_wait_entry sg entry_2 eid current_2
    entered_2.(os_sched_call_stack).(stackLeaseSlot) node).
  { split; [exact Hvalid|]. split; [exact Hcur|]. split; [exact Hnode|].
    split; [exact Hlookup|]. split; [exact Htype|]. split; [exists q; auto|].
    split; [exact Hnonidle|]. split; [exact Hnull|]. split; [exact Hmulti|].
    split; [exact Hflag|]. split; assumption. }
  assert (Hsnapshot : q_pend_empty_snapshot external environment critical sg context entered_2
    mask cpu_sr pe before entry_2 eid observed current_2 entered_2.(os_sched_call_stack).(stackLeaseSlot) node).
  { split; [exact Hphase|]. split; [exact Hentry|]. split; [exact Hsource|].
    split; [exact Hcache|]. split; [exact Hblocking|]. exists owned; auto. }
  pose proof Hqvalid as [Hqid _]; pose proof Hprofile as [_ [_ [_ Hqueues]]].
  pose proof (proj2 (q_accept_qcb_cells_equiv sg pq q Hbase (Hqueues _ Hqid))) as Hcells.
  unfold q_accept_qcb_cells in Hcells; sep_apply_l_atomic Hcells.
  sep_apply_l_atomic (q_query_queue_merge sg entry_2 eid current_2 q free slots
    Hvalid Hbinding Hpart Hlookup Hq Hslots).
  pose proof (q_pend_wait_prefix_split sg entry_2 entered_2.(os_sched_call_stack).(stackLeaseSlot)
    node Hvalid Hcur Hnode) as Hsplit.
  cbn [tcb_cell tcb_field_address] in Hsplit; sep_apply_l_atomic Hsplit.
  pose proof (q_pend_call_history_same_call _ _ _ _ _ _ _ _ Hhistory) as [Hinv [Horigin Hstack]].
  subst environment; unfold sem_pend_optional_continuation_resources; Intros.
  match goal with H : task_stack_call_external _ = _ /\ _ |- _ =>
    pose proof H as [Hexternal [Hplatform Hcoverage]] end.
  Exists entered_2 entry_2 current_2 entered_2.(os_sched_call_stack).(stackLeaseSlot) node owned.
  unfold q_pend_masked_frame, sem_pend_optional_continuation_resources.
  rewrite Hinv, Horigin, PreH3; entailer!.
Qed.


Lemma proof_of_OSQPend_which_implies_wit_11 : OSQPend_which_implies_wit_11.
Proof.
  pre_process.
  pose proof PreH1 as [Hphase [Hentry [Hsource [Hcache [Hblocking Howned]]]]].
  pose proof Hphase as [Hhistory [Hsaved Hacquire]].
  pose proof (q_pend_call_history_same_call _ _ _ _ _ _ _ _ Hhistory) as Hsame.
  pose proof Hsame as [Hinv [Horigin Hstack]].
  pose proof Hentry as [Hvalid [Hcurrent [Hold [He [Htype [Hqueue [Hnonidle
    [Hnull [Hmulti [Hflag [Hready Hlayout]]]]]]]]]]].
  pose proof (q_pend_wait_entry_prio _ _ _ _ _ _ Hentry) as Hprio.
  destruct (q_pend_wait_entry_resource_conditions _ _ _ _ _ _ Hentry)
    as [Hkind [Hunavailable Hnotowner]].
  destruct (kernel_call_task_source_current_at entered entry Hsource)
    as [Hslot [found [Hfound Hgeneration]]].
  assert (Htid : tid = entered.(os_sched_call_stack).(stackLeaseSlot)) by congruence.
  assert (found = old) by (rewrite <- Htid in Hfound; congruence); subst found.
  assert (Hfirst : q_pend_first_critical sg eid ticks entry
    (QueuePendWaiting context.(os_sched_call_stack).(stackLeaseSlot)
      context.(os_sched_call_stack).(stackLeaseGeneration))
    (event_pend_state sg entry eid current tid old PendQ ticks)).
  { destruct Hqueue as [queue [Hq Hcount]].
    exists current, queue; split; [exact He|]. split; [exact Hq|].
    rewrite (proj2 (Z.ltb_ge _ _) Hcount); exists tid, old.
    split; [exact Hcurrent|]. split; [exact Hold|].
    split; [rewrite Htid, Hgeneration, Hstack; reflexivity|reflexivity]. }
  destruct (q_pend_event_wait_call_cut sg entered entry eid current tid old ticks
    Hvalid He Hcurrent Hold Hprio Hnull Hmulti Hflag Hready Hkind Hunavailable Hnotowner
    Hsource Hcache Hblocking PreH2) as [Hvalid_wait [Hsched Hcontinued]].
  assert (Horigin_lease : context.(os_sched_call_origin) =
    RunningInvocation context.(os_sched_call_stack).(stackLeaseSlot)
      context.(os_sched_call_stack).(stackLeaseGeneration)).
  { pose proof (proj1 Hsource) as Hlease; rewrite Horigin, Hstack in Hlease; exact Hlease. }
  assert (Hactive : task_invocation_active entry.(TskState)
    context.(os_sched_call_invocation) context.(os_sched_call_origin)).
  { pose proof (proj1 (proj2 Hsource)) as Hactive; rewrite Hinv, Horigin in Hactive; exact Hactive. }
  assert (Hactive_wait : task_invocation_active
    (event_pend_state sg entry eid current tid old PendQ ticks).(TskState)
    context.(os_sched_call_invocation) context.(os_sched_call_origin)).
  { eapply q_pend_first_critical_preserves_invocation; eassumption. }
  assert (Hcontinued_original : q_pend_wait_state context eid
    (event_pend_state sg entry eid current tid old PendQ ticks)).
  { unfold q_pend_wait_state in *; rewrite Hstack in Hcontinued; exact Hcontinued. }
  assert (Hcheckpoint : q_pend_first_wait_checkpoint external environment critical sg context
    before entered entry eid ticks (event_pend_state sg entry eid current tid old PendQ ticks)).
  { split; assumption. }
  assert (Hrestore : q_pend_restore_phase_pre
    (QueuePendWaitPhase context mask entry current eid ticks
      (event_pend_state sg entry eid current tid old PendQ ticks))
    environment critical sg entered mask (event_pend_state sg entry eid current tid old PendQ ticks)).
  { split; [reflexivity|]. split; [|exact Hsched].
    split; [exact Hsame|]. split; [exact Horigin_lease|]. split; [exact He|].
    split; [exact Hfirst|]. split; assumption. }
  unfold q_pend_masked_frame.
  sep_apply_l_atomic (q_pend_wait_call_continuations_merge external platform environment saved_local
    sg entered entry eid current tid old ticks Hentry).
  Exists (event_pend_state sg entry eid current tid old PendQ ticks).
  unfold q_pend_restore_input, q_pend_masked_frame; entailer!.
Qed.






