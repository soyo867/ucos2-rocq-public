From SimpleC.Verification Require Import VCPrelude.
From Ucos2Verify.VC.code.sem Require Import sem_pend_task_client_goal.
From Ucos2Verify.VC.code.sem Require Import sem_pend_task_client_proof_auto.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.sem.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_remove_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_wait_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_checkpoint_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_clear_status_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_clear_status_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_acquire_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_restore_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_program_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_clear_status_pend_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_return_fields_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_multi_pointer_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_fields_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_resource_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_wait_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_cleanup_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_sched_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_sched_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_client_case_lib.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_client_annotation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec Ucos2Verify.lib.kernel_runtime_inv.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_idle_frames_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_unlock_fields_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.lib.error_codes Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_sched_call_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Local Open Scope sac.


Lemma proof_of_OSSemPend_entail_wit_1_4 : OSSemPend_entail_wit_1_4.
Proof.
  unfold OSSemPend_entail_wit_1_4; right; intros.
  assert (0 <= event_slot_type_value before.(EventState) eid <= 255).
  { unfold event_slot_type_value.
    destruct (before.(EventState).(inUsedEventStates) eid) as [node|]; [destruct node.(eventType)|];
      cbn [encode_event_type]; lia. }
  entailer!.
Qed.

Lemma proof_of_OSSemPend_entail_wit_2_1 : OSSemPend_entail_wit_2_1.
Proof.
  unfold OSSemPend_entail_wit_2_1; left; intros.
  Intros.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range (&( "OSIntNesting" )) before.(IntrState).(intNesting)).
  entailer!.
Qed.

Lemma proof_of_OSSemPend_entail_wit_2_2 : OSSemPend_entail_wit_2_2.
Proof.
  unfold OSSemPend_entail_wit_2_2; left; intros.
  Intros.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range (&( "OSIntNesting" )) before.(IntrState).(intNesting)).
  entailer!.
Qed.

Lemma proof_of_OSSemPend_entail_wit_2_3 : OSSemPend_entail_wit_2_3.
Proof.
  unfold OSSemPend_entail_wit_2_3; left; intros.
  Intros.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range (&( "OSIntNesting" )) before.(IntrState).(intNesting)).
  entailer!.
Qed.

Lemma proof_of_OSSemPend_entail_wit_3_1 : OSSemPend_entail_wit_3_1.
Proof.
  unfold OSSemPend_entail_wit_3_1; left; intros.
  Intros.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range (&( "OSLockNesting" )) before.(IntrState).(lockNesting)).
  entailer!.
Qed.

Lemma proof_of_OSSemPend_entail_wit_3_2 : OSSemPend_entail_wit_3_2.
Proof.
  unfold OSSemPend_entail_wit_3_2; left; intros.
  Intros.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range (&( "OSLockNesting" )) before.(IntrState).(lockNesting)).
  entailer!.
Qed.

Lemma proof_of_OSSemPend_return_wit_1 : OSSemPend_return_wit_1.
Proof.
  unfold OSSemPend_return_wit_1; left; intros.
  unfold sem_pend_clear_status_phase_restore_output; Intros returned final_state.
  assert (Hsource : sem_pend_client_return_source environment critical sg first_returned
    (sem_count_update_state entry eid current_2 (encode_event_cnt_value current_2 - 1)) returned final_state) by tauto.
  pose proof (tmr_task_client_clear_status_pend_entry_return environment critical sg first_returned
    (sem_count_update_state entry eid current_2 (encode_event_cnt_value current_2 - 1)) returned final_state ltac:(assumption) ltac:(assumption) Hsource) as Hentry.
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hsource) as Hreturned.
  assert (Hsame : kernel_stack_call_same_call returned context).
  { unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence. }
  pose proof (sem_pend_client_program_restore environment critical sg context first_returned returned
    pe ticks before (sem_count_update_state entry eid current_2 (encode_event_cnt_value current_2 - 1)) 0 final_state ltac:(assumption) ltac:(assumption) Hsource) as Hresult.
  pose proof (sem_query_safe_return _ _ _ _ X Hresult ltac:(assumption)) as Hreturn.
  repeat (sep_apply_l_atomic mutex_query_truep_sepcon_merge).
  unfold tmr_task_client_clear_status_pend_post; Exists returned final_state local 0; entailer!;
    intros heap Hheap; exact (conj Hresult (conj Hreturn (conj Hsame Hentry))).
Qed.

Lemma proof_of_OSSemPend_return_wit_2 : OSSemPend_return_wit_2.
Proof.
  unfold OSSemPend_return_wit_2; left; intros.
  Intros.
  assert (Herror : sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = Some OS_ERR_PEND_LOCKED).
  { assert (Htype : event_slot_type_value before.(EventState) eid = 3) by assumption.
    rewrite Htype. assert (Hzero : before.(IntrState).(intNesting) = 0) by lia.
    rewrite Hzero; apply sem_pend_context_error_locked; lia. }
  pose proof (sem_pend_client_program_context_error environment critical sg context pe ticks before
    eid observed OS_ERR_PEND_LOCKED ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) Herror) as Hresult.
  pose proof (sem_query_safe_return _ _ _ _ X Hresult ltac:(assumption)) as Hreturn.
  assert (Hsame : kernel_stack_call_same_call context context).
  { unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call; auto. }
  assert (Hentry : tmr_task_client_clear_status_pend_entry sg context before) by assumption.
  repeat (sep_apply_l_atomic mutex_query_truep_sepcon_merge).
  unfold tmr_task_client_clear_status_pend_post; Exists context before local 13.
  unfold sem_pend_fields_closed, kernel_continuation_call_closed,
    kernel_continuation_inv, kernel_call_execution_owned, os_sched_fields_capsules.
  rewrite kernel_program_fields_inv_split_unmap.
  rewrite (UCOS2_fields_inv_split_module sg before InterruptModule ltac:(discriminate)).
  cbn [UCOS2_module_rep]; unfold interrupt_inv, interrupt_in_range, store_int_state.
  assert (Hint : &( "OSIntNesting" ) = sg.(g_OSIntNesting)) by assumption.
  rewrite Hint.
  assert (Hlock : &( "OSLockNesting" ) = sg.(g_OSLockNesting)) by assumption.
  rewrite Hlock.
  entailer!; intros heap Hheap; exact (conj Hresult (conj Hreturn (conj Hsame Hentry))).
Qed.

Lemma proof_of_OSSemPend_return_wit_3 : OSSemPend_return_wit_3.
Proof.
  unfold OSSemPend_return_wit_3; left; intros.
  Intros.
  assert (Herror : sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = Some OS_ERR_PEND_ISR).
  { assert (Htype : event_slot_type_value before.(EventState) eid = 3) by assumption.
    rewrite Htype. apply sem_pend_context_error_isr_before_lock; lia. }
  pose proof (sem_pend_client_program_context_error environment critical sg context pe ticks before
    eid observed OS_ERR_PEND_ISR ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) Herror) as Hresult.
  pose proof (sem_query_safe_return _ _ _ _ X Hresult ltac:(assumption)) as Hreturn.
  assert (Hsame : kernel_stack_call_same_call context context).
  { unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call; auto. }
  assert (Hentry : tmr_task_client_clear_status_pend_entry sg context before) by assumption.
  repeat (sep_apply_l_atomic mutex_query_truep_sepcon_merge).
  unfold tmr_task_client_clear_status_pend_post; Exists context before local 2.
  unfold sem_pend_fields_closed, kernel_continuation_call_closed,
    kernel_continuation_inv, kernel_call_execution_owned, os_sched_fields_capsules.
  rewrite kernel_program_fields_inv_split_unmap.
  rewrite (UCOS2_fields_inv_split_module sg before InterruptModule ltac:(discriminate)).
  cbn [UCOS2_module_rep]; unfold interrupt_inv, interrupt_in_range, store_int_state.
  assert (Hint : &( "OSIntNesting" ) = sg.(g_OSIntNesting)) by assumption.
  rewrite Hint.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range sg.(g_OSLockNesting)
    before.(IntrState).(lockNesting)).
  entailer!; intros heap Hheap; exact (conj Hresult (conj Hreturn (conj Hsame Hentry))).
Qed.

Lemma proof_of_OSSemPend_return_wit_4 : OSSemPend_return_wit_4.
Proof.
  unfold OSSemPend_return_wit_4; left; intros.
  Intros.
  assert (Herror : sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = Some OS_ERR_EVENT_TYPE).
  { apply sem_pend_context_error_type_first; cbn [encode_event_type]; lia. }
  pose proof (sem_pend_client_program_context_error environment critical sg context pe ticks before
    eid observed OS_ERR_EVENT_TYPE ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) Herror) as Hresult.
  pose proof (sem_query_safe_return _ _ _ _ X Hresult ltac:(assumption)) as Hreturn.
  assert (Hsame : kernel_stack_call_same_call context context).
  { unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call; auto. }
  assert (Hentry : tmr_task_client_clear_status_pend_entry sg context before) by assumption.
  assert (Haddr : &((pe) # "os_event" ->ₛ "OSEventType") = event_addr sg eid + OSEventType_off) by assumption.
  rewrite Haddr.
  sep_apply_l_atomic (sem_pend_fields_type_merge sg before eid ltac:(assumption)).
  repeat (sep_apply_l_atomic mutex_query_truep_sepcon_merge).
  unfold tmr_task_client_clear_status_pend_post; Exists context before local 1.
  unfold sem_pend_fields_closed, kernel_continuation_call_closed,
    kernel_continuation_inv, kernel_call_execution_owned, os_sched_fields_capsules.
  rewrite kernel_program_fields_inv_split_unmap.
  entailer!; intros heap Hheap; exact (conj Hresult (conj Hreturn (conj Hsame Hentry))).
Qed.

Lemma proof_of_OSSemPend_return_wit_5 : OSSemPend_return_wit_5.
Proof.
  unfold OSSemPend_return_wit_5; left; intros.
  Intros.
  assert (Hnull : pe = 0) by congruence; rewrite Hnull in *.
  pose proof (sem_pend_client_program_null environment critical sg context ticks before) as Hresult.
  pose proof (sem_query_safe_return _ _ _ _ X Hresult ltac:(assumption)) as Hreturn.
  assert (Hsame : kernel_stack_call_same_call context context).
  { unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call; auto. }
  assert (Hentry : tmr_task_client_clear_status_pend_entry sg context before) by assumption.
  repeat (sep_apply_l_atomic mutex_query_truep_sepcon_merge).
  unfold tmr_task_client_clear_status_pend_post; Exists context before local 4.
  unfold sem_pend_fields_closed, kernel_continuation_call_closed,
    kernel_continuation_inv, kernel_call_execution_owned, os_sched_fields_capsules.
  rewrite kernel_program_fields_inv_split_unmap.
  entailer!; intros heap Hheap; exact (conj Hresult (conj Hreturn (conj Hsame Hentry))).
Qed.

Lemma proof_of_OSSemPend_return_wit_6 : OSSemPend_return_wit_6.
Proof.
  unfold OSSemPend_return_wit_6; left; intros.
  unfold sem_pend_clear_status_phase_restore_output; Intros returned final_state.
  assert (Hsource : sem_pend_client_return_source environment critical sg second_returned
    after returned final_state) by tauto.
  pose proof (tmr_task_client_clear_status_pend_entry_return environment critical sg second_returned
    after returned final_state ltac:(assumption) ltac:(assumption) Hsource) as Hentry.
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hsource) as Hreturned.
  assert (Hsame : kernel_stack_call_same_call returned context).
  { unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence. }
  pose proof (sem_pend_client_program_restore environment critical sg context second_returned returned
    pe ticks before after error final_state ltac:(assumption) ltac:(assumption) Hsource) as Hresult.
  pose proof (sem_query_safe_return _ _ _ _ X Hresult ltac:(assumption)) as Hreturn.
  repeat (sep_apply_l_atomic mutex_query_truep_sepcon_merge).
  unfold tmr_task_client_clear_status_pend_post; Exists returned final_state next_local error; entailer!;
    intros heap Hheap; exact (conj Hresult (conj Hreturn (conj Hsame Hentry))).
Qed.

Lemma proof_of_OSSemPend_return_wit_7 : OSSemPend_return_wit_7.
Proof.
  unfold OSSemPend_return_wit_7; left; intros.
  unfold sem_pend_clear_status_phase_restore_output; Intros returned final_state.
  assert (Hsource : sem_pend_client_return_source environment critical sg second_returned
    after returned final_state) by tauto.
  pose proof (tmr_task_client_clear_status_pend_entry_return environment critical sg second_returned
    after returned final_state ltac:(assumption) ltac:(assumption) Hsource) as Hentry.
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hsource) as Hreturned.
  assert (Hsame : kernel_stack_call_same_call returned context).
  { unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence. }
  pose proof (sem_pend_client_program_restore environment critical sg context second_returned returned
    pe ticks before after error final_state ltac:(assumption) ltac:(assumption) Hsource) as Hresult.
  pose proof (sem_query_safe_return _ _ _ _ X Hresult ltac:(assumption)) as Hreturn.
  repeat (sep_apply_l_atomic mutex_query_truep_sepcon_merge).
  unfold tmr_task_client_clear_status_pend_post; Exists returned final_state next_local error; entailer!;
    intros heap Hheap; exact (conj Hresult (conj Hreturn (conj Hsame Hentry))).
Qed.

Lemma proof_of_OSSemPend_return_wit_8 : OSSemPend_return_wit_8.
Proof.
  unfold OSSemPend_return_wit_8; left; intros.
  unfold sem_pend_clear_status_phase_restore_output; Intros returned final_state.
  assert (Hsource : sem_pend_client_return_source environment critical sg second_returned
    after returned final_state) by tauto.
  pose proof (tmr_task_client_clear_status_pend_entry_return environment critical sg second_returned
    after returned final_state ltac:(assumption) ltac:(assumption) Hsource) as Hentry.
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hsource) as Hreturned.
  assert (Hsame : kernel_stack_call_same_call returned context).
  { unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence. }
  pose proof (sem_pend_client_program_restore environment critical sg context second_returned returned
    pe ticks before after error final_state ltac:(assumption) ltac:(assumption) Hsource) as Hresult.
  pose proof (sem_query_safe_return _ _ _ _ X Hresult ltac:(assumption)) as Hreturn.
  repeat (sep_apply_l_atomic mutex_query_truep_sepcon_merge).
  unfold tmr_task_client_clear_status_pend_post; Exists returned final_state next_local error; entailer!;
    intros heap Hheap; exact (conj Hresult (conj Hreturn (conj Hsame Hentry))).
Qed.

Lemma proof_of_OSSemPend_return_wit_9 : OSSemPend_return_wit_9.
Proof.
  unfold OSSemPend_return_wit_9; left; intros.
  unfold sem_pend_clear_status_phase_restore_output; Intros returned final_state.
  assert (Hsource : sem_pend_client_return_source environment critical sg second_returned
    after returned final_state) by tauto.
  pose proof (tmr_task_client_clear_status_pend_entry_return environment critical sg second_returned
    after returned final_state ltac:(assumption) ltac:(assumption) Hsource) as Hentry.
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hsource) as Hreturned.
  assert (Hsame : kernel_stack_call_same_call returned context).
  { unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence. }
  pose proof (sem_pend_client_program_restore environment critical sg context second_returned returned
    pe ticks before after error final_state ltac:(assumption) ltac:(assumption) Hsource) as Hresult.
  pose proof (sem_query_safe_return _ _ _ _ X Hresult ltac:(assumption)) as Hreturn.
  repeat (sep_apply_l_atomic mutex_query_truep_sepcon_merge).
  unfold tmr_task_client_clear_status_pend_post; Exists returned final_state next_local error; entailer!;
    intros heap Hheap; exact (conj Hresult (conj Hreturn (conj Hsame Hentry))).
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_1 : OSSemPend_which_implies_wit_1.
Proof.
  unfold OSSemPend_which_implies_wit_1; left; intros.
  unfold tmr_task_client_clear_status_pend_pre.
  apply coq_prop_andp_left; intros [Hdomain [Hentry Hsafe]].
  pose proof Hdomain as [Hprofile [Hlayout Hinput]].
  assert (Hnonidle : flag_pend_non_idle_at sg context before).
  { pose proof Hentry as [[Hsource [Havailable [Hrunning [Hcache [Hidle Hclear]]]]] Hstatus].
    destruct (kernel_call_task_source_current_at context before Hsource) as [Hcurrent [node [Hnode Hg]]].
    exists node; exact (conj Hnode (conj Hg (proj1 (Hclear node Hnode)))). }
  unfold sem_pend_fields_closed, kernel_continuation_call_closed,
    kernel_continuation_inv, kernel_call_execution_owned, os_sched_fields_capsules.
  rewrite kernel_program_fields_inv_split_unmap.
  Intros; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_2 : OSSemPend_which_implies_wit_2.
Proof.
  unfold OSSemPend_which_implies_wit_2; left; intros.
  unfold sem_pend_error_cell; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_3 : OSSemPend_which_implies_wit_3.
Proof.
  unfold OSSemPend_which_implies_wit_3; left; intros.
  Intros.
  match goal with H : sem_pend_call_input _ _ _ _ _ _ _ |- _ =>
    pose proof H as [Hzero|[Hnonzero [Haddr [Hid [Hslot Hprotocol]]]]] end;
    [contradiction|].
  rewrite PreH2.
  sep_apply_l_atomic (sem_pend_fields_type_split sg before eid observed Hslot).
  Intros.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_4 : OSSemPend_which_implies_wit_4.
Proof.
  unfold OSSemPend_which_implies_wit_4; right; intros; Intros.
  rewrite PreH1, PreH2.
  sep_apply_l_atomic (sem_pend_fields_type_merge sg before eid ltac:(assumption)).
  rewrite (UCOS2_fields_inv_split_module sg before InterruptModule ltac:(discriminate)).
  cbn [UCOS2_module_rep]; unfold interrupt_inv, store_int_state; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_6 : OSSemPend_which_implies_wit_6.
Proof.
  unfold OSSemPend_which_implies_wit_6; left; intros; Intros.
  rewrite PreH1, PreH2.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range sg.(g_OSIntNesting) before.(IntrState).(intNesting)).
  prop_apply_p (UCOS2_C_Rules.store_uchar_range sg.(g_OSLockNesting) before.(IntrState).(lockNesting)).
  rewrite (UCOS2_fields_inv_split_module sg before InterruptModule ltac:(discriminate)).
  cbn [UCOS2_module_rep]; unfold interrupt_inv, interrupt_in_range, store_int_state; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_7 : OSSemPend_which_implies_wit_7.
Proof.
  unfold OSSemPend_which_implies_wit_7; left; intros; Intros.
  assert (Hentry : tmr_task_client_clear_status_pend_entry sg context before) by assumption.
  assert (Hinput : sem_pend_call_input critical sg context.(os_sched_call_invocation)
    pe before eid observed) by assumption.
  destruct (tmr_task_client_clear_status_pend_entry_sem sg context before ltac:(assumption) Hentry)
    as [Hcontext [Hfields Hstatus]].
  assert (Hclear : sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None).
  { unfold sem_pend_context_error; rewrite PreH2; cbn [encode_event_type Z.eqb negb].
    rewrite (proj2 (Z.ltb_ge _ _) PreH3), (proj2 (Z.ltb_ge _ _) PreH4); reflexivity. }
  assert (Hpre : sem_pend_clear_status_phase_save_pre (SemPendAcquirePhase pe eid observed)
    environment critical sg context mask before).
  { exact (conj Hcontext (conj Hinput (conj PreH1 (conj Hclear (conj Hfields Hstatus))))). }
  unfold sem_pend_clear_status_phase_save_input.
  unfold sem_pend_fields_closed, kernel_continuation_call_closed,
    kernel_continuation_inv, kernel_call_execution_owned, os_sched_fields_capsules.
  rewrite kernel_program_fields_inv_split_unmap.
  repeat (sep_apply_l_atomic mutex_query_truep_sepcon_merge).
  entailer!; try (intros heap Hheap; exact Hpre).
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_8 : OSSemPend_which_implies_wit_8.
Proof.
  unfold OSSemPend_which_implies_wit_8; left; intros.
  unfold sem_pend_clear_status_phase_save_output; Intros returned acquired.
  assert (Hsource : sem_pend_client_return_source environment critical sg context before returned acquired) by tauto.
  assert (Hobs : sem_pend_clear_status_phase_save_observation (SemPendAcquirePhase pe eid observed)
    environment critical sg context returned mask cpu_sr before acquired) by tauto.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  assert (Hinitial : tmr_task_client_clear_status_pend_entry sg context before) by assumption.
  pose proof (tmr_task_client_clear_status_pend_entry_return environment critical sg context before returned acquired
    Hvalid Hinitial Hsource) as Hentry.
  pose proof Hinitial as [[Htask [Havailable [Hrunning [Hcache [Hidle Hclear]]]]] Hstatus].
  assert (Hnonidle_initial : flag_pend_non_idle_at sg context before).
  { destruct (kernel_call_task_source_current_at context before Htask) as [Hcurrent [node [Hnode Hg]]].
    exists node; exact (conj Hnode (conj Hg (proj1 (Hclear node Hnode)))). }
  pose proof (sem_pend_task_client_return_preserves_non_idle environment critical sg context before returned acquired
    context Hsource Hvalid Hrunning Htask
    ltac:(unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call; auto) Hnonidle_initial) as Hnonidle.
  pose proof (proj1 Hobs) as Hcontext.
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hsource) as [Hi [Ho Hstack]].
  Exists returned acquired.
  unfold sem_pend_fields_masked, kernel_continuation_call_masked, kernel_continuation_inv,
    os_sched_fields_capsules.
  rewrite kernel_program_fields_inv_split_unmap, Hi, Ho; Intros; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_9 : OSSemPend_which_implies_wit_9.
Proof.
  unfold OSSemPend_which_implies_wit_9; left; intros; Intros.
  match goal with H : sem_pend_clear_status_phase_save_observation _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as [Hcontext [found [Hacquire [Hstage Hblocking]]]] end.
  pose proof Hacquire as [_ [_ [Hsaved [Hvalid [_ [Hlookup [_ [Htype Hg]]]]]]]].
  Exists found entry_2 first_returned_2; rewrite PreH6.
  sep_apply_l_atomic (sem_pend_fields_count_split sg entry_2 eid found Hlookup Htype).
  Intros; rewrite Htype; cbn [encode_event_type]; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_10 : OSSemPend_which_implies_wit_10.
Proof.
  unfold OSSemPend_which_implies_wit_10; left; intros; Intros.
  assert (Hacquire : sem_pend_client_acquire_observation environment critical sg context first_returned_2
    mask cpu_sr before entry_2 eid observed current_2) by assumption.
  pose proof Hacquire as [_ [Hsame [Hsaved [Hvalid [_ [Hlookup [_ [Htype Hg]]]]]]]].
  pose proof (tmr_task_client_clear_status_pend_count_checkpoint sg first_returned_2 entry_2 eid current_2
    Hvalid ltac:(assumption) Hlookup Htype ltac:(lia)) as Hentry_after.
  assert (Hclear : sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None).
  { unfold sem_pend_context_error; rewrite PreH3, PreH4, PreH5; reflexivity. }
  pose proof (sem_pend_client_immediate_result environment critical sg context first_returned_2 pe ticks
    before eid observed mask cpu_sr entry_2 current_2 PreH1 PreH2 ltac:(assumption) ltac:(assumption)
    Hclear Hacquire ltac:(lia)) as Hcheckpoint.
  Exists first_returned_2 entry_2 current_2; rewrite PreH8.
  sep_apply_l_atomic (sem_pend_fields_count_merge_decrement sg entry_2 eid current_2
    Hvalid Hlookup Htype ltac:(lia)).
  assert (Hvalid_projection :
    UCOS2_fields_inv sg (sem_count_update_state entry_2 eid current_2 (encode_event_cnt_value current_2 - 1)) |--
    coq_prop (UCOS2_state_inv sg (sem_count_update_state entry_2 eid current_2 (encode_event_cnt_value current_2 - 1)))).
  { unfold UCOS2_fields_inv; entailer!. }
  prop_apply_p Hvalid_projection.
  Intros.
  assert (Hvalid_after : UCOS2_state_inv sg
    (sem_count_update_state entry_2 eid current_2 (encode_event_cnt_value current_2 - 1))) by tauto.
  pose proof (tmr_task_client_clear_status_pend_entry_sem _ _ _ Hvalid_after Hentry_after) as Hsem_after.
  unfold sem_pend_clear_status_phase_restore_input; cbn [sem_pend_clear_status_phase_restore_pre].
  unfold sem_pend_fields_masked, kernel_continuation_call_masked, kernel_continuation_inv,
    os_sched_fields_capsules.
  rewrite kernel_program_fields_inv_split_unmap.
  destruct Hsame as [Hi [Ho Hstack]]; rewrite Hi, Ho.
  cbn [sem_count_update_state replace_EventS TskState].
  repeat (sep_apply_l_atomic mutex_query_truep_sepcon_merge).
  entailer!.
  all: try (unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call; tauto).
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_12 : OSSemPend_which_implies_wit_12.
Proof.
  unfold OSSemPend_which_implies_wit_12; left; intros; Intros.
  match goal with H : sem_pend_clear_status_phase_save_observation _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as [Hcontext [found [Hacquire [Hstage Hblocking]]]] end.
  assert (Hhas : sem_pend_has_stack (Some environment)) by (exists environment; reflexivity).
  Exists current_2 entry_2 first_returned_2; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_13 : OSSemPend_which_implies_wit_13.
Proof.
  unfold OSSemPend_which_implies_wit_13; left; intros; Intros.
  assert (Hacquire : sem_pend_client_acquire_observation environment critical sg context first_returned_2
    mask cpu_sr before entry_2 eid observed current_2) by assumption.
  pose proof Hacquire as [_ [_ [_ [Hvalid [_ [Hlookup [_ [Htype Hg]]]]]]]].
  rewrite PreH7, PreH8.
  prop_apply_p (store_ushort_range (event_addr sg eid + OSEventCnt_off) (encode_event_cnt_value current_2)).
  Intros.
  sep_apply_l_atomic (sem_pend_clear_status_fields_acquired_wait_prefix sg first_returned_2 entry_2 eid current_2
    ltac:(assumption) Hvalid Hlookup Htype ltac:(lia) ltac:(assumption)).
  Intros node.
  pose proof (proj1 (proj2 Hacquire)) as Hsame.
  assert (Hsource_context : kernel_call_task_source context entry_2).
  { apply (proj1 (task_tcb_init_stack_same_call_source_iff first_returned_2 context entry_2 Hsame)); tauto. }
  assert (Horigin_context : context.(os_sched_call_origin) =
    RunningInvocation first_returned_2.(os_sched_call_stack).(stackLeaseSlot) node.(taskGeneration)).
  { rewrite <- (proj1 (proj2 Hsame)); tauto. }
  Exists first_returned_2.(os_sched_call_stack).(stackLeaseSlot) node current_2 entry_2 first_returned_2.
  cbn [tcb_cell tcb_field_address].
  asrt_simpl_pure; sepcon_assoc_change.
  repeat (sep_apply_l_atomic mutex_query_truep_sepcon_merge).
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_14 : OSSemPend_which_implies_wit_14.
Proof.
  unfold OSSemPend_which_implies_wit_14; left; intros; Intros.
  assert (Hwait : sem_pend_clear_status_wait_entry sg entry_2 eid current_2 tid_2 old_2) by assumption.
  pose proof (sem_pend_task_priority_in_range sg entry_2 tid_2 old_2 (proj1 Hwait)
    (proj1 (proj2 (proj2 (proj2 Hwait))))) as Hpriority.
  repeat rewrite Z.quot_div_nonneg by lia.
  pose proof (sem_pend_clear_status_wait_entry_row_in_range _ _ _ _ _ _ Hwait) as Hrow.
  assert (Horigin : sem_pend_clear_status_wait_origin environment critical sg context first_returned_2
    mask cpu_sr before observed entry_2 eid current_2 tid_2 old_2).
  { unfold sem_pend_clear_status_wait_origin; tauto. }
  pose proof (sem_pend_clear_status_fields_wait_prefix_split_call sg entry_2 eid current_2 tid_2 old_2 ticks Hwait) as Hsplit.
  cbn [tcb_cell tcb_field_address] in Hsplit.
  sep_apply_l_atomic Hsplit.
  Exists current_2 tid_2 old_2 entry_2 first_returned_2.
  repeat rewrite Z.quot_div_nonneg by lia.
  rewrite PreH2, PreH4, PreH5.
  asrt_simpl_pure; sepcon_assoc_change.
  repeat (sep_apply_l_atomic mutex_query_truep_sepcon_merge).
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_15 : OSSemPend_which_implies_wit_15.
Proof.
  unfold OSSemPend_which_implies_wit_15; left; intros; Intros.
  assert (Horigin : sem_pend_clear_status_wait_origin environment critical sg context first_returned_2
    mask saved before observed entry_2 eid current tid old) by assumption.
  assert (Hcontext : sem_pend_client_phase_context sg first_returned_2 entry_2) by assumption.
  pose proof Horigin as [Hacquire [Hwait Hrest]].
  pose proof Hacquire as [_ [Hsame [Hsaved Hacqrest]]].
  pose proof Hcontext as [Hvalid [Hsource [Hrunning [Hidle [Havailable Hcache]]]]].
  pose proof (sem_pend_task_priority_in_range sg entry_2 tid old Hvalid
    (proj1 (proj2 (proj2 (proj2 Hwait))))) as Hpriority.
  repeat rewrite Z.quot_div_nonneg by lia.
  pose proof (sem_pend_clear_status_wait_origin_history environment critical sg context first_returned_2
    mask saved before observed entry_2 eid current tid old ticks Horigin) as Hhistory.
  assert (Havailable_original : kernel_call_stack_available context entry_2).
  { unfold kernel_call_stack_available in *; rewrite (proj1 (proj2 Hsame)) in Havailable; exact Havailable. }
  pose proof (sem_pend_clear_status_phase_wait_restore_returned_pre environment critical sg context first_returned_2
    mask saved before observed entry_2 eid current tid old ticks Horigin Hrunning Hidle Havailable_original) as Hpre.
  pose proof (proj1 (proj2 Hpre)) as Hwaiting.
  pose proof Hwait as [_ [_ [_ [Hold Hwait_rest]]]].
  pose proof (tmr_task_event_pend_multi_pointer_transport sg entry_2 eid current tid old PendSem ticks Hold) as Htransport.
  assert (Hnonidle : flag_pend_non_idle_at sg context (event_pend_state sg entry_2 eid current tid old PendSem ticks)).
  { eapply SelectedIdleFrames.task_used_priority_transport_non_idle; [|eassumption].
    change (SelectedIdleFrames.task_used_priority_transport entry_2.(TskState)
      (glob_task_set_usedtask entry_2.(TskState) tid (task_set_event_ptr (task_prepare_event_wait old PendSem ticks) (Some eid)))).
    eapply SelectedIdleFrames.task_update_used_priority_transport; [exact Hold|reflexivity|reflexivity]. }
  assert (Hzero : sem_pend_task_client_multi_zero first_returned_2 entry_2).
  { assert (Hentry : tmr_task_client_clear_status_pend_entry sg first_returned_2 entry_2) by assumption.
    pose proof Hentry as [[Htask [_ [_ [_ [_ Hclear]]]]] Hstatus].
    destruct (kernel_call_task_source_current_at first_returned_2 entry_2 Htask) as [Hcur [node [Hnode Hg]]].
    exists node; exact (conj Hnode (conj Hg (proj2 (proj2 (proj1 (proj2 (Hclear node Hnode))))))). }
  unfold sem_pend_task_client_multi_zero in Hzero; rewrite (proj2 (proj2 Hsame)) in Hzero.
  pose proof (sem_pend_task_client_transport_multi_zero context _ _ Htransport Hzero) as Hwaiting_zero.
  assert (Hsave_observation : sem_pend_clear_status_phase_save_observation
    (SemPendAcquirePhase pe eid observed) environment critical sg context first_returned_2
    mask saved before entry_2) by assumption.
  pose proof (sem_pend_acquire_wait_selection_enabled environment critical sg context first_returned_2
    mask saved before entry_2 pe eid observed current tid old ticks Hsave_observation) as Henabled.
  pose proof (sem_pend_task_client_wait_sched_entry environment critical sg context mask before observed eid ticks
    (event_pend_state sg entry_2 eid current tid old PendSem ticks) first_returned_2
    (event_pend_state sg entry_2 eid current tid old PendSem ticks)
    Hpre Henabled Hnonidle Hwaiting_zero) as Hsched_entry.
  Exists entry_2 first_returned_2 (event_pend_state sg entry_2 eid current tid old PendSem ticks) saved.
  rewrite PreH1, PreH2, PreH3, PreH4.
  unfold os_sched_fields_capsules.
  rewrite <- (proj1 Hsame), <- (proj1 (proj2 Hsame)).
  pose proof (sem_pend_clear_status_fields_wait_call_continuation_merge_source _ _ _
    environment.(task_stack_call_continuations) local critical sg (task_stack_call_active_key first_returned_2)
    first_returned_2 saved entry_2 entry_2 eid current tid old ticks Hwait Hsource Hcache ltac:(assumption)) as Hmerge.
  unfold sem_pend_fields_wait_call_post in Hmerge.
  repeat (sep_apply_l_atomic mutex_query_truep_sepcon_merge).
  lazymatch type of Hmerge with ?prefix |-- _ =>
    lazymatch goal with |- ?whole |-- _ =>
      assert (Hpacked : whole |-- prefix ** TT) by
        (asrt_simpl_pure; sepcon_assoc_change;
         repeat (sep_apply_l_atomic mutex_query_truep_sepcon_merge);
         entailer!; intros heap Hheap; exact I);
      rewrite Hpacked, Hmerge
    end
  end.
  Intros.
  unfold sem_pend_clear_status_phase_restore_input, sem_pend_fields_masked; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_16 : OSSemPend_which_implies_wit_16.
Proof.
  unfold OSSemPend_which_implies_wit_16; left; intros; Intros.
  sep_apply_l_atomic (sem_pend_task_client_sched_input_same_call environment restored_local_2 critical sg
    context mask before observed eid ticks waiting_2 restored_call_2 sched_entry_2).
  Intros.
  Exists restored_local_2 waiting_2 sched_entry_2 restored_call_2; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_17 : OSSemPend_which_implies_wit_17.
Proof.
  unfold OSSemPend_which_implies_wit_17; left; intros; Intros.
  sep_apply_l_atomic (sem_pend_task_client_sched_output_second_save environment critical sg context mask
    before observed eid ticks waiting_2 restored_call sched_entry ltac:(assumption)).
  Intros returned current next_local.
  Exists waiting_2 next_local returned current.
  asrt_simpl_pure; sepcon_assoc_change.
  repeat (sep_apply_l_atomic mutex_query_truep_sepcon_merge).
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_18 : OSSemPend_which_implies_wit_18.
Proof.
  unfold OSSemPend_which_implies_wit_18; left; intros.
  unfold sem_pend_clear_status_phase_save_output; Intros second_returned resumed.
  assert (Hsource : sem_pend_client_return_source environment critical sg returned_2 scheduled_2
    second_returned resumed) by tauto.
  assert (Hcontext : sem_pend_client_phase_context sg returned_2 scheduled_2) by assumption.
  assert (Hobs : sem_pend_clear_status_phase_save_observation (SemPendWaitPhase context mask before observed eid ticks waiting_2)
    environment critical sg returned_2 second_returned mask cpu_sr scheduled_2 resumed) by tauto.
  pose proof (sem_pend_task_client_return_preserves_non_idle environment critical sg returned_2
    scheduled_2 second_returned resumed context Hsource (proj1 Hcontext)
    (proj1 (proj2 (proj2 Hcontext))) (proj1 (proj2 Hcontext))
    ltac:(assumption) ltac:(assumption)) as Hnonidle.
  pose proof (sem_pend_task_client_return_multi_zero environment critical sg returned_2
    scheduled_2 second_returned resumed context Hsource (proj1 Hcontext) (proj1 (proj2 Hcontext))
    ltac:(assumption) ltac:(assumption)) as Hzero.
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hsource) as Hreturned.
  assert (Hsame : kernel_stack_call_same_call second_returned context).
  { unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence. }
  pose proof Hobs as [Hresumed [_ [[Hsame' [Hhistory Hpath]] Hselected]]].
  Exists next_local_2 scheduled_2 returned_2 waiting_2 second_returned resumed.
  unfold sem_pend_fields_masked, kernel_continuation_call_masked, kernel_continuation_inv,
    os_sched_fields_capsules.
  rewrite kernel_program_fields_inv_split_unmap, (proj1 Hsame), (proj1 (proj2 Hsame)).
  Intros; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_19 : OSSemPend_which_implies_wit_19.
Proof.
  unfold OSSemPend_which_implies_wit_19; left; intros; Intros.
  assert (Hobs : sem_pend_clear_status_phase_save_observation
    (SemPendWaitPhase context mask before observed eid ticks waiting)
    environment critical sg returned second_returned_2 mask cpu_sr scheduled resumed_2) by assumption.
  destruct (sem_pend_clear_status_phase_selected_resume_origin environment critical sg context mask before observed
    eid ticks waiting second_returned_2 resumed_2 (proj2 (proj2 Hobs))) as [node Horigin].
  pose proof (proj1 Horigin) as [Hvalid [Hcurrent [Hnode Hrest]]].
  destruct (sem_pend_task_client_resume_local_fields sg context second_returned_2 resumed_2
    context.(os_sched_call_stack).(stackLeaseSlot) node ltac:(assumption) ltac:(assumption)
    ltac:(assumption) ltac:(assumption) Hcurrent Hnode) as [Hzero Hnonidle].
  rewrite PreH1.
  sep_apply_l_atomic (sem_pend_fields_cleanup_split sg resumed_2
    context.(os_sched_call_stack).(stackLeaseSlot) node Hvalid Hcurrent Hnode).
  Exists next_local_2 context.(os_sched_call_stack).(stackLeaseSlot) node resumed_2 second_returned_2.
  cbn [tcb_cell tcb_field_address].
  asrt_simpl_pure; sepcon_assoc_change.
  repeat (sep_apply_l_atomic mutex_query_truep_sepcon_merge).
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_20 : OSSemPend_which_implies_wit_20.
Proof.
  unfold OSSemPend_which_implies_wit_20; left; intros; Intros.
  assert (Hstatus : old.(statPend) = PendOK).
  { destruct old.(statPend); cbn [encode_pend_status] in PreH3; congruence. }
  pose proof (sem_pend_clear_status_resume_cleanup_without_timeout environment critical sg context mask before observed
    eid ticks resumed tid_2 old ltac:(assumption) ltac:(rewrite Hstatus; discriminate)) as Hcleanup.
  rewrite Hstatus in Hcleanup; cbn [encode_pend_status sem_pend_resume_error encode_os_err_code] in Hcleanup.
  Exists next_local_2 tid_2 old resumed second_returned_2; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_21 : OSSemPend_which_implies_wit_21.
Proof.
  unfold OSSemPend_which_implies_wit_21; left; intros; Intros.
  assert (Hstatus : old.(statPend) = PendAbort).
  { destruct old.(statPend); cbn [encode_pend_status] in PreH3; congruence. }
  pose proof (sem_pend_clear_status_resume_cleanup_without_timeout environment critical sg context mask before observed
    eid ticks resumed tid_2 old ltac:(assumption) ltac:(rewrite Hstatus; discriminate)) as Hcleanup.
  rewrite Hstatus in Hcleanup; cbn [encode_pend_status sem_pend_resume_error encode_os_err_code] in Hcleanup.
  Exists next_local_2 tid_2 old resumed second_returned_2; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_22 : OSSemPend_which_implies_wit_22.
Proof.
  unfold OSSemPend_which_implies_wit_22; left; intros; Intros.
  assert (Horigin : sem_pend_clear_status_resume_origin environment critical sg context mask before observed
    eid ticks resumed tid_2 old) by assumption.
  assert (Htimeout : old.(statPend) = PendTimeout).
  { destruct old.(statPend); cbn [encode_pend_status] in PreH3, PreH4; congruence. }
  pose proof (proj1 Horigin) as Hresume.
  pose proof Hresume as [Hvalid [Hcur [Hold [[Hmulti [Hflag Hregistration]] Hready]]]].
  pose proof (sem_pend_task_priority_in_range sg resumed tid_2 old Hvalid Hold) as Hpriority.
  repeat rewrite Z.quot_div_nonneg by lia.
  rewrite Htimeout in Hregistration.
  destruct (sem_pend_resume_timeout_event sg resumed eid tid_2 old Hvalid Hold Hregistration)
    as [found [Hfound Hin]].
  assert (Hevent : mutex_query_lookup resumed eid current) by assumption.
  assert (found = current) by (unfold mutex_query_lookup in *; congruence); subst found.
  pose proof (sem_pend_clear_status_resume_cleanup_timeout environment critical sg context mask before observed
    eid ticks resumed tid_2 old current Horigin Htimeout Hevent) as Hcleanup.
  assert (Hsame : kernel_stack_call_same_call second_returned_2 context) by assumption.
  destruct (sem_pend_task_client_remove_context sg second_returned_2 resumed eid current tid_2 old
    ltac:(assumption) Hold Hevent Hin) as [Hcleaning [Htransport Hnonidle_returned]].
  assert (Hnonidle : flag_pend_non_idle_at sg context (event_task_remove_state resumed eid current tid_2 old)).
  { unfold flag_pend_non_idle_at in *; rewrite (proj2 (proj2 Hsame)) in Hnonidle_returned.
    apply Hnonidle_returned; assumption. }
  pose proof (sem_pend_task_client_transport_multi_zero context _ _ Htransport ltac:(assumption)) as Hzero.
  pose proof (sem_pend_fields_task_update_preserves_coverage resumed.(TskState)
    (task_stack_call_active_key second_returned_2) tid_2 old (task_set_event_ptr old None)
    Hold eq_refl ltac:(assumption)) as Hcovered.
  pose proof (proj1 Hcleanup) as [Hvalid_clean [Hcur_clean [Hnode_clean Hrest]]].
  rewrite PreH5, PreH6.
  sep_apply_l_atomic (sem_pend_fields_remove_call_merge sg resumed eid current tid_2 old Hresume
    Htimeout Hevent ltac:(assumption)).
  unfold os_sched_fields_capsules.
  sep_apply_l_atomic (sem_pend_fields_task_update_continuations _ _ _
    environment.(task_stack_call_continuations) next_local_2 resumed.(TskState) tid_2 old
    (task_set_event_ptr old None) Hold eq_refl eq_refl).
  sep_apply_l_atomic (sem_pend_fields_cleanup_split sg (event_task_remove_state resumed eid current tid_2 old)
    tid_2 (task_set_event_ptr old None) Hvalid_clean Hcur_clean Hnode_clean).
  Exists next_local_2 tid_2 (task_set_event_ptr old None)
    (event_task_remove_state resumed eid current tid_2 old) second_returned_2.
  repeat rewrite Z.quot_div_nonneg by lia.
  cbn [tcb_cell tcb_field_address event_task_remove_state replace_EventS replace_TskS TskState].
  asrt_simpl_pure; sepcon_assoc_change.
  repeat (sep_apply_l_atomic mutex_query_truep_sepcon_merge).
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_23 : OSSemPend_which_implies_wit_23.
Proof.
  unfold OSSemPend_which_implies_wit_23; left; intros; Intros.
  assert (Horigin : sem_pend_clear_status_resume_origin environment critical sg context mask before observed
    eid ticks resumed_2 tid_2 old_2) by assumption.
  assert (Htimeout : old_2.(statPend) = PendTimeout).
  { destruct old_2.(statPend); cbn [encode_pend_status] in PreH3, PreH4; congruence. }
  pose proof (proj1 Horigin) as Hresume.
  pose proof Hresume as [Hvalid [Hcur [Hold [[Hmulti [Hflag Hregistration]] Hready]]]].
  pose proof (sem_pend_task_priority_in_range sg resumed_2 tid_2 old_2 Hvalid Hold) as Hpriority.
  repeat rewrite Z.quot_div_nonneg by lia.
  rewrite Htimeout in Hregistration.
  destruct (sem_pend_resume_timeout_event sg resumed_2 eid tid_2 old_2 Hvalid Hold Hregistration)
    as [current [Hevent Hin]].
  pose proof (sem_pend_fields_resume_split_remove_call sg resumed_2 eid tid_2 old_2 current
    Hresume Hevent ltac:(assumption)) as Hsplit.
  cbn [tcb_cell tcb_field_address] in Hsplit.
  sep_apply_l_atomic Hsplit.
  Exists next_local_2 current tid_2 old_2 resumed_2 second_returned_2.
  repeat rewrite Z.quot_div_nonneg by lia.
  rewrite PreH5; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_24 : OSSemPend_which_implies_wit_24.
Proof.
  unfold OSSemPend_which_implies_wit_24; left; intros; Intros.
  assert (Horigin : sem_pend_clear_status_cleanup_origin environment critical sg context mask before observed
    eid ticks error_2 cleaning tid node) by assumption.
  pose proof (proj1 Horigin) as Hcleanup.
  assert (Hcontext : sem_pend_client_phase_context sg second_returned_2 cleaning) by assumption.
  destruct (tmr_task_client_clear_status_pend_cleanup_stores sg second_returned_2 cleaning tid node Hcleanup
    Hcontext PreH2 PreH1) as [Hvalid Hentry].
  pose proof (tmr_task_client_clear_status_pend_entry_sem _ _ _ Hvalid Hentry) as Hsem_entry.
  assert (Hclear : sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None).
  { unfold sem_pend_context_error; rewrite PreH5, PreH6, PreH7; reflexivity. }
  pose proof (sem_pend_clear_status_cleanup_result environment critical sg context mask before observed eid
    pe ticks error_2 cleaning tid node PreH3 PreH4 ltac:(assumption) ltac:(assumption) Hclear Horigin) as Hresult.
  assert (Hsame : kernel_stack_call_same_call second_returned_2 context) by assumption.
  Exists next_local_2 acquired_2 error_2 second_returned_2 (event_pend_cleanup_state sg false cleaning tid node).
  rewrite PreH8, <- (proj1 Hsame), <- (proj1 (proj2 Hsame)).
  unfold os_sched_fields_capsules.
  pose proof (sem_pend_fields_cleanup_continuation_merge environment next_local_2 critical sg
    second_returned_2 cpu_sr acquired_2 cleaning tid node Hcleanup (proj1 (proj2 Hcontext))
    ltac:(assumption)) as Hmerge.
  unfold sem_pend_fields_cleanup_cells in Hmerge; cbn [tcb_cell tcb_field_address] in Hmerge.
  lazymatch type of Hmerge with ?prefix |-- _ =>
    lazymatch goal with |- ?whole |-- _ =>
      assert (Hpacked : whole |-- prefix ** (pd # UChar |-> error_2 ** TT)) by
        (asrt_simpl_pure; sepcon_assoc_change;
         repeat (sep_apply_l_atomic mutex_query_truep_sepcon_merge);
         entailer!; intros heap Hheap; exact I);
      rewrite Hpacked, Hmerge
    end
  end.
  Intros.
  unfold sem_pend_clear_status_phase_restore_input; cbn [sem_pend_clear_status_phase_restore_pre]; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; intros heap Hheap; exact I].
Qed.
