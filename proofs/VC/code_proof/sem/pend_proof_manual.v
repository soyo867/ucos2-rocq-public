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
From Ucos2Verify.VC.code.sem Require Import pend_goal.
From Ucos2Verify.VC.code.sem Require Import pend_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_call_spec.
Require Import Ucos2Verify.lib.sched.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Local Open Scope sac.

Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cleanup_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_wait_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.

Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.

Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.

Lemma proof_of_OSSemPend_entail_wit_1_4 : OSSemPend_entail_wit_1_4.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&(pe # "os_event" ->ₛ "OSEventType")) (event_slot_type_value before.(EventState) eid)).
  prop_apply_p (store_uint_range (&("timeout")) ticks).

  asrt_simpl_pure.
  sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_entail_wit_2_1 : OSSemPend_entail_wit_2_1.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&("OSIntNesting")) before.(IntrState).(intNesting)).

  asrt_simpl_pure.
  sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_entail_wit_2_2 : OSSemPend_entail_wit_2_2.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&("OSIntNesting")) before.(IntrState).(intNesting)).

  asrt_simpl_pure.
  sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_entail_wit_2_3 : OSSemPend_entail_wit_2_3.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&("OSIntNesting")) before.(IntrState).(intNesting)).

  asrt_simpl_pure.
  sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_entail_wit_3_1 : OSSemPend_entail_wit_3_1.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&("OSLockNesting")) before.(IntrState).(lockNesting)).

  asrt_simpl_pure.
  sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_entail_wit_3_2 : OSSemPend_entail_wit_3_2.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&("OSLockNesting")) before.(IntrState).(lockNesting)).

  asrt_simpl_pure.
  sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_return_wit_1 : OSSemPend_return_wit_1.
Proof.
  unfold OSSemPend_return_wit_1; left; intros; Intros.
  rewrite <- sem_pend_continuation_phase_restore_return_output.
  assert (Hclear : sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None).
  { replace (event_slot_type_value before.(EventState) eid) with 3 by lia.
    unfold sem_pend_context_error; cbn [encode_event_type Z.eqb negb].
    rewrite (proj2 (Z.ltb_ge 0 before.(IntrState).(intNesting)) ltac:(lia)),
      (proj2 (Z.ltb_ge 0 before.(IntrState).(lockNesting)) ltac:(lia)); reflexivity. }
  assert (Hresult : sem_pend_checkpoint_result environment critical sg context pe ticks before 0
    (sem_count_update_state entry eid current_2 (encode_event_cnt_value current_2 - 1))).
  { eapply sem_pend_observed_immediate_result with (returned := first_returned) (mask := mask) (saved := retval) (observed := observed);
      eassumption || lia. }
  sep_apply_r_atomic (sem_pend_continuation_call_post_from_restore external platform environment
    critical saved_local sg context first_returned mask pe ticks pd before
    (sem_count_update_state entry eid current_2 (encode_event_cnt_value current_2 - 1)) 0 eid X
    Hresult ltac:(lia) ltac:(lia) Hclear ltac:(assumption) ltac:(assumption)).
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_return_wit_2 : OSSemPend_return_wit_2.
Proof.
  unfold OSSemPend_return_wit_2; left; intros; Intros.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  rewrite PreH4, PreH8.
  sep_apply_l_atomic (sem_pend_interrupt_merge sg before Hvalid).
  assert (Hresult : sem_pend_c_program external critical sg context pe ticks before 13 before).
  { change 13 with (encode_os_err_code OS_ERR_PEND_LOCKED); eapply sem_pend_c_context_return with (eid := eid) (observed := observed); try eassumption; try lia.
    assert (Hint : before.(IntrState).(intNesting) = 0) by lia.
    rewrite PreH9, Hint; apply sem_pend_context_error_locked; lia.
  }
  assert (Hsame : kernel_stack_call_same_call context context) by
    (unfold kernel_stack_call_same_call; repeat split; reflexivity).
  assert (Hruntime : sem_pend_runtime_program external platform environment critical sg context pe ticks before 13 before).
  { left; split; [exact Hresult|]. split; [|reflexivity].
    right; exists eid; split; [assumption|].
    assert (Hint : before.(IntrState).(intNesting) = 0) by lia.
    rewrite PreH9, Hint, sem_pend_context_error_locked by lia; discriminate. }
  sep_apply_r_atomic (sem_pend_continuation_call_post_from_result external platform environment critical saved_local sg context context mask
    pe ticks pd before before 13 X Hruntime PreH22 Hsame).
  rewrite mutex_query_closed_equiv.

  asrt_simpl_pure.
  sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_return_wit_3 : OSSemPend_return_wit_3.
Proof.
  unfold OSSemPend_return_wit_3; left; intros; Intros.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  rewrite PreH4.
  sep_apply_l_atomic (sem_pend_interrupt_merge sg before Hvalid).
  assert (Hresult : sem_pend_c_program external critical sg context pe ticks before 2 before).
  { change 2 with (encode_os_err_code OS_ERR_PEND_ISR); eapply sem_pend_c_context_return with (eid := eid) (observed := observed); try eassumption; try lia.
    rewrite PreH5; apply sem_pend_context_error_isr_before_lock; lia.
  }
  assert (Hsame : kernel_stack_call_same_call context context) by
    (unfold kernel_stack_call_same_call; repeat split; reflexivity).
  assert (Hruntime : sem_pend_runtime_program external platform environment critical sg context pe ticks before 2 before).
  { left; split; [exact Hresult|]. split; [|reflexivity].
    right; exists eid; split; [assumption|].
    rewrite PreH5, sem_pend_context_error_isr_before_lock by lia; discriminate. }
  sep_apply_r_atomic (sem_pend_continuation_call_post_from_result external platform environment critical saved_local sg context context mask
    pe ticks pd before before 2 X Hruntime PreH18 Hsame).
  rewrite mutex_query_closed_equiv.

  asrt_simpl_pure.
  sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_return_wit_4 : OSSemPend_return_wit_4.
Proof.
  unfold OSSemPend_return_wit_4; left; intros; Intros.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  rewrite PreH9.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid Hvalid).
  assert (Hresult : sem_pend_c_program external critical sg context pe ticks before 1 before).
  { change 1 with (encode_os_err_code OS_ERR_EVENT_TYPE); eapply sem_pend_c_context_return with (eid := eid) (observed := observed); try eassumption; try lia.
    apply sem_pend_context_error_type_first; assumption.
  }
  assert (Hsame : kernel_stack_call_same_call context context) by
    (unfold kernel_stack_call_same_call; repeat split; reflexivity).
  assert (Hruntime : sem_pend_runtime_program external platform environment critical sg context pe ticks before 1 before).
  { left; split; [exact Hresult|]. split; [|reflexivity].
    right; exists eid; split; [assumption|].
    rewrite sem_pend_context_error_type_first by assumption; discriminate. }
  sep_apply_r_atomic (sem_pend_continuation_call_post_from_result external platform environment critical saved_local sg context context mask
    pe ticks pd before before 1 X Hruntime PreH14 Hsame).
  rewrite mutex_query_closed_equiv.

  asrt_simpl_pure.
  sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_return_wit_5 : OSSemPend_return_wit_5.
Proof.
  unfold OSSemPend_return_wit_5; left; intros; Intros.
  assert (Hresult : sem_pend_c_program external critical sg context pe ticks before 4 before).
  { rewrite PreH6; apply sem_pend_c_null_return. }
  assert (Hsame : kernel_stack_call_same_call context context) by
    (unfold kernel_stack_call_same_call; repeat split; reflexivity).
  assert (Hruntime : sem_pend_runtime_program external platform environment critical sg context pe ticks before 4 before).
  { left; split; [exact Hresult|]. split; [left; exact PreH6|reflexivity]. }
  sep_apply_r_atomic (sem_pend_continuation_call_post_from_result external platform environment critical saved_local sg context context mask
    pe ticks pd before before 4 X Hruntime PreH5 Hsame).

  asrt_simpl_pure.
  sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_return_wit_6 : OSSemPend_return_wit_6.
Proof.
  unfold OSSemPend_return_wit_6; left; intros; Intros.
  rewrite <- sem_pend_continuation_phase_restore_return_output.
  assert (Hclear : sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None).
  { replace (event_slot_type_value before.(EventState) eid) with 3 by lia.
    unfold sem_pend_context_error; cbn [encode_event_type Z.eqb negb].
    rewrite (proj2 (Z.ltb_ge 0 before.(IntrState).(intNesting)) ltac:(lia)),
      (proj2 (Z.ltb_ge 0 before.(IntrState).(lockNesting)) ltac:(lia)); reflexivity. }
  sep_apply_r_atomic (sem_pend_continuation_call_post_from_restore external platform environment
    critical saved_local sg context second_returned mask pe ticks pd before after error eid X
    ltac:(assumption) ltac:(lia) ltac:(lia) Hclear ltac:(assumption) ltac:(assumption)).
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_return_wit_7 : OSSemPend_return_wit_7.
Proof.
  unfold OSSemPend_return_wit_7; left; intros; Intros.
  rewrite <- sem_pend_continuation_phase_restore_return_output.
  assert (Hclear : sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None).
  { replace (event_slot_type_value before.(EventState) eid) with 3 by lia.
    unfold sem_pend_context_error; cbn [encode_event_type Z.eqb negb].
    rewrite (proj2 (Z.ltb_ge 0 before.(IntrState).(intNesting)) ltac:(lia)),
      (proj2 (Z.ltb_ge 0 before.(IntrState).(lockNesting)) ltac:(lia)); reflexivity. }
  sep_apply_r_atomic (sem_pend_continuation_call_post_from_restore external platform environment
    critical saved_local sg context second_returned mask pe ticks pd before after error eid X
    ltac:(assumption) ltac:(lia) ltac:(lia) Hclear ltac:(assumption) ltac:(assumption)).
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_return_wit_8 : OSSemPend_return_wit_8.
Proof.
  unfold OSSemPend_return_wit_8; left; intros; Intros.
  rewrite <- sem_pend_continuation_phase_restore_return_output.
  assert (Hclear : sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None).
  { replace (event_slot_type_value before.(EventState) eid) with 3 by lia.
    unfold sem_pend_context_error; cbn [encode_event_type Z.eqb negb].
    rewrite (proj2 (Z.ltb_ge 0 before.(IntrState).(intNesting)) ltac:(lia)),
      (proj2 (Z.ltb_ge 0 before.(IntrState).(lockNesting)) ltac:(lia)); reflexivity. }
  sep_apply_r_atomic (sem_pend_continuation_call_post_from_restore external platform environment
    critical saved_local sg context second_returned mask pe ticks pd before after error eid X
    ltac:(assumption) ltac:(lia) ltac:(lia) Hclear ltac:(assumption) ltac:(assumption)).
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_return_wit_9 : OSSemPend_return_wit_9.
Proof.
  unfold OSSemPend_return_wit_9; left; intros; Intros.
  rewrite <- sem_pend_continuation_phase_restore_return_output.
  assert (Hclear : sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None).
  { replace (event_slot_type_value before.(EventState) eid) with 3 by lia.
    unfold sem_pend_context_error; cbn [encode_event_type Z.eqb negb].
    rewrite (proj2 (Z.ltb_ge 0 before.(IntrState).(intNesting)) ltac:(lia)),
      (proj2 (Z.ltb_ge 0 before.(IntrState).(lockNesting)) ltac:(lia)); reflexivity. }
  sep_apply_r_atomic (sem_pend_continuation_call_post_from_restore external platform environment
    critical saved_local sg context second_returned mask pe ticks pd before after error eid X
    ltac:(assumption) ltac:(lia) ltac:(lia) Hclear ltac:(assumption) ltac:(assumption)).
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_1 : OSSemPend_which_implies_wit_1.
Proof.
  unfold OSSemPend_which_implies_wit_1; left; intros.
  unfold sem_pend_error_cell; reflexivity.
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_2 : OSSemPend_which_implies_wit_2.
Proof.
  unfold OSSemPend_which_implies_wit_2; left; intros; Intros.
  assert (Hinput : sem_pend_call_input critical sg context.(os_sched_call_invocation) pe before eid observed) by assumption.
  destruct (sem_pend_call_input_nonnull _ _ _ _ _ _ _ Hinput PreH1)
    as [Haddr [Hid [Hslot Hprotocol]]].
  rewrite mutex_query_closed_equiv.
  sep_apply_l_atomic (sem_query_type_split_full sg before eid observed Hslot).
  rewrite PreH2.

  asrt_simpl_pure.
  sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_3 : OSSemPend_which_implies_wit_3.
Proof.
  unfold OSSemPend_which_implies_wit_3; left; intros; Intros.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  rewrite PreH2.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid Hvalid).
  sep_apply_l_atomic (sem_pend_interrupt_split sg before).
  rewrite PreH1.

  asrt_simpl_pure.
  sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_5 : OSSemPend_which_implies_wit_5.
Proof.
  unfold OSSemPend_which_implies_wit_5; left; intros; Intros.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  rewrite PreH1, PreH2.
  sep_apply_l_atomic (sem_pend_interrupt_merge sg before Hvalid).
  rewrite mutex_query_closed_equiv.

  asrt_simpl_pure.
  sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_6 : OSSemPend_which_implies_wit_6.
Proof.
  unfold OSSemPend_which_implies_wit_6; left; intros; Intros.
  assert (Hclear : sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None).
  { rewrite PreH2; unfold sem_pend_context_error; cbn [encode_event_type Z.eqb negb].
    rewrite (proj2 (Z.ltb_ge 0 before.(IntrState).(intNesting)) ltac:(lia)),
      (proj2 (Z.ltb_ge 0 before.(IntrState).(lockNesting)) ltac:(lia)); reflexivity. }
  unfold sem_pend_continuation_phase_save_input, sem_pend_save_phase_pre, sem_pend_continuation_save_input.
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_7 : OSSemPend_which_implies_wit_7.
Proof.
  unfold OSSemPend_which_implies_wit_7; left; intros.
  unfold sem_pend_continuation_phase_save_output; Intros returned acquired.
  Exists returned acquired.
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_8 : OSSemPend_which_implies_wit_8.
Proof.
  unfold OSSemPend_which_implies_wit_8; left; intros; Intros.
  assert (Hphase : sem_pend_save_phase_observation (SemPendAcquirePhase pe eid observed)
    environment critical sg context first_returned_2 mask cpu_sr before entry_2) by assumption.
  destruct Hphase as [current [Hacquire Hstage]].
  pose proof (sem_pend_optional_acquire_fields _ _ _ _ _ _ _ _ _ _ _ _ Hacquire)
    as [Hsame [Hsaved [Hvalid [Hbefore [Hlookup [Htype0 [Htype Hg]]]]]]].
  rewrite PreH6.
  sep_apply_l_atomic (sem_post_count_split_full sg entry_2 eid current Hlookup Htype); Intros.
  Exists current first_returned_2 entry_2.
  assert (Hphase : sem_pend_save_phase_observation (SemPendAcquirePhase pe eid observed)
    environment critical sg context first_returned_2 mask cpu_sr before entry_2)
    by (exists current; auto).
  assert (Hencoded : encode_event_type current.(eventType) = 3) by (rewrite Htype; reflexivity).
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_9 : OSSemPend_which_implies_wit_9.
Proof.
  unfold OSSemPend_which_implies_wit_9; left; intros; Intros.
  assert (Hvalid : UCOS2_state_inv sg entry_2) by assumption.
  assert (Hlookup : mutex_query_lookup entry_2 eid current_2) by assumption.
  assert (Htype : current_2.(eventType) = OS_EVENT_TYPE_SEM).
  { apply sem_query_encoded_type_is_sem; exact PreH1. }
  rewrite PreH3.
  sep_apply_l_atomic (sem_pend_count_merge_decrement sg entry_2 eid current_2 Hvalid Hlookup Htype ltac:(lia)).
  assert (Hobservation : sem_pend_stack_save_observation critical sg context first_returned_2
    environment mask cpu_sr before entry_2) by assumption.
  destruct Hobservation as [Hsame [Hsaved Hnone]].
  pose proof Hsame as [Hi [Ho Hs]].
  Exists first_returned_2 entry_2 current_2.
  unfold sem_pend_continuation_phase_restore_input, sem_pend_restore_phase_pre, sem_pend_continuation_restore_input.
  rewrite sem_pend_optional_continuation_count_update, Hi, Ho.

  asrt_simpl_pure.
  sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_10 : OSSemPend_which_implies_wit_10.
Proof.
  unfold OSSemPend_which_implies_wit_10; left; intros; Intros.
  assert (Hlayout : sem_pend_observed_blocking_layout environment critical sg context before eid
    (&("OSTCBCur")) (&("OSRdyGrp")) (&("OSRdyTbl"))) by assumption.
  assert (Hacquire : sem_pend_optional_acquire_observation environment critical sg context first_returned_2
    mask cpu_sr before entry_2 eid observed current_2) by assumption.
  destruct (Hlayout first_returned_2 mask cpu_sr entry_2 observed current_2 Hacquire ltac:(lia))
    as [Hcur [Hgrp [Htbl Hobject]]].
  Exists current_2 first_returned_2 entry_2.
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_11 : OSSemPend_which_implies_wit_11.
Proof.
  unfold OSSemPend_which_implies_wit_11; left; intros; Intros.
  assert (Hphase : sem_pend_save_phase_observation (SemPendAcquirePhase pe eid observed)
    environment critical sg context first_returned_2 mask cpu_sr before entry_2) by assumption.
  pose proof Hphase as [current [Hobserved Hstage]].
  pose proof (sem_pend_optional_acquire_fields _ _ _ _ _ _ _ _ _ _ _ _ Hobserved)
    as [_ [_ [_ [_ [Hlookup _]]]]].
  assert (Hcurrent : mutex_query_lookup entry_2 eid current_2) by assumption.
  assert (current = current_2) by congruence; subst current.
  prop_apply_p (store_ushort_range (&(pe # "os_event" ->ₛ "OSEventCnt"))
    (encode_event_cnt_value current_2)); Intros.
  assert (Hzero : encode_event_cnt_value current_2 = 0) by lia.
  specialize (Hstage Hzero).
  assert (Hclear : sem_pend_precritical_error pe (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None).
  { unfold sem_pend_precritical_error, sem_pend_context_error.
    rewrite (proj2 (Z.eqb_neq _ _) PreH3), PreH4; cbn [encode_event_type Z.eqb negb].
    rewrite (proj2 (Z.ltb_ge _ _) PreH5), (proj2 (Z.ltb_ge _ _) PreH6); reflexivity. }
  assert (Howned : sem_pend_has_stack environment).
  { eapply sem_pend_observed_zero_count_owned; eassumption. }
  Exists current_2 first_returned_2 entry_2.
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_12 : OSSemPend_which_implies_wit_12.
Proof.
  unfold OSSemPend_which_implies_wit_12; left; intros; Intros.
  assert (Hstage : sem_pend_task_call_stage sg context entry_2) by assumption.
  assert (Hacquire : sem_pend_optional_acquire_observation environment critical sg context first_returned_2
    mask cpu_sr before entry_2 eid observed current_2) by assumption.
  pose proof (sem_pend_optional_acquire_fields _ _ _ _ _ _ _ _ _ _ _ _ Hacquire)
    as [_ [_ [Hvalid [_ [Hlookup [_ [Htype _]]]]]]].
  assert (Hlayout : event_object_layout_prop sg eid) by assumption.
  prop_apply_p (store_ushort_range (&(pe # "os_event" ->ₛ "OSEventCnt"))
    (encode_event_cnt_value current_2)); Intros.
  assert (Hzero : encode_event_cnt_value current_2 = 0) by lia.
  rewrite PreH7, PreH8.
  sep_apply_l_atomic (sem_pend_acquired_wait_prefix sg context entry_2 eid current_2
    Hstage Hvalid Hlookup Htype Hzero Hlayout); Intros node.
  Exists context.(os_sched_call_stack).(stackLeaseSlot) node current_2 first_returned_2 entry_2.
  cbn [tcb_cell tcb_field_address].
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_13 : OSSemPend_which_implies_wit_13.
Proof.
  unfold OSSemPend_which_implies_wit_13; left; intros; Intros.
  assert (Horigin : sem_pend_observed_wait_origin environment critical sg context first_returned_2 mask cpu_sr before observed entry_2 eid current_2 tid_2 old_2)
    by (unfold sem_pend_observed_wait_origin; tauto).
  pose proof (proj1 (proj2 Horigin)) as Hentry.
  pose proof (sem_pend_wait_entry_row_in_range _ _ _ _ _ _ Hentry) as Hrow.
  pose proof Hentry as [Hvalid [_ [_ [Hold _]]]].
  pose proof (sem_pend_task_priority_in_range _ _ _ _ Hvalid Hold) as Hpriority.
  pose proof (sem_pend_wait_prefix_split_call sg entry_2 eid current_2 tid_2 old_2 ticks Hentry) as Hsplit.
  cbn [tcb_cell tcb_field_address] in Hsplit.
  rewrite PreH2, PreH3, PreH4, PreH5.
  sep_apply_l_atomic Hsplit.
  Exists current_2 tid_2 old_2 first_returned_2 entry_2.
  rewrite Z.quot_div_nonneg by lia.

  asrt_simpl_pure.
  sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_14 : OSSemPend_which_implies_wit_14.
Proof.
  unfold OSSemPend_which_implies_wit_14; left; intros; Intros.
  assert (Horigin : sem_pend_observed_wait_origin environment critical sg context first_returned_2 mask saved before observed entry_2 eid current tid old) by assumption.
  assert (Hobservation : sem_pend_stack_save_observation critical sg context first_returned_2
    environment mask saved before entry_2) by assumption.
  pose proof (proj1 (proj2 Horigin)) as Hentry.
  pose proof Hentry as [Hvalid [_ [_ [Hold _]]]].
  pose proof (sem_pend_task_priority_in_range _ _ _ _ Hvalid Hold) as Hpriority.
  assert (Hblocking : sem_pend_blocking_call_stage sg context entry_2).
  { assert (Hphase : sem_pend_save_phase_observation (SemPendAcquirePhase pe eid observed)
      environment critical sg context first_returned_2 mask saved before entry_2) by assumption.
    destruct Hphase as [actual [Hacquire Hstage]].
    pose proof (sem_pend_optional_acquire_fields _ _ _ _ _ _ _ _ _ _ _ _ Hacquire)
      as [_ [_ [_ [_ [Hactual _]]]]].
    pose proof Hentry as [_ [Hzero [_ [_ [Hlookup _]]]]].
    assert (actual = current) by congruence; subst actual.
    pose proof (proj2 (Hstage Hzero)) as Hneeded.
    assert (Howned : sem_pend_has_stack environment) by assumption.
    destruct environment as [owned|]; [exact Hneeded|].
    destruct Howned as [owned Howned]; discriminate. }
  rewrite PreH1, PreH2, PreH3, PreH4.
  rewrite Z.quot_div_nonneg by lia.
  pose proof (sem_pend_continuation_wait_restore_input external platform environment critical saved_local sg
    context first_returned_2 mask saved before observed entry_2 eid current tid old ticks
    Horigin Hobservation) as Hmerge.
  pose proof (sem_pend_observed_wait_origin_history environment critical sg context first_returned_2
    mask saved before observed entry_2 eid current tid old ticks Horigin) as Hhistory.
  pose proof (proj1 Hobservation) as Hsame.
  pose proof Horigin as [_ [_ [_ [Hsource Hcache]]]].
  assert (Hconfiguration : kernel_tcb_stack_field_layout sg) by assumption.
  pose proof (sem_pend_blocking_wait_sched_call_cut sg context first_returned_2
    entry_2 eid current tid old ticks Hentry Hsource Hcache Hsame Hblocking Hconfiguration) as Hsched.
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  assert (Hwait_post :
    event_task_wait_post sg.(g_OSTCBCur) (task_slot_addr sg tid) (event_addr sg eid)
      sg.(g_OSRdyGrp) sg.(g_OSRdyTbl) (old.(curPrio) / 8)
      (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
      (encode_event_wait_tbl_at_or current.(waitList) entry_2.(TskState) (old.(curPrio) / 8))
      (encode_event_wait_grp current.(waitList) entry_2.(TskState))
      (encode_ready_tbl_at_or entry_2.(SchedState).(readyList) entry_2.(TskState) (old.(curPrio) / 8))
      (encode_ready_grp entry_2.(SchedState).(readyList) entry_2.(TskState)) **
    sem_pend_wait_call_frame sg entry_2 eid current tid old ticks |--
    sem_pend_wait_call_post sg entry_2 eid current tid old ticks).
  { unfold sem_pend_wait_call_post; entailer!. }
  sep_apply_l_atomic Hwait_post.
  sep_apply_l_atomic Hmerge.
  Intros.
  Exists entry_2 first_returned_2 (event_pend_state sg entry_2 eid current tid old PendSem ticks) saved.
  assert (Hphase : sem_pend_restore_phase_pre
    (SemPendWaitPhase context mask before observed eid ticks
      (event_pend_state sg entry_2 eid current tid old PendSem ticks))
    environment critical sg first_returned_2 mask
      (event_pend_state sg entry_2 eid current tid old PendSem ticks)).
  { split; [reflexivity|]. split; [apply sem_pend_wait_at_waiting; assumption|exact Hsched]. }
  unfold sem_pend_continuation_phase_restore_input.

  asrt_simpl_pure.
  sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
  all: first [exact (proj1 (proj2 H4)) | exact (proj2 (proj2 (proj2 H4)))].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_15 : OSSemPend_which_implies_wit_15.
Proof.
  unfold OSSemPend_which_implies_wit_15; left; intros; Intros.
  assert (Hvalid : UCOS2_state_inv sg waiting_2) by assumption.
  assert (Hsource : kernel_call_task_source first_returned waiting_2) by assumption.
  assert (Hsame : kernel_stack_call_same_call first_returned context) by assumption.
  unfold sem_pend_continuation_phase_restore_output; Intros returned current_state.
  assert (Hobservation : sem_pend_stack_restore_observation sg first_returned returned
    environment waiting_2 current_state) by tauto.
  assert (Hwait : sem_pend_wait_at environment critical sg context mask before observed eid ticks
    waiting_2 returned current_state) by (unfold sem_pend_restore_phase_pre in *; tauto).
  assert (Hsched : sem_pend_wait_sched_entry sg returned current_state)
    by (unfold sem_pend_restore_phase_pre in *; tauto).
  pose proof Hwait as [owned [Howned [Hjoined [Hhistory Hpath]]]].
  subst environment.
  pose proof Hobservation as [Hreturned Hpreserve].
  pose proof (Hpreserve Hvalid Hsource) as Hcurrent_source.
  pose proof Hreturned as [Hi [Ho Hs]].
  unfold sem_pend_optional_continuation_resources; Intros.
  assert (He : owned.(task_stack_call_external) = external) by tauto.
  assert (Hp : owned.(task_stack_call_platform) = platform) by tauto.
  unfold mutex_query_closed; Intros.
  Exists returned current_state waiting_2.
  unfold sem_pend_continuation_phase_sched_input, sem_pend_continuation_sched_input, os_sched_continuation_pre.
  rewrite <- (task_tcb_init_continuation_save_input_closed_world owned critical saved_local sg returned mask current_state).
  unfold task_tcb_init_continuation_save_input, task_create_continuation_input,
    task_tcb_init_continuation_capsules, kernel_call_execution_owned, mutex_query_closed.
  rewrite <- He, <- Hp, Hi, Ho.
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_16 : OSSemPend_which_implies_wit_16.
Proof.
  unfold OSSemPend_which_implies_wit_16; left; intros; Intros.
  unfold sem_pend_continuation_phase_sched_output; Intros returned current.
  assert (Hwait : sem_pend_wait_selected_at environment critical sg context mask before observed eid ticks
    waiting_2 returned current) by tauto.
  pose proof Hwait as [[owned [Howned [Hsame Hhistory]]] [node [Hvalid Hresume]]].
  Exists current returned waiting_2.
  unfold sem_pend_continuation_phase_save_input, sem_pend_save_phase_pre.
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_17 : OSSemPend_which_implies_wit_17.
Proof.
  unfold OSSemPend_which_implies_wit_17; left; intros; Intros.
  assert (Hsame : kernel_stack_call_same_call returned_2 context) by assumption.
  unfold sem_pend_continuation_phase_save_output; Intros second current.
  assert (Hreturned : kernel_stack_call_same_call second returned_2) by
    (unfold sem_pend_stack_save_observation in *; tauto).
  destruct Hsame as [Hi [Ho Hs]]; destruct Hreturned as [Hi' [Ho' Hs']].
  assert (Hjoined : kernel_stack_call_same_call second context).
  { unfold kernel_stack_call_same_call; repeat split; congruence. }
  Exists scheduled_2 current second returned_2 waiting_2.
  rewrite Hi, Ho.
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_18 : OSSemPend_which_implies_wit_18.
Proof.
  unfold OSSemPend_which_implies_wit_18; left; intros; Intros.
  assert (Hwait : sem_pend_wait_selected_at environment critical sg context mask before observed eid ticks
    waiting second_returned_2 resumed_2) by assumption.
  destruct (sem_pend_wait_selected_resume_origin _ _ _ _ _ _ _ _ _ _ _ _ Hwait) as [node Horigin].
  pose proof Horigin as [[Hvalid [Hcurrent [Hnode Hrest]]] _].
  assert (Hsaved : interrupt_saved_value mask cpu_sr)
    by (unfold sem_pend_stack_save_observation in *; tauto).
  rewrite PreH1.
  sep_apply_l_atomic (sem_pend_cleanup_split sg resumed_2 context.(os_sched_call_stack).(stackLeaseSlot)
    node Hvalid Hcurrent Hnode).
  Exists resumed_2 context.(os_sched_call_stack).(stackLeaseSlot) node second_returned_2.
  cbn [tcb_cell tcb_field_address].
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_19 : OSSemPend_which_implies_wit_19.
Proof.
  unfold OSSemPend_which_implies_wit_19; left; intros; Intros.
  assert (Horigin : sem_pend_observed_resume_origin environment critical sg context mask before observed eid ticks resumed tid_2 old) by assumption.
  assert (Hstatus : old.(statPend) = PendOK)
    by (destruct old.(statPend); cbn [encode_pend_status] in *; congruence).
  pose proof (sem_pend_observed_resume_cleanup_without_timeout environment critical sg context mask before observed eid ticks resumed tid_2 old
    Horigin ltac:(rewrite Hstatus; discriminate)) as Hcleanup.
  rewrite Hstatus in Hcleanup; cbn [encode_pend_status sem_pend_resume_error encode_os_err_code] in Hcleanup.
  Exists resumed tid_2 old second_returned_2.

  asrt_simpl_pure.
  sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_20 : OSSemPend_which_implies_wit_20.
Proof.
  unfold OSSemPend_which_implies_wit_20; left; intros; Intros.
  assert (Horigin : sem_pend_observed_resume_origin environment critical sg context mask before observed eid ticks resumed tid_2 old) by assumption.
  assert (Hstatus : old.(statPend) = PendAbort)
    by (destruct old.(statPend); cbn [encode_pend_status] in *; congruence).
  pose proof (sem_pend_observed_resume_cleanup_without_timeout environment critical sg context mask before observed eid ticks resumed tid_2 old
    Horigin ltac:(rewrite Hstatus; discriminate)) as Hcleanup.
  rewrite Hstatus in Hcleanup; cbn [encode_pend_status sem_pend_resume_error encode_os_err_code] in Hcleanup.
  Exists resumed tid_2 old second_returned_2.

  asrt_simpl_pure.
  sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_21 : OSSemPend_which_implies_wit_21.
Proof.
  unfold OSSemPend_which_implies_wit_21; left; intros; Intros.
  assert (Horigin : sem_pend_observed_resume_origin environment critical sg context mask before observed eid ticks resumed tid_2 old) by assumption.
  pose proof (proj1 Horigin) as Hentry.
  pose proof Hentry as [Hvalid [Hcur [Hold _]]].
  assert (He : mutex_query_lookup resumed eid current) by assumption.
  assert (Hlayout : event_object_layout_prop sg eid) by assumption.
  assert (Htimeout : old.(statPend) = PendTimeout)
    by (destruct old.(statPend); cbn [encode_pend_status] in *; congruence).
  pose proof (sem_pend_task_priority_in_range _ _ _ _ Hvalid Hold) as Hpriority.
  assert (Hstacks : sem_pend_optional_continuation_resources external platform environment saved_local second_returned_2 resumed |--
    sem_pend_optional_continuation_resources external platform environment saved_local second_returned_2
      (event_task_remove_state resumed eid current tid_2 old)).
  { change (sem_pend_optional_continuation_resources external platform environment saved_local
      second_returned_2 resumed |--
      sem_pend_optional_continuation_resources external platform environment saved_local
        second_returned_2 (replace_TskS
          (glob_task_set_usedtask resumed.(TskState) tid_2 (task_set_event_ptr old None)) resumed)).
    apply sem_pend_optional_continuation_task_update with (old := old);
      assumption || reflexivity. }
  sep_apply_l_atomic Hstacks.
  pose proof (sem_pend_observed_resume_cleanup_timeout environment critical sg context mask before observed eid ticks resumed tid_2 old current Horigin Htimeout He) as Hcleanup.
  pose proof (proj1 Hcleanup) as [Hclean [Hcurrent [Hnode Hrest]]].
  rewrite PreH3, PreH4; rewrite Z.quot_div_nonneg by lia.
  sep_apply_l_atomic (sem_pend_observed_timeout_remove_cleanup environment critical sg context mask before
    observed eid ticks resumed tid_2 old current Horigin Htimeout He Hlayout); Intros.
  pose proof (sem_pend_cleanup_split sg (event_task_remove_state resumed eid current tid_2 old)
    tid_2 (task_set_event_ptr old None) Hclean Hcurrent Hnode) as Hsplit.
  cbn [tcb_cell tcb_field_address] in Hsplit; sep_apply_l_atomic Hsplit.
  Exists (event_task_remove_state resumed eid current tid_2 old) tid_2 (task_set_event_ptr old None) second_returned_2.

  asrt_simpl_pure.
  sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_22 : OSSemPend_which_implies_wit_22.
Proof.
  unfold OSSemPend_which_implies_wit_22; left; intros; Intros.
  assert (Horigin : sem_pend_observed_resume_origin environment critical sg context mask before observed eid ticks resumed_2 tid_2 old_2) by assumption.
  pose proof (proj1 Horigin) as Hentry.
  assert (Hlayout : event_object_layout_prop sg eid) by assumption.
  pose proof Hentry as [Hvalid [Hcur [Hold [Hregistration Hready]]]].
  pose proof (sem_pend_task_priority_in_range _ _ _ _ Hvalid Hold) as Hpriority.
  assert (Htimeout : old_2.(statPend) = PendTimeout)
    by (destruct old_2.(statPend); cbn [encode_pend_status] in *; congruence).
  assert (Hptr : old_2.(eventPtr) = Some eid).
  { destruct Hregistration as [_ [_ Hregistration]]; rewrite Htimeout in Hregistration; exact Hregistration. }
  destruct (sem_pend_resume_timeout_event sg resumed_2 eid tid_2 old_2 Hvalid Hold Hptr)
    as [current [Hlookup Hin]].
  pose proof (sem_pend_resume_split_remove_call sg resumed_2 eid tid_2 old_2 current Hentry Hlookup Hlayout) as Hsplit.
  cbn [tcb_cell tcb_field_address] in Hsplit.
  rewrite PreH3, PreH4.
  sep_apply_l_atomic Hsplit.
  Exists current resumed_2 tid_2 old_2 second_returned_2.
  rewrite Z.quot_div_nonneg by lia.

  asrt_simpl_pure.
  sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSSemPend_which_implies_wit_23 : OSSemPend_which_implies_wit_23.
Proof.
  unfold OSSemPend_which_implies_wit_23; left; intros; Intros.
  assert (Horigin : sem_pend_observed_cleanup_origin environment critical sg context mask before observed
    eid ticks error_2 cleaning tid node) by assumption.
  pose proof (proj1 Horigin) as Hentry.
  pose proof Hentry as [Hvalid [Hcurrent [Hnode _]]].
  assert (Hsaved : interrupt_saved_value mask cpu_sr)
    by (tauto).
  assert (Hsame : kernel_stack_call_same_call second_returned_2 context) by assumption.
  assert (Hstacks : sem_pend_optional_continuation_resources external platform environment saved_local second_returned_2 cleaning |--
    sem_pend_optional_continuation_resources external platform environment saved_local second_returned_2
      (event_pend_cleanup_state sg false cleaning tid node)).
  { unfold event_pend_cleanup_state.
    apply sem_pend_optional_continuation_task_update with (old := node).
    - exact Hnode.
    - destruct sg.(osKernelConfig).(cfgEventMultiEnabled); reflexivity.
    - destruct sg.(osKernelConfig).(cfgEventMultiEnabled); reflexivity. }
  sep_apply_l_atomic Hstacks.
  assert (Hordered : sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None).
  { rewrite PreH3, PreH4, PreH5; reflexivity. }
  assert (Hid : valid_event_id sg eid) by assumption.
  assert (Hslot : sem_query_public_slot before eid observed) by assumption.
  pose proof (sem_pend_observed_cleanup_return_merge environment critical sg context mask before observed
    eid pe ticks error_2 cleaning tid node PreH1 PreH2 Hid Hslot Hordered Horigin) as Hmerge.
  unfold sem_pend_cleanup_cells in Hmerge; cbn [tcb_cell tcb_field_address] in Hmerge.
  rewrite PreH6.
  sep_apply_l_atomic Hmerge; Intros.
  Exists acquired_2 second_returned_2 error_2 (event_pend_cleanup_state sg false cleaning tid node).
  pose proof Hsame as [Hi [Ho Hs]].
  unfold sem_pend_continuation_phase_restore_input, sem_pend_restore_phase_pre, sem_pend_continuation_restore_input; rewrite Hi, Ho.
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

