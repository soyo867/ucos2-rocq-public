Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_heap_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OS_SchedNew reads the same initialized OSUnMapTbl owned by the whole
    program. Opening this masked fragment does not manufacture a table or
    leave a second copy in its frame. The remaining modules are unchanged.
    This is a concrete heap-fragment theorem, not a proof that a ready task
    exists or that a context switch is safe. *)
Lemma kernel_program_rep_split_sched_new : forall sg state,
  kernel_program_rep sg state --||--
  sched_new_rep sg (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
    (sched_row_values state.(TskState) state.(SchedState).(readyList))
    (sched_priority_byte state.(SchedState).(highRdyPrio)) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg state.(SchedState).(highRdyTid) **
  sched_physical_without_high sg state.(SchedState) **
  UCOS2_raw_rep_missing_module sg state SchedModule.
Proof.
  intros sg state; unfold kernel_program_rep.
  rewrite (UCOS2_raw_rep_split_module sg state SchedModule).
  cbn [UCOS2_module_rep].
  rewrite <- sched_raw_rep_sched_new_equiv.
  split; entailer!.
Qed.

Lemma kernel_program_rep_merge_sched_priority_write : forall sg state,
  sched_new_rep sg (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
    (sched_row_values state.(TskState) state.(SchedState).(readyList))
    (sched_new_priority (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
      (sched_row_values state.(TskState) state.(SchedState).(readyList))) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg state.(SchedState).(highRdyTid) **
  sched_physical_without_high sg state.(SchedState) **
  UCOS2_raw_rep_missing_module sg state SchedModule |--
  kernel_program_rep sg
    (replace_SchedS (sched_priority_write_state state.(TskState) state.(SchedState)) state).
Proof.
  intros sg state.
  rewrite sched_new_rep_after_priority_write_equiv.
  unfold kernel_program_rep.
  rewrite (UCOS2_raw_rep_split_module sg
    (replace_SchedS (sched_priority_write_state state.(TskState) state.(SchedState)) state)
    SchedModule).
  cbn [UCOS2_module_rep replace_SchedS TskState SchedState].
  assert (Hframe : UCOS2_raw_rep_missing_module sg state SchedModule =
    UCOS2_raw_rep_missing_module sg
      (replace_SchedS (sched_priority_write_state state.(TskState) state.(SchedState)) state)
      SchedModule) by reflexivity.
  rewrite <- Hframe; entailer!.
Qed.

Lemma kernel_program_sched_new_heap_post : forall sg state (frame : Assertion) before,
  (kernel_program_rep sg state ** frame) before ->
  exists after, sched_new_heap_fragment sg before after /\
    (kernel_program_rep sg
      (replace_SchedS (sched_priority_write_state state.(TskState) state.(SchedState)) state) **
     frame) after.
Proof.
  intros sg state frame before Hbefore.
  assert (Hsplit : kernel_program_rep sg state ** frame |--
    sched_new_rep sg (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
      (sched_row_values state.(TskState) state.(SchedState).(readyList))
      (sched_priority_byte state.(SchedState).(highRdyPrio)) **
    (sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg state.(SchedState).(highRdyTid) **
     sched_physical_without_high sg state.(SchedState) **
     UCOS2_raw_rep_missing_module sg state SchedModule ** frame)).
  { rewrite kernel_program_rep_split_sched_new; entailer!. }
  destruct (sched_new_heap_fragment_frame_post sg _ _ _ _ before (Hsplit before Hbefore))
    as [after [Hsource Hafter]].
  exists after; split; [exact Hsource|].
  assert (Hmerge :
    sched_new_rep sg (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
      (sched_row_values state.(TskState) state.(SchedState).(readyList))
      (sched_new_priority (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
        (sched_row_values state.(TskState) state.(SchedState).(readyList))) **
    (sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg state.(SchedState).(highRdyTid) **
     sched_physical_without_high sg state.(SchedState) **
     UCOS2_raw_rep_missing_module sg state SchedModule ** frame) |--
    kernel_program_rep sg
      (replace_SchedS (sched_priority_write_state state.(TskState) state.(SchedState)) state) **
    frame).
  { sep_apply_l_atomic (kernel_program_rep_merge_sched_priority_write sg state); entailer!. }
  exact (Hmerge after Hafter).
Qed.
