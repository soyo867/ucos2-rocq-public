Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_type_source_spec.
Import UCOS2_C_Rules EventStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The selected64 wrapper takes the actual SP-indexed strong descriptor,
    then exchanges CPU authority. The current whole pool is part of that
    SAME endpoint, not a frame kept across the preceding arbitrary client
    interval. Its reindexing is valid because this last actual transition
    only removes a Task continuation and leaves Event unchanged. *)
Lemma mutex_del_private_pool_selected_call_return : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg focus fragments state
  handler (frame : Assertion) heap,
  let incoming := focus.(armv7a_focus_call).(os_sched_call_stack) in
  task_current_at state incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  event_private_types_defined state.(EventState) ->
  (kernel_client_call_stack_world abi sg focus (incoming.(stackLeaseRegion), fragments) state **
    (interrupt_platform_running platform handler.(os_int_exit_invocation)
       handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
     (event_private_pool_rep sg state.(EventState) ** frame))) heap ->
  let restored := os_int_exit_wrapper_restored_state state incoming in
  exists saved,
    armv7a_irq_restore_pointer_reads sg heap (task_slot_addr sg incoming.(stackLeaseSlot))
      saved.(armv7a_continuation_sp) /\
    armv7a_continuation_focus_binding focus saved /\
    (forall final, armv7a_restore_transition abi handler saved heap final ->
      final.(ConAssertion.s_mem) = heap.(ConAssertion.s_mem) /\
      event_private_types_defined restored.(EventState) /\
      (kernel_call_execution_owned external platform
         (armv7a_continuation_resumed_call saved focus.(armv7a_focus_call))
         (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
       (kernel_stack_inv abi
         (fun sg state => kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState))
         sg (Some (task_stack_key incoming)) restored ** frame)) final).
Proof.
  intros external platform port abi sg focus fragments state handler frame heap incoming
    Hcurrent Haddress Htypes Hpre restored.
  destruct (kernel_client_call_stack_resume external platform port abi sg focus fragments state handler
    (event_private_pool_rep sg state.(EventState) ** frame) heap Hcurrent Haddress Hpre)
    as [saved [Hpointers [Hbinding [Hcoverage Hreturn]]]].
  exists saved; split; [exact Hpointers|]. split; [exact Hbinding|].
  intros final Hrun; destruct (Hreturn final Hrun) as [Hmemory Hpost].
  assert (Hevent : restored.(EventState) = state.(EventState)) by reflexivity.
  split; [exact Hmemory|]. split; [rewrite Hevent; exact Htypes|].
  match type of Hpost with ?P final => assert (Hclose : P |--
    kernel_call_execution_owned external platform
      (armv7a_continuation_resumed_call saved focus.(armv7a_focus_call))
      (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
    (kernel_stack_inv abi
      (fun sg state => kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState))
      sg (Some (task_stack_key incoming)) restored ** frame)) end.
  { unfold kernel_stack_inv; rewrite kernel_program_inv_split_unmap, Hevent; entailer!. }
  exact (Hclose final Hpost).
Qed.
