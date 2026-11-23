Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The final real OS_CPU_SR_Restore supplies the internal return join used
    by OSTaskCreate. Its input owns the CURRENT whole continuation map; no
    old map is framed through a switch. This covers two adjacent local
    Restore transitions, not an intervening IRQ or the scheduler prefix. *)
Lemma task_create_stack_restore_success_from_source :
  forall environment critical arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg original returned saved entry state cursor before written_cursor middle final_cursor after
    (frame : Assertion),
  task_tcb_init_stack_same_call returned original ->
  task_stack_live_coverage state.(TskState) (task_stack_call_active_key returned) ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     returned.(os_sched_call_invocation) returned.(os_sched_call_origin) saved entry **
   task_tcb_init_stack_context environment returned ** UCOS2_inv sg state **
   task_tcb_init_stack_covered_capsules environment state ** unmap_table_rep sg ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written_cursor middle ->
  armv7a_restore_suffix_transition restore written_cursor middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (task_create_stack_covered_success_post environment critical sg original
     (armv7a_irq_fiq_mask saved) ** frame) after.
Proof.
  intros environment critical arch restore sg original returned saved entry state cursor before
    written_cursor middle final_cursor after frame Hsame Hcoverage Hr0 Hmask Hpre Hprefix Hsuffix.
  match type of Hpre with ?P before =>
    assert (Horder : P |-- critical_region_masked environment.(task_stack_call_platform) critical sg
      returned.(os_sched_call_invocation) returned.(os_sched_call_origin) saved entry **
      task_tcb_init_stack_context environment returned ** UCOS2_inv sg state **
      task_tcb_init_stack_covered_capsules environment state ** (unmap_table_rep sg ** frame))
  end.
  { entailer!. }
  destruct (task_tcb_init_stack_covered_uninterrupted_restore environment critical arch restore sg
    returned saved entry state cursor before written_cursor middle final_cursor after _
    Hcoverage Hr0 Hmask (Horder before Hpre) Hprefix Hsuffix) as [Hsource [Hreturn Hafter]].
  split; [exact Hsource|]. split; [exact Hreturn|].
  match type of Hafter with ?P after =>
    assert (Hclose : P |-- task_create_stack_covered_success_post environment critical sg original
      (armv7a_irq_fiq_mask saved) ** frame)
  end.
  { unfold task_create_stack_covered_success_post; Exists returned state; entailer!. }
  exact (Hclose after Hafter).
Qed.

(** Real selected-frame restoration followed by the caller's final Restore.
    The first input is precisely the full-map endpoint of
    os_sched_install_take_call_continuation. Its restore-reads result also
    carries the descriptor binding: key equality alone is NOT enough to
    equate an entire stack lease. The saved token and inside handle belong
    to the original OS_Sched invocation and are consumed once at MSR.

    Register joins below belong to the actual source cut, not the public
    Create Require and not a new CPU guarantee. The postcondition is the
    same internal join used in the annotated C. Earlier saves/hooks and
    an IRQ between the final MSR/BX still need their own source producers. *)
Lemma task_create_stack_selected_restore_success :
  forall environment critical arch
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg outgoing original selected pc lr saved entry state installed restored
    cursor written_cursor middle final_cursor after (frame : Assertion),
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_focus_binding (armv7a_call_focus original pc lr) selected ->
  armv7a_continuation_restore_reads selected installed ->
  armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) = 192 ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key selected.(armv7a_continuation_stack))) ->
  (armv7a_task_switch_control task_abi outgoing **
   task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
     selected.(armv7a_continuation_fragments) **
   armv7a_task_continuation_resource environment.(task_stack_call_continuations) selected **
   UCOS2_inv sg state **
   armv7a_task_call_stacks environment.(task_stack_call_continuations) state.(TskState)
     (armv7a_call_focus original pc lr) state.(TskState).(parkedTaskStacks) **
   interrupt_platform_saved environment.(task_stack_call_platform)
     (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
   critical_region_inside critical sg original.(os_sched_call_invocation) entry **
   unmap_table_rep sg ** frame) installed ->
  armv7a_task_restore_transition task_abi outgoing selected installed restored ->
  cursor.(kernel_restore_r0) = saved ->
  cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
  armv7a_restore_prefix_transition restore cursor restored written_cursor middle ->
  armv7a_restore_suffix_transition restore written_cursor middle final_cursor after ->
  selected.(armv7a_continuation_pc) = pc /\ selected.(armv7a_continuation_lr) = lr /\
  kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (task_create_stack_covered_success_post environment critical sg original
    (armv7a_irq_fiq_mask saved) ** frame) after.
Proof.
  intros environment critical arch task_abi restore sg outgoing original selected pc lr saved entry
    state installed restored cursor written_cursor middle final_cursor after frame
    Horigin Hfocus Hreads Hmask Hcoverage Hpre Htask_restore Hr0 Hcpsr Hprefix Hsuffix.
  destruct Hfocus as [Hcall [Hpc Hlr]].
  cbn [armv7a_call_focus armv7a_focus_call armv7a_focus_pc armv7a_focus_lr] in Hcall, Hpc, Hlr.
  assert (Hlease : selected.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { pose proof (proj1 Hreads) as Hbinding.
    unfold armv7a_continuation_binding in Hbinding; rewrite Hcall in Hbinding.
    symmetry; exact (proj2 Hbinding). }
  set (returned := armv7a_continuation_resumed_call selected original).
  assert (Hsame : task_tcb_init_stack_same_call returned original).
  { unfold returned, armv7a_continuation_resumed_call, task_tcb_init_stack_same_call; cbn; auto. }
  assert (Hcovered : task_stack_live_coverage state.(TskState) (task_stack_call_active_key returned)).
  { unfold task_stack_call_active_key, returned, armv7a_continuation_resumed_call.
    cbn [os_sched_call_origin]; rewrite Horigin; rewrite Hlease in Hcoverage; exact Hcoverage. }
  match type of Hpre with ?P installed =>
    assert (Horder : P |-- armv7a_task_switch_control task_abi outgoing **
      task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
        selected.(armv7a_continuation_fragments) **
      armv7a_task_continuation_resource environment.(task_stack_call_continuations) selected **
      (UCOS2_inv sg state **
       armv7a_task_call_stacks environment.(task_stack_call_continuations) state.(TskState)
         (armv7a_call_focus original pc lr) state.(TskState).(parkedTaskStacks) **
       interrupt_platform_saved environment.(task_stack_call_platform)
         (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
       critical_region_inside critical sg original.(os_sched_call_invocation) entry **
       unmap_table_rep sg ** frame))
  end.
  { entailer!. }
  destruct (armv7a_task_restore_resources _ _ _ _ task_abi outgoing selected _ installed restored
    Hreads (Horder installed Hpre) Htask_restore) as [Hmemory [Hsource Hrestored]].
  unfold armv7a_task_restored_execution in Hrestored; rewrite Hcall, Hmask in Hrestored.
  fold returned in Hrestored.
  match type of Hrestored with ?P restored =>
    assert (Hrestore_input : P |-- critical_region_masked environment.(task_stack_call_platform) critical sg
      returned.(os_sched_call_invocation) returned.(os_sched_call_origin) saved entry **
      task_tcb_init_stack_context environment returned ** UCOS2_inv sg state **
      task_tcb_init_stack_covered_capsules environment state ** unmap_table_rep sg ** frame)
  end.
  { sep_apply_l_atomic (armv7a_task_call_stacks_forget _ _ _ environment.(task_stack_call_continuations)
      state.(TskState) (armv7a_call_focus original pc lr) state.(TskState).(parkedTaskStacks)).
    unfold kernel_call_execution_owned, critical_region_masked,
      task_tcb_init_stack_context, task_tcb_init_stack_covered_capsules.
    unfold returned, armv7a_continuation_resumed_call.
    cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack
      os_sched_call_fragments].
    entailer!. }
  split; [exact Hpc|]. split; [exact Hlr|].
  eapply task_create_stack_restore_success_from_source; try eassumption.
  - rewrite Hcpsr; exact Hmask.
  - exact (Hrestore_input restored Hrestored).
Qed.
