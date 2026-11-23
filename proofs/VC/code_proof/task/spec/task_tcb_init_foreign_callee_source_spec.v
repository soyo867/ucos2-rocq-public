Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_foreign_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_registered_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_switch_capture_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Actual foreign save -> capture -> reference hook -> original install -> original
    restore -> TCBInit's public callee post, on one succession of heaps.
    The original no-free/publication result is an already executed branch;
    it is never reconstructed from successful resumption. In particular
    no-free retains its initialized stack for the caller's rollback.

    [history] is the output of the preceding registered source trace. The
    high-ready destination guard observes this captured state. Other
    destinations continue their own execution rather than satisfying this
    return theorem. The reference hook's empty memory and state effect is
    the same explicit source boundary used by the existing switch source.
    No termination of application code is assumed. *)
Lemma task_tcb_init_foreign_capture_callee_return :
  forall environment critical arch
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg region args task_return lower upper initial_name invocation origin initial result
    original suspended released state node call old_sp cpsr registers lr prefix suffix first old_words
    publication saved acquired (frame : Assertion) before,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let retained := interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) acquired **
    task_tcb_init_stack_buffer_result region args task_return lower upper result ** frame in
  task_tcb_init_stack_call_result critical sg region args task_return lower upper initial_name
    invocation origin initial result released ->
  UCOS2_state_inv sg released ->
  task_tcb_init_stack_source_preserved original initial released ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released state ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended -> armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  call.(os_sched_call_stack).(stackLeaseSlot) <> original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  os_sched_source_live_save_input sg state node call old_sp cpsr registers lr
    prefix suffix first old_words focus publication ->
  (os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
     environment.(task_stack_call_port) abi sg call focus state ** unmap_table_rep sg ** retained) before ->
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  let foreign_saved := armv7a_task_save_image call old_sp cpsr registers lr fragments in
  let updated := os_sched_save_current_sp state call.(os_sched_call_stack).(stackLeaseSlot)
    foreign_saved.(armv7a_continuation_sp) in
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      foreign_saved.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi call foreign_saved stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
      os_sched_destination_binding environment.(task_stack_call_external) call fragments updated
        original.(os_sched_call_stack) suspended.(armv7a_continuation_fragments) ->
      exists installed selected,
        sched_install_heap_fragment sg hooked installed
          (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
        selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
        selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
        (forall restored,
          armv7a_task_restore_transition task_abi call selected installed restored ->
          forall cursor restore_written middle final_cursor after,
          cursor.(kernel_restore_r0) = saved ->
          cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
          armv7a_restore_prefix_transition restore cursor restored restore_written middle ->
          armv7a_restore_suffix_transition restore restore_written middle final_cursor after ->
          kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
          (task_tcb_init_stack_call_post environment critical sg region args task_return lower upper initial_name
             invocation origin (armv7a_irq_fiq_mask saved) initial original result **
           unmap_table_rep sg ** frame) after)).
Proof.
  intros environment critical arch task_abi restore sg region args task_return lower upper initial_name
    invocation origin initial result original suspended released state node call old_sp cpsr registers lr
    prefix suffix first old_words publication saved acquired frame before abi focus retained
    Hresult Hreleased Hordinary Hhistory Horigin Hbinding Hcall Hslice Hmask Hdifferent Hpointer Hinput Hpre
    fragments foreign_saved updated.
  pose proof Hinput as Hgeometry.
  destruct Hgeometry as [Hcurrent [Hnode [Hid [Hgen [Hnone [Hhigh [Hnonempty [Hfocus [Hfragments
    [Hregion [Hbounds [Hsp_range [Hpublication [Hlength [Hcpsr [Hlr [Hranges [Hmask_foreign [Hsp32
      [Hsp Haddress]]]]]]]]]]]]]]]]]]]].
  destruct (task_tcb_init_switch_capture_source environment task_abi sg original suspended released state node
    call old_sp cpsr registers lr prefix suffix first old_words publication retained before Hhistory Hinput Hpre)
    as [written [stored [Hwrites [Hload [Hstore Hcapture]]]]].
  fold fragments foreign_saved updated in Hstore, Hcapture.
  assert (Hlease : suspended.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  assert (Hpointer_after : task_saved_pointer_at updated suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp)).
  { destruct Hpointer as [original_node [Hlookup [Hg Hpointer]]].
    exists original_node; split; [|auto].
    unfold updated, os_sched_save_current_sp; rewrite Hnode.
    cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
    assert (Heq : (suspended.(armv7a_continuation_stack).(stackLeaseSlot) =?
      call.(os_sched_call_stack).(stackLeaseSlot)) = false) by
      (apply Z.eqb_neq; rewrite Hlease; congruence).
    rewrite Heq; exact Hlookup. }
  exists written, stored; split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcaptured Hhook_heap Hhook_step Hdestination.
  assert (Hhook_eq : hooked = captured).
  { eapply kernel_heap_execution_deterministic; [exact Hhook_heap|].
    split; [constructor|]; split; reflexivity. }
  subst hooked.
  destruct (Hcapture captured Hcaptured) as [Hsave_source [Hhistory_after Hcaptured_owned]].
  match type of Hcaptured_owned with ?P captured => assert (Hopen : P |--
    coq_prop (os_sched_saved_stack_binding call fragments updated /\
      sched_high_ready_consistency updated.(TskState) updated.(SchedState) /\
      updated.(SchedState).(readyList) <> [] /\
      task_stack_live_coverage updated.(TskState) (Some (task_stack_key call.(os_sched_call_stack)))) &&
    (UCOS2_inv sg updated **
     task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
     armv7a_task_call_stack_entry abi updated.(TskState) focus (task_stack_key call.(os_sched_call_stack))
       (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
     armv7a_task_call_stacks abi updated.(TskState) focus updated.(TskState).(parkedTaskStacks) **
     (armv7a_task_switch_control task_abi call **
      (interrupt_platform_saved environment.(task_stack_call_platform)
         (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
       critical_region_inside critical sg original.(os_sched_call_invocation) acquired ** unmap_table_rep sg **
       (task_tcb_init_stack_buffer_result region args task_return lower upper result ** frame))))) end.
  { unfold task_tcb_init_switch_capture, retained; entailer!. }
  destruct (Hopen captured Hcaptured_owned) as [[Hsaved [Hhigh_after [Hnonempty_after Hcoverage]]] Howned].
  destruct (task_tcb_init_foreign_switch_return environment critical arch task_abi restore sg original released
    call fragments updated suspended saved acquired captured
    (task_tcb_init_stack_buffer_result region args task_return lower upper result ** frame)
    Hreleased Hhistory_after Horigin Hbinding Hcall Hslice Hmask Hsaved Hdestination Hhigh_after Hnonempty_after
    Hpointer_after (Haddress _) Hcoverage Howned)
    as [installed [selected [Hinstall [Hreads [Hselected_sp [Hcpsr_saved [Hregisters Hreturn]]]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  split; [exact Hselected_sp|]. split; [exact Hcpsr_saved|]. split; [exact Hregisters|].
  intros restored Hrestore cursor restore_written middle final_cursor after Hr0 Hcursor Hprefix Hsuffix.
  destruct (Hreturn restored Hrestore cursor restore_written middle final_cursor after Hr0 Hcursor Hprefix Hsuffix)
    as [Hexecution [_ Hreturned]].
  split; [exact Hexecution|].
  match type of Hreturned with ?P after => match goal with |- ?Q after =>
    assert (Hclose : P |-- Q) end end.
  { eapply derivable1_trans with (y :=
      (task_tcb_init_stack_call_return_post environment critical sg original
         (armv7a_irq_fiq_mask saved) released **
       task_tcb_init_stack_buffer_result region args task_return lower upper result) **
      (unmap_table_rep sg ** frame)); [entailer!|].
    sep_apply_l_atomic (task_tcb_init_foreign_return_call_post environment critical sg region args
      task_return lower upper initial_name invocation origin (armv7a_irq_fiq_mask saved) initial original
      result released Hresult Hreleased Hordinary); entailer!. }
  exact (Hclose after Hreturned).
Qed.
