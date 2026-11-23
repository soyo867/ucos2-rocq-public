Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_switch_capture_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_pending_suffix_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_return_tail_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The rollback Save was interrupted after MRS. A foreign task's actual
    switch stores/capture/restore resume that saved continuation, then
    CPSID/DSB/BX returns its original R0 and the real NULL store consumes
    the newly acquired priority cell. The original no-free observation
    and initialized child buffer survive on this same heap chain. *)
Lemma task_create_foreign_save_rollback_source :
  forall environment critical arch
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg region args task_return lower upper initial_name original suspended initial released checkpoint
    state node call old_sp cpsr registers lr prefix suffix first old_words publication (frame : Assertion) before,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let retained := task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) ** frame in
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) initial ->
  task_tcb_init_call_result sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) initial 66 released ->
  UCOS2_state_inv sg checkpoint ->
  task_tcb_init_stack_return_preserved original released checkpoint ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) checkpoint state ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended ->
  interrupt_saved_value (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr))
    (nth 0 suspended.(armv7a_continuation_registers) 0) ->
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
        (forall restored cursor final_registers acquired after,
          armv7a_task_restore_transition task_abi call selected installed restored ->
          cursor.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
          cursor.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
          cursor.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
          armv7a_save_suffix_transition save cursor
            (os_sched_install_context call fragments original.(os_sched_call_stack) updated)
            restored final_registers acquired after ->
          kernel_save_after_mrs_execution arch cursor
            (os_sched_install_context call fragments original.(os_sched_call_stack) updated)
            restored final_registers acquired after /\
          final_registers.(kernel_save_r0) = nth 0 suspended.(armv7a_continuation_registers) 0 /\
          exists returned rollback_entry rollback_heap,
            task_tcb_init_stack_same_call returned original /\
            kernel_heap_execution (pointer_store_writes
              (sg.(g_OSTCBPrioTbl) + args.(createPriority) * sizeof(PTR)) 0) after rollback_heap /\
            (task_tcb_init_stack_restore_input environment critical sg returned final_registers.(kernel_save_r0)
               rollback_entry (task_create_stack_rolled_back args rollback_entry) **
             task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
             unmap_table_rep sg ** frame) rollback_heap)).
Proof.
  intros environment critical arch task_abi save restore sg region args task_return lower upper initial_name
    original suspended initial released checkpoint state node call old_sp cpsr registers lr prefix suffix first old_words
    publication frame before abi focus retained Hentry Hresult Hcheckpoint Hprevious Hhistory Horigin Hbinding Hcall
    Hslice Hsaved_value Hdifferent Hpointer Hinput Hpre fragments foreign_saved updated.
  pose proof Hinput as Hgeometry.
  destruct Hgeometry as [Hcurrent [Hnode [Hid [Hgen [Hnone [Hhigh [Hnonempty [Hfocus [Hfragments
    [Hregion [Hbounds [Hsp_range [Hpublication [Hlength [Hcpsr [Hlr [Hranges [Hmask_foreign [Hsp32
      [Hsp Haddress]]]]]]]]]]]]]]]]]]]].
  destruct (task_tcb_init_switch_capture_source environment task_abi sg original suspended checkpoint state node
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
  destruct (task_tcb_init_pending_call_suffix_source environment critical arch task_abi save restore sg
    original checkpoint call fragments updated suspended captured retained Hhistory_after Horigin Hbinding Hcall
    Hslice Hpointer_after (Haddress _) Hdestination Hcaptured_owned)
    as [installed [selected [Hinstall [Hreads [Hselected_sp [Hsaved_cpsr [Hsaved_registers Hreturn]]]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  intros restored cursor final_registers acquired after Hrestored Hcursor_cpsr Hcursor_r0 Hcursor_lr Hsuffix.
  destruct (Hreturn restored Hrestored) as [Hsame [Hselected_stage [Hstage [Hpreserved [Hordinary [Hcurrent_world [Hnext_save Hnext_restore]]]]]]].
  destruct (Hnext_save cursor final_registers acquired after Hcursor_cpsr Hcursor_r0 Hcursor_lr Hsaved_value Hsuffix)
    as [Hexecution [Hacquired [Hr0 [Hreturn_word Hafter]]]].
  split; [exact Hexecution|]. split; [exact Hr0|].
  assert (Hordered : (task_tcb_init_stack_save_output environment critical sg original
    (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) final_registers.(kernel_save_r0) checkpoint **
    task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
    unmap_table_rep sg ** frame) after).
  { match type of Hafter with ?P after => match goal with |- ?Q after => assert (Horder : P |-- Q)
      by (unfold retained; entailer!) end end. exact (Horder after Hafter). }
  destruct (task_create_no_free_rollback_store_source environment critical sg region args task_return lower upper
    initial_name original original (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr))
    final_registers.(kernel_save_r0) initial released checkpoint after frame Hentry
    ltac:(unfold task_tcb_init_stack_same_call; auto) Hresult Hcheckpoint Hprevious Hordered)
    as [returned [rollback_entry [rollback_heap [Hreturned [Hsaved [Hstore_null Hrollback]]]]]].
  exists returned, rollback_entry, rollback_heap; split; [exact Hreturned|].
  split; [exact Hstore_null|exact Hrollback].
Qed.
