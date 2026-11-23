Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_preparation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_init_repeated_irq_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual successful admission prefix of OSTaskCreate supplies the
    repeated-IRQ StackInit producer. The first Save and the Restore after
    the reservation are the explicit uninterrupted source branches; IRQs
    during StackInit use the existing finite registered source family.

    The priority and nesting premises identify the guards taken at THIS
    first acquisition. Their values are read from the owned cells below.
    They are not added to the public Require. The initialized private
    buffer and the current creation invocation reach the next canonical
    OS_TCBInit call through the continuation's proved base case. *)
Lemma task_create_reserve_stack_init_repeated_irq_source :
  forall schedule environment critical arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg region args task_return lower old_frame upper initial_name call mask state
    handler_region handler_fragments registers before final_registers acquired saved_heap
    (frame : Assertion),
  task_priority_in_range sg args.(createPriority) ->
  state.(IntrState).(intNesting) = 0 ->
  state.(TskState).(prioTbl) args.(createPriority) = PTFree ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (task_create_stack_pre environment critical sg region args task_return lower old_frame upper
     initial_name call mask state **
   task_stack_fragments_rep handler_region handler_fragments ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired saved_heap /\
  acquired = state /\
  exists reserved_heap,
    task_create_stack_reserve_fragment sg args.(createPriority) saved_heap reserved_heap /\
    (forall cursor written middle final_cursor restored_heap,
      cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor reserved_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor restored_heap ->
      kernel_call_restore_uninterrupted_execution arch cursor reserved_heap final_cursor restored_heap /\
      final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
      exists prepared,
        kernel_heap_execution [] restored_heap prepared /\
        task_create_stack_init_irq_continuation schedule environment critical sg args region handler_region
          handler_fragments task_return lower upper initial_name call mask
          (task_create_stack_reserved args call state) call (task_create_stack_reserved args call state) []
          (task_stack_init_core_push_words args.(createEntry) args.(createArgument) task_return) prepared frame).
Proof.
  intros schedule environment critical arch save restore sg region args task_return lower old_frame upper
    initial_name call mask state handler_region handler_fragments registers before final_registers
    acquired saved_heap frame Hpriority Hnesting Hfree Hreturn Hcpsr Hmask Hpre Hsave.
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (task_create_stack_entry sg args initial_name call state /\
      task_create_stack_buffer_domain region args task_return lower old_frame upper /\
      task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
    (kernel_call_execution_owned environment.(task_stack_call_external)
       environment.(task_stack_call_platform) call mask **
     (UCOS2_inv sg state ** task_tcb_init_stack_capsules environment state **
      task_stack_storage region (lower ++ old_frame ++ upper) ** unmap_table_rep sg **
      task_stack_fragments_rep handler_region handler_fragments ** frame))) end.
  { unfold task_create_stack_pre, task_tcb_init_stack_save_input, critical_region_outside.
    rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
    unfold UCOS2_inv; entailer!; tauto. }
  destruct (Hopen before Hpre) as [[Hentry [Hdomain Hcoverage]] Howned].
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)).
  { split; [exact Hcpsr|reflexivity]. }
  assert (Hrun : kernel_call_save_uninterrupted_execution arch registers state before
    final_registers acquired saved_heap).
  { unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave). }
  assert (Hsave_input : (kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) call
      (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) **
    (UCOS2_inv sg state ** task_tcb_init_stack_capsules environment state **
     task_stack_storage region (lower ++ old_frame ++ upper) ** unmap_table_rep sg **
     task_stack_fragments_rep handler_region handler_fragments ** frame)) before).
  { cbn [kernel_save_read_cpsr kernel_save_cpsr]; rewrite Hmask; exact Howned. }
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg call
    (kernel_save_read_cpsr registers) state before final_registers acquired saved_heap _
    Hsaved Hsave_input Hsave) as [Hstate [Hmemory [Hsave_return [Hr0 Hmasked]]]].
  split; [exact Hrun|]. split; [exact Hstate|].
  set (reserved := task_create_stack_reserved args call state).
  pose proof (task_create_stack_reserved_entry sg args initial_name call state Hentry Hpriority Hfree)
    as Hreserved_entry.
  fold reserved in Hreserved_entry.
  assert (Hreserved_valid : UCOS2_state_inv sg reserved) by exact (proj1 Hreserved_entry).
  assert (Hreserved_coverage : task_stack_live_coverage reserved.(TskState) (task_stack_call_active_key call))
    by exact Hcoverage.
  match type of Hmasked with ?P saved_heap => assert (Hreserve_input : P |--
    UCOS2_inv sg state **
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       call.(os_sched_call_invocation) call.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
     os_sched_context_resources environment.(task_stack_call_external) call **
     task_tcb_init_stack_capsules environment state **
     task_stack_storage region (lower ++ old_frame ++ upper) ** unmap_table_rep sg **
     task_stack_fragments_rep handler_region handler_fragments ** frame)) by entailer! end.
  destruct (task_create_stack_reserve_execution sg args initial_name call state _ saved_heap
    Hentry Hpriority Hnesting Hfree (Hreserve_input saved_heap Hmasked))
    as [reserved_heap [Hstores Hreserved]].
  exists reserved_heap; split; [exact Hstores|].
  intros cursor written middle final_cursor restored_heap Hrestore_r0 Hrestore_mask Hprefix Hsuffix.
  match type of Hreserved with ?P reserved_heap => assert (Hrestore_input : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
    os_sched_context_resources environment.(task_stack_call_external) call **
    (UCOS2_inv sg reserved ** task_tcb_init_stack_capsules environment reserved **
     task_stack_storage region (lower ++ old_frame ++ upper) ** unmap_table_rep sg **
     task_stack_fragments_rep handler_region handler_fragments ** frame)) end.
  { change (task_tcb_init_stack_capsules environment reserved) with
      (task_tcb_init_stack_capsules environment state).
    fold reserved; entailer!. }
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg call
    final_registers.(kernel_save_r0) state cursor reserved_heap written middle final_cursor restored_heap _
    Hrestore_r0 Hrestore_mask (Hrestore_input reserved_heap Hreserved) Hprefix Hsuffix)
    as [Hrestore [Hrestore_return [Hrestore_memory Hrestored]]].
  split; [exact Hrestore|]. split; [exact Hrestore_return|].
  assert (Hsaved_mask : armv7a_irq_fiq_mask final_registers.(kernel_save_r0) = mask).
  { rewrite Hr0; exact Hmask. }
  destruct Hdomain as [Hlayout [Hlength [Hentry_range [Hargument_range Hreturn_range]]]].
  match type of Hrestored with ?P restored_heap => assert (Hinit_input : P |--
    task_create_stack_init_input environment critical sg region args task_return lower old_frame upper
      call mask reserved ** unmap_table_rep sg **
    task_stack_fragments_rep handler_region handler_fragments ** frame) end.
  { sep_apply_l_atomic (task_create_stack_storage_init_pre TaskStackNoVFP region args task_return
      lower old_frame upper Hlayout Hlength Hentry_range Hargument_range Hreturn_range).
    unfold task_create_stack_init_input, task_tcb_init_stack_save_input, critical_region_outside.
    rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running, Hsaved_mask.
    unfold UCOS2_inv; entailer!. }
  exact (task_create_stack_init_repeated_irq_tcb_pre schedule environment critical sg args reserved
    call mask region handler_region handler_fragments task_return lower old_frame upper initial_name
    restored_heap frame Hlayout Hreserved_entry (Hinit_input restored_heap Hrestored)).
Qed.
