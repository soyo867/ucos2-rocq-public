Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_world_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Actual final TCB publication stores -> final TCB Restore -> next
    OS_Sched Save -> real no-switch C prefix -> final Restore. Every
    physical endpoint is passed to the next source segment. In this local
    no-IRQ branch the actual new-task publication supplies the nonempty
    ready list; it is not an extra public precondition or a fact extracted from CPU
    authority. Only this explicit branch is claimed; neither intervening
    IRQs nor eventual ordinary task return are elided. *)
Lemma task_create_tcb_publication_nonswitch_source :
  forall environment critical arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg publication state call saved acquired before old_frame (frame : Assertion),
  let args := task_create_stack_publication_args publication in
  let published := task_create_stack_publication_state sg publication state in
  UCOS2_state_inv sg state ->
  task_create_stack_publication_input sg publication state ->
  task_create_call_stage call state ->
  task_stack_live_coverage state.(TskState) (task_stack_call_active_key call) ->
  0 <= args.(initPrio) < 64 ->
  0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296 ->
  (task_tcb_init_publication_tail_storage sg args state
     publication.(stack_publication_slot) publication.(stack_publication_image) **
   task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
   armv7a_task_stack_continuations environment.(task_stack_call_continuations)
     state.(TskState) state.(TskState).(parkedTaskStacks) **
   (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved acquired **
    task_tcb_init_stack_context environment call ** unmap_table_rep sg ** frame)) before ->
  exists publication_heap,
    task_tcb_init_publication_tail_fragment sg args.(initPrio)
      (task_slot_addr sg publication.(stack_publication_slot)) before publication_heap /\
    kernel_client_step (task_create_stack_publication_client publication) sg state published /\
    task_create_call_stage call published /\
    (forall tcb_cursor tcb_written tcb_middle tcb_final returned_heap,
      tcb_cursor.(kernel_restore_r0) = saved ->
      armv7a_irq_fiq_mask tcb_cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore tcb_cursor publication_heap tcb_written tcb_middle ->
      armv7a_restore_suffix_transition restore tcb_written tcb_middle tcb_final returned_heap ->
      kernel_call_restore_uninterrupted_execution arch tcb_cursor publication_heap tcb_final returned_heap /\
      (task_tcb_init_stack_save_input environment critical sg call
         (armv7a_irq_fiq_mask saved) published ** unmap_table_rep sg ** frame) returned_heap /\
      (forall registers final_registers sched_acquired saved_heap,
        published.(SchedState).(isRunning) = true ->
        registers.(kernel_save_return_word) = None ->
        valid_os_cpu_sr registers.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
        os_sched_requests_switch published = false ->
        armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) published returned_heap
          final_registers sched_acquired saved_heap ->
        kernel_call_save_uninterrupted_execution arch registers published returned_heap
          final_registers sched_acquired saved_heap /\
        sched_acquired = published /\
        exists prefix_heap,
          os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
          (forall cursor written middle final_cursor after,
            cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
            armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
            armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
            armv7a_restore_suffix_transition restore written middle final_cursor after ->
            kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
            (task_create_stack_post environment critical sg publication.(stack_publication_region)
              publication.(stack_publication_args) publication.(stack_publication_return)
              publication.(stack_publication_lower) old_frame publication.(stack_publication_upper)
              call (armv7a_irq_fiq_mask saved) 0 ** frame) after))).
Proof.
  intros environment critical arch save restore sg publication state call saved acquired before old_frame frame
    args published Hvalid Hinput Hstage Hcoverage Hpriority Hpointer Hpre.
  destruct (task_create_tcb_publication_world_source environment critical sg publication state
    call saved acquired before frame Hvalid Hinput Hstage Hcoverage Hpriority Hpointer Hpre)
    as [publication_heap [Hstores [Hstep [Hstage_published Hmasked]]]].
  fold published in Hstep, Hstage_published, Hmasked.
  exists publication_heap; split; [exact Hstores|]. split; [exact Hstep|].
  split; [exact Hstage_published|].
  intros tcb_cursor tcb_written tcb_middle tcb_final returned_heap Hr0 Hmask Hprefix Hsuffix.
  match type of Hmasked with ?P publication_heap => assert (Hopen : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) call **
    (kernel_stack_inv environment.(task_stack_call_continuations) kernel_program_inv sg
      (task_stack_call_active_key call) published ** frame))
    by (unfold kernel_stack_call_masked; entailer!) end.
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg call saved acquired
    tcb_cursor publication_heap tcb_written tcb_middle tcb_final returned_heap _ Hr0 Hmask
    (Hopen publication_heap Hmasked) Hprefix Hsuffix) as [Hrun [Hlr [Hmemory Howned]]].
  assert (Hclosed : (kernel_stack_call_closed environment.(task_stack_call_continuations) kernel_program_inv
    sg (task_stack_call_active_key call) call (armv7a_irq_fiq_mask saved) published ** frame) returned_heap).
  { match type of Howned with ?P returned_heap => match goal with |- ?Q returned_heap =>
      assert (Hclose : P |-- Q) end end.
    { unfold kernel_stack_call_closed; entailer!. }
    exact (Hclose returned_heap Howned). }
  assert (Hpublic : (task_tcb_init_stack_save_input environment critical sg call
    (armv7a_irq_fiq_mask saved) published ** unmap_table_rep sg ** frame) returned_heap).
  { match type of Hclosed with ?P returned_heap => match goal with |- ?Q returned_heap =>
      assert (Hpublic_rule : P |-- Q) end end.
    { rewrite task_tcb_init_stack_save_input_closed_world; reflexivity. }
    exact (Hpublic_rule returned_heap Hclosed). }
  split; [exact Hrun|]. split; [exact Hpublic|].
  intros registers final_registers sched_acquired saved_heap Hrunning Hreturn Hcpsr Hsaved_mask
    Hnoswitch Hsave.
  assert (Hnonempty : os_sched_selection_enabled published = true ->
    published.(SchedState).(readyList) <> []).
  { intros _ Hempty.
    assert (Hin : In publication.(stack_publication_slot) published.(SchedState).(readyList)).
    { change (In publication.(stack_publication_slot)
        (Ucos2Verify.lib.helpers.insert_sorted_by
          (sched_task_key sg (task_commit state.(TskState) args.(initPrio)
            publication.(stack_publication_invocation)
            (task_tcb_init_commit_node args publication.(stack_publication_acquired)
              publication.(stack_publication_slot) publication.(stack_publication_image))))
          publication.(stack_publication_slot) state.(SchedState).(readyList))).
      apply Ucos2Verify.lib.helpers.insert_sorted_by_in; left; reflexivity. }
    rewrite Hempty in Hin; contradiction. }
  destruct (os_sched_stack_uninterrupted_nonswitch_call environment critical arch save restore sg
    call (armv7a_irq_fiq_mask saved) published registers returned_heap
    final_registers sched_acquired saved_heap frame Hreturn Hcpsr Hsaved_mask
    Hnoswitch Hnonempty Hclosed Hsave) as [Hsave_run [Hstate Htail]].
  split; [exact Hsave_run|]. split; [exact Hstate|].
  destruct Htail as [prefix_heap [Hprefix_run Hreturn_source]].
  exists prefix_heap; split; [exact Hprefix_run|].
  intros cursor written middle final_cursor after Hrestore_r0 Hrestore_mask Hrestore_prefix Hrestore_suffix.
  destruct (Hreturn_source cursor written middle final_cursor after Hrestore_r0 Hrestore_mask
    Hrestore_prefix Hrestore_suffix) as [Hrestore_run Hpost].
  split; [exact Hrestore_run|].
  match type of Hpost with ?P after => match goal with |- ?Q after =>
    assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (os_sched_stack_return_post_returns_create environment critical sg call call
      (armv7a_irq_fiq_mask saved) published publication.(stack_publication_region)
      publication.(stack_publication_args) publication.(stack_publication_return)
      publication.(stack_publication_lower) old_frame publication.(stack_publication_upper)
      ltac:(unfold task_tcb_init_stack_same_call; auto)); entailer!. }
  exact (Hclose after Hpost).
Qed.
