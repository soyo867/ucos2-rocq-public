Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_handler_stack_loan_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_unowned_irq_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_unowned_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_boot_wrapper_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapStorage KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** TCBInit's actual publication stores feed its final Restore. An IRQ at
    that Restore's unmasked cut takes the non-VFP BreakNothing path while
    OSRunning is zero. The approved BSP loan borrows the same CPU/port and
    handler-stack remainder; the two pushed alignment/LR words stay in a
    protected caller frame until POP. Counter-only handler traces preserve
    the published world and its strong parked-stack map. The resumed C
    Restore then supplies the actual OSRunning read and existing Create
    success post, with the child's published resources still in that world.

    The Sem-prefixed helpers used here describe common ARM stack accesses,
    Boot IRQ save and counter-only handler traces; no Sem argument, error
    cell, specification continuation or extra ghost state is introduced.

    This source family assumes the explicitly owned two-word scratch slice
    and its address equation at this concrete Boot stack cut. A stack lease
    alone does not imply that geometry. It covers one actual Boot IRQ with
    finite registered counter/local steps under the already-approved BSP
    loan, not arbitrary Bootstrap entry, handler implementations or all
    OSTaskCreate executions. The source transition premises describe the
    actual execution; no future return post is supplied as a premise. *)
Lemma task_create_tcb_publication_boot_irq_return_source :
  forall environment critical arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg publication state call handler prefix suffix first local_step normal_return
    (bsp_loan : armv7a_handler_stack_loan_contract environment.(task_stack_call_platform)
      environment.(task_stack_call_port) handler
      (armv7a_handler_stack_remainder handler.(os_int_exit_handler_stack) prefix suffix)
      local_step normal_return)
    saved acquired before old_frame (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let args := task_create_stack_publication_args publication in
  let published := task_create_stack_publication_state sg publication state in
  UCOS2_state_inv sg state ->
  task_create_stack_publication_input sg publication state ->
  task_create_call_stage call state ->
  task_stack_live_coverage state.(TskState) (task_stack_call_active_key call) ->
  0 <= args.(initPrio) < 64 ->
  0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296 ->
  call.(os_sched_call_origin) = BootInvocation ->
  state.(SchedState).(isRunning) = false ->
  handler.(os_int_exit_interrupted_call) = call ->
  handler.(os_int_exit_handler_stack) = call.(os_sched_call_stack).(stackLeaseRegion) ->
  handler.(os_int_exit_handler_fragments) = prefix ++ [(first, first + 2, [None; None])] ++ suffix ->
  Forall (fun fragment => Forall (fun word : option Z => word = None) (snd fragment)) (prefix ++ suffix) ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask saved ->
  (task_tcb_init_publication_tail_storage sg args state
     publication.(stack_publication_slot) publication.(stack_publication_image) **
   task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
   armv7a_task_stack_continuations abi state.(TskState) state.(TskState).(parkedTaskStacks) **
   (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved acquired **
    task_tcb_init_stack_context environment call ** unmap_table_rep sg **
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) ** frame))) before ->
  exists publication_heap,
    task_tcb_init_publication_tail_fragment sg args.(initPrio)
      (task_slot_addr sg publication.(stack_publication_slot)) before publication_heap /\
    kernel_client_step (task_create_stack_publication_client publication) sg state published /\
    task_create_call_stage call published /\
    (forall suspended cursor written irq_input saved_heap
      handler_cursor handler_heap returned_cursor returned_heap handler_entry_pc handler_bl_pc
      remask_cursor remasked_cursor remasked_heap remask_word
      irq_return resume_cursor final_cursor restored,
      handler.(os_int_exit_handler_stack).(stackRegionBase) + first * sizeof(UINT) =
        sem_pend_boot_handler_sp suspended.(armv7a_continuation_sp) ->
      cursor.(kernel_restore_r0) = saved ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor publication_heap written irq_input ->
      armv7a_save_transition abi handler suspended irq_input saved_heap ->
      suspended.(armv7a_continuation_lr) = cursor.(kernel_restore_lr) ->
      armv7a_task_frame_slice suspended ->
      kernel_heap_execution
        (sem_pend_boot_handler_push suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_lr))
        saved_heap handler_heap ->
      handler_cursor.(restore_handler_pc) = handler_entry_pc ->
      handler_cursor.(restore_handler_current_call).(restore_handler_return_word) = handler_bl_pc + 4 ->
      snd handler_cursor.(restore_handler_local) = sem_pend_boot_handler_sp suspended.(armv7a_continuation_sp) ->
      (fst handler_cursor.(restore_handler_local)).(kernel_restore_lr) = handler_bl_pc + 4 ->
      armv7a_irq_fiq_mask
        (fst handler_cursor.(restore_handler_local)).(kernel_restore_current_cpsr) = 192 ->
      normal_return sg handler_cursor handler_heap returned_cursor returned_heap ->
      local_step returned_cursor returned_heap remasked_cursor remasked_heap ->
      remask_cursor =
        {| kernel_restore_current_cpsr :=
             (fst returned_cursor.(restore_handler_local)).(kernel_restore_current_cpsr);
           kernel_restore_r0 := 211; kernel_restore_lr := suspended.(armv7a_continuation_lr);
           kernel_restore_msr_word := None; kernel_restore_return_word := None |} ->
      snd remasked_cursor.(restore_handler_local) = suspended.(armv7a_continuation_sp) ->
      remasked_cursor.(restore_handler_pc) = handler_bl_pc + 16 ->
      (fst remasked_cursor.(restore_handler_local)).(kernel_restore_current_cpsr) =
        armv7a_cpsr_restore_direct remask_cursor.(kernel_restore_current_cpsr) 211 ->
      (fst remasked_cursor.(restore_handler_local)).(kernel_restore_lr) = suspended.(armv7a_continuation_lr) ->
      kernel_call_restore_instruction_step arch RestoreWriteCPSR
        remask_cursor returned_heap remask_word remasked_heap ->
      armv7a_restore_transition abi handler suspended remasked_heap irq_return ->
      resume_cursor.(kernel_restore_current_cpsr) = suspended.(armv7a_continuation_cpsr) ->
      resume_cursor.(kernel_restore_msr_word) = written.(kernel_restore_msr_word) ->
      resume_cursor.(kernel_restore_lr) = suspended.(armv7a_continuation_lr) ->
      armv7a_restore_suffix_transition restore resume_cursor irq_return final_cursor restored ->
      sem_pend_boot_handler_pop suspended.(armv7a_continuation_sp)
        suspended.(armv7a_continuation_lr) returned_heap /\
      snd returned_cursor.(restore_handler_local) = sem_pend_boot_handler_sp suspended.(armv7a_continuation_sp) /\
      final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
      uchar_load sg.(g_OSRunning) 0 restored /\
      (task_create_stack_post environment critical sg publication.(stack_publication_region)
         publication.(stack_publication_args) publication.(stack_publication_return)
         publication.(stack_publication_lower) old_frame publication.(stack_publication_upper)
         call (armv7a_irq_fiq_mask saved) 0 **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack)
         handler.(os_int_exit_handler_fragments) ** frame) restored).
Proof.
  intros environment critical arch restore sg publication state call handler prefix suffix first
    local_step normal_return [bsp Hsp_return] saved acquired before old_frame frame abi args published
    Hvalid Hinput Hstage Hcoverage Hpriority Hpointer Hboot Hrunning Horiginal Hstack Hfragments Hunknown
    Hhandler Hpre.
  destruct (task_create_tcb_publication_world_source environment critical sg publication state call
    saved acquired before
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)
    Hvalid Hinput Hstage Hcoverage Hpriority Hpointer Hpre)
    as [publication_heap [Hstores [Hstep [Hstage_published Hmasked]]]].
  fold published in Hstep, Hstage_published, Hmasked.
  assert (Hrunning_published : published.(SchedState).(isRunning) = false) by exact Hrunning.
  assert (Hcovered : task_stack_live_coverage published.(TskState) (task_stack_call_active_key call)).
  { match type of Hmasked with ?P publication_heap =>
      assert (Hobserve : P |-- coq_prop (task_stack_live_coverage published.(TskState)
        (task_stack_call_active_key call)) && TT)
        by (unfold kernel_stack_call_masked, kernel_stack_inv; entailer!; intros ? ?; exact I) end.
    exact (proj1 (Hobserve publication_heap Hmasked)). }
  exists publication_heap; split; [exact Hstores|]. split; [exact Hstep|].
  split; [exact Hstage_published|].
  intros suspended cursor written irq_input saved_heap handler_cursor handler_heap returned_cursor returned_heap
    handler_entry_pc handler_bl_pc remask_cursor remasked_cursor remasked_heap remask_word irq_return
    resume_cursor final_cursor restored Haddress_scratch Hr0 Hcpsr Hprefix Hsave Hsavedlr Hslice Hpush
    Hentrypc Hbl Hentrysp Hentrylr Hentrycpsr Hnormal Hremask Hremaskcursor Hremaskedsp Hremaskedpc
    Hremaskedcpsr Hremaskedlr Hmsr Hirq Hresumecpsr Hresumeword Hresumelr Hsuffix.
  set (remainder := armv7a_handler_stack_remainder handler.(os_int_exit_handler_stack) prefix suffix) in *.
  set (private := armv7a_handler_stack_loan environment.(task_stack_call_platform)
    environment.(task_stack_call_port) handler remainder) in *.
  set (scratch := armv7a_handler_scratch (sem_pend_boot_handler_sp suspended.(armv7a_continuation_sp))
    (Z.land suspended.(armv7a_continuation_sp) 4) suspended.(armv7a_continuation_lr)).
  set (retained := task_tcb_init_stack_capsules environment published ** unmap_table_rep sg ** frame).
  set (protected := task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
    suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended ** retained).
  assert (Hprefix_input : (critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) call **
    (UCOS2_inv sg published ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) ** retained)) publication_heap).
  { match type of Hmasked with ?P publication_heap => match goal with |- ?Q publication_heap =>
      assert (Hopen : P |-- Q) end end.
    { unfold kernel_stack_call_masked, kernel_stack_inv, retained, task_tcb_init_stack_capsules.
      rewrite kernel_program_inv_split_unmap; entailer!. }
    exact (Hopen publication_heap Hmasked). }
  destruct (armv7a_restore_prefix_releases_critical_region _ _ _ _ restore sg call saved acquired
    cursor publication_heap written irq_input _ Hr0 Hcpsr Hprefix_input Hprefix)
    as [Hwritten [Hprefix_memory Hreleased]].
  assert (Hsave_input : (os_int_exit_frame_save_pre environment.(task_stack_call_external)
    environment.(task_stack_call_platform) handler ** (UCOS2_inv sg published ** retained)) irq_input).
  { match type of Hreleased with ?P irq_input => match goal with |- ?Q irq_input =>
      assert (Horder : P |-- Q) end end.
    { unfold os_int_exit_frame_save_pre; rewrite Horiginal, Hhandler; entailer!. }
    exact (Horder irq_input Hreleased). }
  destruct (sem_pend_unowned_boot_irq_save_source _ _ _ abi sg published handler suspended retained
    irq_input saved_heap Hrunning_published ltac:(rewrite Horiginal; exact Hboot)
    ltac:(rewrite Horiginal; exact Hstack) Hsave_input Hsave)
    as [Hsave_writes [Hrunning_read [Hcall [Hbinding Hsaved_resources]]]].
  rewrite Horiginal in Hcall.
  assert (Hread_frame : (task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
    suspended.(armv7a_continuation_fragments) ** TT) saved_heap).
  { match type of Hsaved_resources with ?P saved_heap => match goal with |- ?Q saved_heap =>
      assert (Hfocus : P |-- Q) by (entailer!; intros ? ?; exact I) end end.
    exact (Hfocus saved_heap Hsaved_resources). }
  pose proof (armv7a_task_frame_slice_restore_reads suspended (TT) saved_heap Hbinding Hslice Hread_frame) as Hreads.
  pose proof (armv7a_frame_word_reads_in_range _ _ _ (proj2 Hreads)) as Hranges.
  unfold armv7a_continuation_words in Hranges.
  pose proof (Forall_inv_tail Hranges) as Hwords.
  apply Forall_app in Hwords; destruct Hwords as [_ Hlast].
  pose proof (Forall_inv Hlast) as Hlr.
  assert (Hpush_input :
    ((sem_pend_boot_handler_sp suspended.(armv7a_continuation_sp)) # UInt |->_ **
      ((sem_pend_boot_handler_sp suspended.(armv7a_continuation_sp) + 4) # UInt |->_ **
      (private handler_cursor.(restore_handler_current_call) handler_cursor.(restore_handler_local) **
       (UCOS2_inv sg published ** protected)))) saved_heap).
  { match type of Hsaved_resources with ?P saved_heap => match goal with |- ?Q saved_heap =>
      assert (Hsplit : P |-- Q) end end.
    { unfold os_int_exit_context_resources.
      rewrite Hfragments, (proj1 (armv7a_handler_stack_split_scratch _ prefix suffix first)), Haddress_scratch.
      unfold private, armv7a_handler_stack_loan, protected; rewrite Hentrycpsr.
      fold remainder; entailer!. }
    exact (Hsplit saved_heap Hsaved_resources). }
  destruct (armv7a_handler_scratch_push_source
    (sem_pend_boot_handler_sp suspended.(armv7a_continuation_sp))
    (Z.land suspended.(armv7a_continuation_sp) 4) suspended.(armv7a_continuation_lr) _ saved_heap
    (sem_pend_boot_alignment_in_range suspended.(armv7a_continuation_sp)) Hlr Hpush_input)
    as [produced [Hpush_writes Hproduced]].
  assert (produced = handler_heap) by
    (eapply kernel_heap_execution_deterministic; [exact Hpush_writes|exact Hpush]).
  subst produced.
  assert (Hentry : (private handler_cursor.(restore_handler_current_call) handler_cursor.(restore_handler_local) **
    (UCOS2_inv sg published ** (scratch ** protected))) handler_heap).
  { match type of Hproduced with ?P handler_heap => match goal with |- ?Q handler_heap =>
      assert (Horder : P |-- Q) by (unfold scratch; entailer!) end end.
    exact (Horder handler_heap Hproduced). }
  destruct (restore_handler_return_refinement _ _ _ bsp sg handler_cursor handler_heap
    returned_cursor returned_heap Hnormal) as [Hmatched [Hreturnpc Hhandler_run]].
  destruct (mutex_del_restore_handler_execution_trace _ _ _ _ _ _ _ Hhandler_run) as [clients Htrace].
  pose proof (sem_pend_boot_handler_trace_preserves_frame _ _ _ _ bsp sg clients _ _ _ _ Htrace
    published (scratch ** protected) Hrunning_published Hentry) as Hreturned.
  assert (Hpop : sem_pend_boot_handler_pop suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_lr) returned_heap).
  { unfold sem_pend_boot_handler_pop; eapply armv7a_handler_scratch_pop_reads.
    match type of Hreturned with ?P returned_heap =>
      assert (Horder : P |-- scratch ** (private returned_cursor.(restore_handler_current_call)
        returned_cursor.(restore_handler_local) ** (UCOS2_inv sg published ** protected))) by entailer! end.
    exact (Horder returned_heap Hreturned). }
  assert (Hreturnedsp : snd returned_cursor.(restore_handler_local) =
    sem_pend_boot_handler_sp suspended.(armv7a_continuation_sp)).
  { rewrite (Hsp_return _ _ _ _ _ Hnormal); exact Hentrysp. }
  pose proof (restore_handler_local_resources _ _ _ bsp _ _ _ _ _ Hremask Hreturned) as Hremasked.
  assert (Hreturn_input : (interrupt_platform_running environment.(task_stack_call_platform)
    handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources environment.(task_stack_call_port) handler **
    task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
      suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended **
    (UCOS2_inv sg published ** retained)) remasked_heap).
  { match type of Hremasked with ?P remasked_heap => match goal with |- ?Q remasked_heap =>
      assert (Hmerge : P |-- Q) end end.
    { unfold private, armv7a_handler_stack_loan, scratch, protected.
      rewrite Hremaskedcpsr, armv7a_cpsr_restore_mask_eq.
      change (armv7a_irq_fiq_mask 211) with 192.
      unfold os_int_exit_context_resources; rewrite Hfragments.
      pose proof (armv7a_handler_stack_merge_scratch handler.(os_int_exit_handler_stack) prefix suffix first
        (Z.land suspended.(armv7a_continuation_sp) 4) suspended.(armv7a_continuation_lr)) as Hstack_merge.
      rewrite Haddress_scratch in Hstack_merge; fold remainder in Hstack_merge.
      sep_apply_l_atomic Hstack_merge; entailer!. }
    exact (Hmerge remasked_heap Hremasked). }
  assert (Hrestore_reads : armv7a_continuation_restore_reads suspended remasked_heap).
  { match type of Hreturn_input with ?P remasked_heap => assert (Hfocus : P |--
      task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
        suspended.(armv7a_continuation_fragments) ** TT) by (entailer!; intros ? ?; exact I) end.
    exact (armv7a_task_frame_slice_restore_reads suspended (TT) remasked_heap Hbinding Hslice
      (Hfocus remasked_heap Hreturn_input)). }
  destruct (armv7a_restore_call_resources _ _ _ abi handler suspended call
    (UCOS2_inv sg published ** retained) remasked_heap irq_return Hcall Hrestore_reads Hreturn_input Hirq)
    as [Hrestore_memory Hresumed].
  destruct (armv7a_save_transition_observations _ _ _ abi handler suspended irq_input saved_heap Hsave)
    as [_ [_ [_ [Hsavedmask _]]]].
  rewrite Hsavedmask, Hhandler in Hresumed.
  set (word := armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)).
  assert (Hword : resume_cursor.(kernel_restore_msr_word) = Some word)
    by (rewrite Hresumeword, Hwritten; reflexivity).
  assert (Hwordmask : armv7a_irq_fiq_mask word = armv7a_irq_fiq_mask saved)
    by (unfold word; rewrite armv7a_cpsr_restore_mask_eq, Hr0; reflexivity).
  assert (Hsuffix_input : (kernel_call_execution_owned environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (armv7a_continuation_resumed_call suspended call)
    (armv7a_irq_fiq_mask word) ** (UCOS2_inv sg published ** retained **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments))) irq_return).
  { match type of Hresumed with ?P irq_return => match goal with |- ?Q irq_return =>
      assert (Horder : P |-- Q) by (rewrite Hwordmask; entailer!) end end.
    exact (Horder irq_return Hresumed). }
  destruct (armv7a_restore_suffix_transports_owned_execution _ _ _ _ restore
    (armv7a_continuation_resumed_call suspended call) word resume_cursor irq_return final_cursor restored _
    Hword Hsuffix_input Hsuffix) as [Hfinal [Hsuffix_memory Hafter]].
  rewrite Hwordmask in Hafter.
  pose proof (proj2 Hbinding) as Hsaved_stack; rewrite Hcall in Hsaved_stack.
  assert (Hsame : task_tcb_init_stack_same_call (armv7a_continuation_resumed_call suspended call) call).
  { unfold task_tcb_init_stack_same_call, armv7a_continuation_resumed_call; cbn; auto. }
  assert (Hcovered_returned : task_stack_live_coverage published.(TskState)
    (task_stack_call_active_key (armv7a_continuation_resumed_call suspended call))) by exact Hcovered.
  split; [exact Hpop|]. split; [exact Hreturnedsp|]. split.
  - rewrite Hfinal; cbn [kernel_restore_branch_lr kernel_restore_return_word].
    rewrite Hresumelr, Hsavedlr; reflexivity.
  - split.
    + match type of Hafter with ?P restored => assert (Hobserve : P |--
        sg.(g_OSRunning) # UChar |-> 0 ** TT) end.
      { rewrite UCOS2_inv_split_running, Hrunning_published; entailer!; intros ? ?; exact I. }
      eapply framed_uchar_store_load; exact (Hobserve restored Hafter).
    + match type of Hafter with ?P restored => match goal with |- ?Q restored =>
        assert (Hfinish : P |-- Q) end end.
      { unfold task_create_stack_post; Exists (armv7a_continuation_resumed_call suspended call) published.
        destruct (Z.eq_dec 0 0); [|contradiction].
        unfold retained, task_tcb_init_stack_save_input, critical_region_outside.
        rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
        unfold UCOS2_inv; entailer!. }
      exact (Hfinish restored Hafter).
Qed.
