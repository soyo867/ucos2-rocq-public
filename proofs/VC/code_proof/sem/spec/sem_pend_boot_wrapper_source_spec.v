Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_unowned_irq_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_checkpoint_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_handler_stack_loan_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_call_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapStorage KernelHeapObservation ListNotations.
Import Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

Lemma sem_pend_boot_alignment_in_range : forall sp,
  0 <= Z.land sp 4 < 4294967296.
Proof.
  intros sp.
  pose proof (Z.land_ones (Z.land sp 4) 3 ltac:(lia)) as Hmask.
  change (Z.land (Z.land sp 4) 7 = Z.land sp 4 mod 8) in Hmask.
  rewrite <- Z.land_assoc in Hmask.
  change (Z.land sp 4 = Z.land sp 4 mod 8) in Hmask.
  pose proof (Z.mod_pos_bound (Z.land sp 4) 8 ltac:(lia)); lia.
Qed.

(** Pinned non-VFP BreakNothing (os_cpu_a_vfp-none.S:586--606).
    This source family owns an actual two-word writable slice of the
    handler's ORIGINAL fragments; the loaned prefix/suffix words are None.
    They are not inferred from a lease or a mere SP bound. The saved
    sixteen-word continuation stays in a separate caller frame.

    The user-approved BSP contract now borrows ONLY the remainder and the
    actual CPU/opaque-port resources, returns the same SP at normal C
    return, and frames the saved alignment/LR pair. It does not prove the
    deployed BSP. The real remask Local step AND MSR projection remain
    explicit source/CPU premises. This theorem constructs entry ownership,
    derives POP reads, and reconstructs the old handler owner after remask;
    none of those three facts is assumed as an unexplained resource cut.

    Other scratch layouts, Task-origin None and other IRQ/registry families
    are not classified here, and no condition is added to SemPend Require. *)
Lemma sem_pend_boot_wrapper_public_source : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  sg context original handler suspended prefix suffix first
  local_step normal_return
  (bsp_loan : armv7a_handler_stack_loan_contract platform port handler
    (armv7a_handler_stack_remainder handler.(os_int_exit_handler_stack) prefix suffix)
    local_step normal_return)
  mask saved acquired checkpoint initial pevent eid timeout perr X cursor before written irq_input saved_heap
  handler_cursor handler_heap returned_cursor returned_heap handler_entry_pc handler_bl_pc
  remask_cursor remasked_cursor remasked_heap remask_word
  irq_return resume_cursor final_cursor restored (frame : Assertion),
  handler.(os_int_exit_interrupted_call) = original ->
  original.(os_sched_call_origin) = BootInvocation ->
  checkpoint.(SchedState).(isRunning) = false ->
  handler.(os_int_exit_handler_stack) = original.(os_sched_call_stack).(stackLeaseRegion) ->
  handler.(os_int_exit_handler_fragments) = prefix ++ [(first, first + 2, [None; None])] ++ suffix ->
  Forall (fun fragment => Forall (fun word : option Z => word = None) (snd fragment)) (prefix ++ suffix) ->
  handler.(os_int_exit_handler_stack).(stackRegionBase) + first * sizeof(UINT) =
    sem_pend_boot_handler_sp suspended.(armv7a_continuation_sp) ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask saved ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  kernel_stack_call_same_call original context ->
  sem_pend_checkpoint_result None critical sg context pevent timeout initial 0 checkpoint ->
  pevent <> 0 -> pevent = event_addr sg eid ->
  sem_pend_context_error (event_slot_type_value initial.(EventState) eid)
    initial.(IntrState).(intNesting) initial.(IntrState).(lockNesting) = None ->
  safeExec (LastSeen initial)
    (bind (atomic_cmd (sem_pend_runtime_program external platform None critical sg context pevent timeout))
      sem_query_observe_error) X ->
  (sem_pend_stack_restore_input external platform None critical sg original mask saved acquired checkpoint **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
    (unmap_table_rep sg ** perr # UChar |->_ ** frame)) before ->
  armv7a_restore_prefix_transition restore cursor before written irq_input ->
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
  kernel_call_restore_instruction_step arch RestoreWriteCPSR remask_cursor returned_heap remask_word remasked_heap ->
  armv7a_restore_transition abi handler suspended remasked_heap irq_return ->
  resume_cursor.(kernel_restore_current_cpsr) = suspended.(armv7a_continuation_cpsr) ->
  resume_cursor.(kernel_restore_msr_word) = written.(kernel_restore_msr_word) ->
  resume_cursor.(kernel_restore_lr) = suspended.(armv7a_continuation_lr) ->
  armv7a_restore_suffix_transition restore resume_cursor irq_return final_cursor restored ->
  exists after, kernel_heap_execution [(perr, 0)] restored after /\
    (sem_pend_stack_call_post external platform None critical sg context mask
       pevent timeout perr initial X **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) after.
Proof.
  intros external platform port critical arch abi restore sg context original handler suspended prefix suffix first
    local_step normal_return [bsp Hsp_return] mask saved acquired checkpoint initial pevent eid timeout perr X
    cursor before written irq_input saved_heap handler_cursor handler_heap returned_cursor returned_heap
    handler_entry_pc handler_bl_pc remask_cursor remasked_cursor remasked_heap remask_word irq_return resume_cursor
    final_cursor restored frame Horiginal Hboot Hrunning Hstack Hfragments Hunknown Haddress_scratch
    Hhandler Hr0 Hmasked Hcontext Hresult Hnonzero Haddress Hclear Hexec Hpre Hprefix Hsave Hsavedlr Hslice
    Hpush Hentrypc Hbl Hentrysp Hentrylr Hentrycpsr Hnormal Hremask Hremaskcursor Hremaskedsp Hremaskedpc
    Hremaskedcpsr Hremaskedlr Hmsr Hirq Hresumecpsr Hresumeword Hresumelr Hsuffix.
  set (remainder := armv7a_handler_stack_remainder handler.(os_int_exit_handler_stack) prefix suffix) in *.
  set (private := armv7a_handler_stack_loan platform port handler remainder) in *.
  set (scratch := armv7a_handler_scratch (sem_pend_boot_handler_sp suspended.(armv7a_continuation_sp))
    (Z.land suspended.(armv7a_continuation_sp) 4) suspended.(armv7a_continuation_lr)).
  set (protected := task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
    suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended **
    unmap_table_rep sg ** perr # UChar |->_ ** frame).
  assert (Hsaved : interrupt_saved_value mask saved).
  { match type of Hpre with ?P before => assert (Hget : P |-- coq_prop (interrupt_saved_value mask saved) && TT)
      by (unfold sem_pend_stack_restore_input; entailer!) end.
    exact (proj1 (Hget before Hpre)). }
  assert (Hpre' : (sem_pend_stack_restore_input external platform None critical sg
    handler.(os_int_exit_interrupted_call) mask saved acquired checkpoint **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
    (unmap_table_rep sg ** perr # UChar |->_ ** frame)) before) by (rewrite Horiginal; exact Hpre).
  destruct (sem_pend_unowned_restore_boot_irq_entry external platform port critical arch abi restore sg
    handler suspended mask saved acquired checkpoint cursor before written irq_input saved_heap
    (unmap_table_rep sg ** perr # UChar |->_ ** frame) Hrunning ltac:(rewrite Horiginal; exact Hboot)
    ltac:(rewrite Horiginal; exact Hstack) Hhandler Hr0 Hmasked Hpre' Hprefix Hsave)
    as [Hwritten [Hwrites [Hzero [Hcall [Hbinding Hsaved_resources]]]]].
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
       (UCOS2_inv sg checkpoint ** protected)))) saved_heap).
  { match type of Hsaved_resources with ?P saved_heap => match goal with |- ?Q saved_heap => assert (Hsplit : P |-- Q) end end.
    { unfold os_int_exit_context_resources.
      rewrite Hfragments, (proj1 (armv7a_handler_stack_split_scratch _ prefix suffix first)), Haddress_scratch.
      unfold private, armv7a_handler_stack_loan, protected; rewrite Hentrycpsr.
      fold remainder; entailer!. }
    exact (Hsplit saved_heap Hsaved_resources). }
  destruct (armv7a_handler_scratch_push_source
    (sem_pend_boot_handler_sp suspended.(armv7a_continuation_sp))
    (Z.land suspended.(armv7a_continuation_sp) 4) suspended.(armv7a_continuation_lr) _ saved_heap
    (sem_pend_boot_alignment_in_range suspended.(armv7a_continuation_sp)) Hlr Hpush_input)
    as [produced [Hstores Hproduced]].
  assert (produced = handler_heap) by
    (eapply kernel_heap_execution_deterministic; [exact Hstores|exact Hpush]).
  subst produced.
  assert (Hentry : (private handler_cursor.(restore_handler_current_call) handler_cursor.(restore_handler_local) **
    (UCOS2_inv sg checkpoint ** (scratch ** protected))) handler_heap).
  { match type of Hproduced with ?P handler_heap => match goal with |- ?Q handler_heap =>
      assert (Horder : P |-- Q) by (unfold scratch; entailer!) end end.
    exact (Horder handler_heap Hproduced). }
  destruct (restore_handler_return_refinement _ _ _ bsp sg handler_cursor handler_heap
    returned_cursor returned_heap Hnormal) as [Hmatched [Hreturnpc Hhandler_run]].
  destruct (mutex_del_restore_handler_execution_trace _ _ _ _ _ _ _ Hhandler_run) as [clients Htrace].
  pose proof (sem_pend_boot_handler_trace_preserves_frame _ _ _ _ bsp sg clients _ _ _ _ Htrace
    checkpoint (scratch ** protected) Hrunning Hentry) as Hreturned.
  assert (Hpop : sem_pend_boot_handler_pop suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_lr) returned_heap).
  { unfold sem_pend_boot_handler_pop; eapply armv7a_handler_scratch_pop_reads.
    match type of Hreturned with ?P returned_heap =>
      assert (Horder : P |-- scratch ** (private returned_cursor.(restore_handler_current_call)
        returned_cursor.(restore_handler_local) ** (UCOS2_inv sg checkpoint ** protected))) by entailer! end.
    exact (Horder returned_heap Hreturned). }
  assert (Hreturnedsp : snd returned_cursor.(restore_handler_local) =
    sem_pend_boot_handler_sp suspended.(armv7a_continuation_sp)).
  { rewrite (Hsp_return _ _ _ _ _ Hnormal); exact Hentrysp. }
  pose proof (restore_handler_local_resources _ _ _ bsp _ _ _ _ _ Hremask Hreturned) as Hremasked.
  assert (Hreturn_input : (interrupt_platform_running platform handler.(os_int_exit_invocation)
    handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
    task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
      suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended **
    (UCOS2_inv sg checkpoint ** unmap_table_rep sg ** perr # UChar |->_ ** frame)) remasked_heap).
  { match type of Hremasked with ?P remasked_heap => match goal with |- ?Q remasked_heap => assert (Hmerge : P |-- Q) end end.
    { unfold private, armv7a_handler_stack_loan, scratch, protected.
      rewrite Hremaskedcpsr, armv7a_cpsr_restore_mask_eq.
      change (armv7a_irq_fiq_mask 211) with 192.
      unfold os_int_exit_context_resources; rewrite Hfragments.
      pose proof (armv7a_handler_stack_merge_scratch handler.(os_int_exit_handler_stack) prefix suffix first
        (Z.land suspended.(armv7a_continuation_sp) 4) suspended.(armv7a_continuation_lr)) as Hstack_merge.
      rewrite Haddress_scratch in Hstack_merge; fold remainder in Hstack_merge.
      sep_apply_l_atomic Hstack_merge; entailer!. }
    exact (Hmerge remasked_heap Hremasked). }
  destruct (armv7a_save_transition_observations _ _ _ abi handler suspended irq_input saved_heap Hsave)
    as [_ [_ [_ [Hsavedmask [Hsavedpc _]]]]].
  set (word := armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)).
  assert (Hwrittenword : written.(kernel_restore_msr_word) = Some word) by (rewrite Hwritten; reflexivity).
  assert (Hhandlermask : handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask word).
  { unfold word; rewrite armv7a_cpsr_restore_mask_eq, Hr0; exact Hhandler. }
  assert (Hword : resume_cursor.(kernel_restore_msr_word) = Some word).
  { rewrite Hresumeword, Hwritten; reflexivity. }
  assert (Hwordmask : armv7a_irq_fiq_mask word = mask).
  { unfold word; rewrite armv7a_cpsr_restore_mask_eq, Hr0; exact (proj2 Hsaved). }
  assert (Hsavedmask' : armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = armv7a_irq_fiq_mask word).
  { rewrite Hsavedmask, Hhandler; unfold word; rewrite armv7a_cpsr_restore_mask_eq, Hr0; reflexivity. }
  destruct (sem_pend_unowned_irq_return_tail_source external platform port critical arch abi restore sg original
    handler suspended checkpoint word resume_cursor remasked_heap irq_return final_cursor restored perr frame
    Hcall Hbinding Hslice Hsavedmask' Hword Hresumelr Hreturn_input Hirq Hsuffix)
    as [Hrestorereads [Hsame [Hfinal [after [Hstore Hafter]]]]].
  assert (Hhistory : sem_pend_unowned_restore_history external platform critical sg original checkpoint
    (armv7a_continuation_resumed_call suspended original) (mutex_del_restore_clients_state clients checkpoint)).
  { eapply SemPendUnownedRestoreBootIRQ with (abi := abi) (restore := restore)
      (private := private) (local_step := local_step) (normal_return := normal_return)
      (handler := handler) (suspended := suspended) (cursor := cursor) (before := before) (written := written)
      (written_word := word) (irq_input := irq_input) (saved_heap := saved_heap)
      (handler_cursor := handler_cursor) (handler_heap := handler_heap) (returned_cursor := returned_cursor)
      (returned_heap := returned_heap) (handler_entry_pc := handler_entry_pc) (handler_bl_pc := handler_bl_pc)
      (remask_cursor := remask_cursor) (remasked_cursor := remasked_cursor) (remasked_heap := remasked_heap)
      (remask_word := remask_word) (irq_return := irq_return) (resume_cursor := resume_cursor)
      (final_cursor := final_cursor) (after := restored); eassumption. }
  rewrite (sem_pend_boot_counter_clients_state_eq clients checkpoint Hrunning) in Hhistory.
  rewrite Hwordmask in Hafter.
  exists after; split; [exact Hstore|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hfinish : P |-- Q) end end.
  { unfold sem_pend_stack_save_input, sem_pend_optional_stack_resources.
    destruct Hsame as [Hi [Ho Hs]]; rewrite Hi, Ho.
    sep_apply_l_atomic (sem_pend_stack_restore_source_output_unowned external platform critical sg original
      (armv7a_continuation_resumed_call suspended original) mask checkpoint checkpoint Hhistory).
    match goal with |- ?P |-- _ => assert (Hpad : P |--
      (TT ** sem_pend_stack_restore_source_output external platform None critical sg original mask checkpoint **
        unmap_table_rep sg ** perr # UChar |-> 0) **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)
      by (entailer!; apply derivable1_truep_intros) end.
    eapply derivable1_trans; [exact Hpad|].
    sep_apply_l_atomic (sem_pend_stack_call_post_from_restore external platform None critical sg context original mask
      pevent timeout perr initial checkpoint 0 eid X Hresult Hnonzero Haddress Hclear Hcontext Hexec); entailer!. }
  exact (Hfinish after Hafter).
Qed.
