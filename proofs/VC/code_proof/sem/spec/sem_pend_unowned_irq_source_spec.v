Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_unowned_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cleanup_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_call_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapStorage KernelHeapObservation ListNotations.
Import Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** In the selected counter-only registry, the physical OSRunning read
    makes both kernel clients inactive before OSStart. This is proved on
    the actual heap and needs no Task capsule or ready-task premise. *)
Lemma sem_pend_boot_counter_client_heap_eq : forall sg kind state before after
  (frame : Assertion),
  state.(SchedState).(isRunning) = false ->
  (UCOS2_inv sg state ** frame) before ->
  restore_handler_client_execution sg kind before after -> before = after.
Proof.
  intros sg kind state before after frame Hrunning Hpre Hrun.
  destruct Hpre as [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]].
  pose proof (os_int_exit_raw_running_load sg state owned Hraw) as Hr.
  rewrite Hrunning in Hr.
  pose proof (uchar_load_frame _ _ _ _ _ Hr Hjoin) as Hzero.
  destruct Hrun as [before after Henter|before after Hexit].
  - destruct Henter; [reflexivity| |];
      match goal with Hread : uchar_load _ 1 _ |- _ =>
        pose proof (uchar_load_deterministic _ _ _ _ Hread Hzero); discriminate
      end.
  - destruct Hexit;
      match goal with Hcounter : os_int_exit_masked_counter_fragment _ _ _ _ |- _ =>
        inversion Hcounter; subst
      end; try reflexivity;
      match goal with Hread : uchar_load _ 1 _ |- _ =>
        pose proof (uchar_load_deterministic _ _ _ _ Hread Hzero); discriminate
      end.
Qed.

Lemma sem_pend_boot_counter_clients_state_eq : forall clients state,
  state.(SchedState).(isRunning) = false ->
  mutex_del_restore_clients_state clients state = state.
Proof.
  induction clients as [|kind clients IH]; intros state Hrunning; [reflexivity|].
  cbn [mutex_del_restore_clients_state].
  assert (Hstep : mutex_del_restore_client_state kind state = state).
  { destruct kind; cbn [mutex_del_restore_client_state].
    - apply os_int_enter_not_running_no_effect; exact Hrunning.
    - unfold os_int_exit_counter_state; rewrite Hrunning.
      cbn [interrupt_exit_state]; apply replace_IntrS_put_back. }
  rewrite Hstep; apply IH; exact Hrunning.
Qed.

(** The BSP's existing local frame law transports the SAME physical
    kernel, continuation and caller frame; its actual registered kernel
    steps are proved inactive by the preceding byte-read argument. *)
Lemma sem_pend_boot_handler_trace_preserves_frame : forall Local
  (private : RestoreHandlerCall -> Local -> Assertion) local_step normal_return
  (bsp : RestoreHandlerContract private local_step normal_return)
  sg clients cursor before returned_cursor after,
  mutex_del_restore_handler_trace local_step sg clients cursor before returned_cursor after ->
  forall state (frame : Assertion), state.(SchedState).(isRunning) = false ->
  (private cursor.(restore_handler_current_call) cursor.(restore_handler_local) **
    (UCOS2_inv sg state ** frame)) before ->
  (private returned_cursor.(restore_handler_current_call) returned_cursor.(restore_handler_local) **
    (UCOS2_inv sg state ** frame)) after.
Proof.
  intros Local private local_step normal_return bsp sg clients cursor before returned_cursor after Htrace.
  induction Htrace; intros state frame Hrunning Hpre.
  - exact Hpre.
  - apply IHHtrace; [exact Hrunning|].
    eapply (restore_handler_local_resources _ _ _ bsp); eassumption.
  - assert (Horder : private cursor.(restore_handler_current_call) cursor.(restore_handler_local) **
      (UCOS2_inv sg state ** frame) |-- UCOS2_inv sg state **
      (private cursor.(restore_handler_current_call) cursor.(restore_handler_local) ** frame)) by entailer!.
    pose proof (sem_pend_boot_counter_client_heap_eq sg _ state before middle _
      Hrunning (Horder before Hpre) H0) as Heq; subst middle.
    apply IHHtrace; [exact Hrunning|exact Hpre].
Qed.

(** OSRunning != 1 selects BreakNothing in the pinned non-VFP port. The
    ABI save is the actual ordinary-memory/register-save boundary. No TCB
    lookup, publication, parked map, Task readiness or OSIntExit is used.
    The handler uses disjoint fragments of the same SVC stack region.
    This theorem does not prove the later BL/handler-body/remasking path. *)
Lemma sem_pend_unowned_boot_irq_save_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state handler suspended
  (frame : Assertion) before saved_heap,
  state.(SchedState).(isRunning) = false ->
  handler.(os_int_exit_interrupted_call).(os_sched_call_origin) = BootInvocation ->
  handler.(os_int_exit_handler_stack) =
    handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseRegion) ->
  (os_int_exit_frame_save_pre external platform handler ** (UCOS2_inv sg state ** frame)) before ->
  armv7a_save_transition abi handler suspended before saved_heap ->
  kernel_heap_writes (armv7a_continuation_save_writes suspended)
    before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
  uchar_load sg.(g_OSRunning) 0 saved_heap /\
  suspended.(armv7a_continuation_call) = Some handler.(os_int_exit_interrupted_call) /\
  armv7a_continuation_binding suspended /\
  (interrupt_platform_running platform handler.(os_int_exit_invocation)
     handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
   task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
     suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended **
   (UCOS2_inv sg state ** frame)) saved_heap.
Proof.
  intros external platform port abi sg state handler suspended frame before saved_heap
    Hrunning Hboot Hstack Hpre Hsave.
  destruct (armv7a_save_transition_observations _ _ _ abi handler suspended before saved_heap Hsave)
    as [Hentry [Hcall [Hbinding [Hmask [Hpc [Hsp Hfragments]]]]]].
  destruct (armv7a_save_transition_resources _ _ _ abi handler suspended
    handler.(os_int_exit_interrupted_call) (UCOS2_inv sg state ** frame) before saved_heap
    Hcall eq_refl Hbinding Hmask Hpc Hsp Hfragments Hpre Hsave) as [Hwrites Hpost].
  split; [exact Hwrites|]. split.
  - match type of Hpost with ?P saved_heap => assert (Hfocus : P |-- UCOS2_inv sg state ** TT)
      by (entailer!; intros ? ?; exact I) end.
    destruct (Hfocus saved_heap Hpost) as [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]].
    pose proof (os_int_exit_raw_running_load sg state owned Hraw) as Hr.
    rewrite Hrunning in Hr; eapply uchar_load_frame; eassumption.
  - split; [exact Hcall|]. split; assumption.
Qed.

(** The actual None Restore's DSB/MSR releases the existing inside owner,
    then the Boot IRQ save consumes that SAME execution resource. The
    saved input is not replaced by a conveniently chosen new heap. *)
Lemma sem_pend_unowned_restore_boot_irq_entry : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  sg handler suspended mask saved acquired released cursor before written irq_input saved_heap
  (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  released.(SchedState).(isRunning) = false -> call.(os_sched_call_origin) = BootInvocation ->
  handler.(os_int_exit_handler_stack) = call.(os_sched_call_stack).(stackLeaseRegion) ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask saved ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (sem_pend_stack_restore_input external platform None critical sg call mask saved acquired released **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written irq_input ->
  armv7a_save_transition abi handler suspended irq_input saved_heap ->
  written = kernel_restore_write_cpsr cursor /\
  kernel_heap_writes (armv7a_continuation_save_writes suspended)
    irq_input.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
  uchar_load sg.(g_OSRunning) 0 saved_heap /\
  suspended.(armv7a_continuation_call) = Some call /\ armv7a_continuation_binding suspended /\
  (interrupt_platform_running platform handler.(os_int_exit_invocation)
     handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
   task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
     suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended **
   (UCOS2_inv sg released ** frame)) saved_heap.
Proof.
  intros external platform port critical arch abi restore sg handler suspended mask saved acquired released
    cursor before written irq_input saved_heap frame call Hrunning Hboot Hstack Hhandler Hr0 Hmask Hpre Hprefix Hsave.
  assert (Hopen : sem_pend_stack_restore_input external platform None critical sg call mask saved acquired released **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame |--
    critical_region_masked platform critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved acquired ** os_sched_context_resources external call **
    (UCOS2_inv sg released ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) ** frame)).
  { unfold sem_pend_stack_restore_input, sem_pend_optional_stack_resources; entailer!. }
  destruct (armv7a_restore_prefix_releases_critical_region external platform critical arch restore sg call
    saved acquired cursor before written irq_input _ Hr0 Hmask (Hopen before Hpre) Hprefix)
    as [Hcursor [Hmemory Hreleased]].
  assert (Hsave_input : (os_int_exit_frame_save_pre external platform handler **
    (UCOS2_inv sg released ** frame)) irq_input).
  { match type of Hreleased with ?P irq_input => match goal with |- ?Q irq_input => assert (Horder : P |-- Q)
      by (unfold os_int_exit_frame_save_pre; rewrite Hhandler; entailer!) end end.
    exact (Horder irq_input Hreleased). }
  split; [exact Hcursor|].
  exact (sem_pend_unowned_boot_irq_save_source external platform port abi sg released handler suspended
    frame irq_input saved_heap Hrunning Hboot Hstack Hsave_input Hsave).
Qed.

(** Consume an ACTUAL masked handler-return cut on this heap. The saved
    frame is not inferred from an integer identity or restored old global
    snapshot. Sixteen physical reads and the approved continuation ABI
    recover the same invocation/stack, with its newly saved byte image.
    The pending BX and SemPend's *perr=0 then execute on that actual heap.

    The caller must connect the BSP's BL/return/remasking to this cut. This
    local return producer deliberately leaves that source connection to
    the bounded public consumer below. *)
Lemma sem_pend_unowned_irq_return_tail_source : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  sg original handler suspended current word cursor before irq_return final_cursor restored
  perr (frame : Assertion),
  suspended.(armv7a_continuation_call) = Some original ->
  armv7a_continuation_binding suspended -> armv7a_task_frame_slice suspended ->
  armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = armv7a_irq_fiq_mask word ->
  cursor.(kernel_restore_msr_word) = Some word ->
  cursor.(kernel_restore_lr) = suspended.(armv7a_continuation_lr) ->
  (interrupt_platform_running platform handler.(os_int_exit_invocation)
     handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
   task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
     suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended **
   (UCOS2_inv sg current ** unmap_table_rep sg ** perr # UChar |->_ ** frame)) before ->
  armv7a_restore_transition abi handler suspended before irq_return ->
  armv7a_restore_suffix_transition restore cursor irq_return final_cursor restored ->
  armv7a_continuation_restore_reads suspended before /\
  kernel_stack_call_same_call (armv7a_continuation_resumed_call suspended original) original /\
  final_cursor.(kernel_restore_return_word) = Some suspended.(armv7a_continuation_lr) /\
  exists after, kernel_heap_execution [(perr, 0)] restored after /\
    (sem_pend_stack_save_input external platform None critical sg
       (armv7a_continuation_resumed_call suspended original) (armv7a_irq_fiq_mask word) current **
     unmap_table_rep sg ** perr # UChar |-> 0 **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame) after.
Proof.
  intros external platform port critical arch abi restore sg original handler suspended current word cursor
    before irq_return final_cursor restored perr frame Hcall Hbinding Hslice Hmask Hword Hlr
    Hpre Hirq Hsuffix.
  assert (Hreads : armv7a_continuation_restore_reads suspended before).
  { match type of Hpre with ?P before => assert (Hfocus : P |--
      task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
        suspended.(armv7a_continuation_fragments) ** TT) by (entailer!; intros ? ?; exact I) end.
    exact (armv7a_task_frame_slice_restore_reads suspended (TT) before Hbinding Hslice (Hfocus before Hpre)). }
  pose proof (proj2 Hbinding) as Hstack; rewrite Hcall in Hstack.
  assert (Hsame : kernel_stack_call_same_call (armv7a_continuation_resumed_call suspended original) original).
  { unfold kernel_stack_call_same_call, armv7a_continuation_resumed_call; cbn; auto. }
  destruct (armv7a_restore_call_resources external platform port abi handler suspended original
    (UCOS2_inv sg current ** unmap_table_rep sg ** perr # UChar |->_ ** frame)
    before irq_return Hcall Hreads Hpre Hirq) as [Hmemory Hresumed].
  rewrite Hmask in Hresumed.
  assert (Hsuffix_input : (kernel_call_execution_owned external platform
    (armv7a_continuation_resumed_call suspended original) (armv7a_irq_fiq_mask word) **
    (UCOS2_inv sg current ** unmap_table_rep sg ** perr # UChar |->_ **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame)) irq_return).
  { match type of Hresumed with ?P irq_return => match goal with |- ?Q irq_return => assert (Horder : P |-- Q)
      by entailer! end end; exact (Horder irq_return Hresumed). }
  destruct (armv7a_restore_suffix_transports_owned_execution external platform critical arch restore
    (armv7a_continuation_resumed_call suspended original) word cursor irq_return final_cursor restored _
    Hword Hsuffix_input Hsuffix) as [Hcursor [Hrestored_memory Hafter]].
  split; [exact Hreads|]. split; [exact Hsame|]. split.
  - rewrite Hcursor; cbn [kernel_restore_branch_lr kernel_restore_return_word]; rewrite Hlr; reflexivity.
  - set (tail := kernel_call_execution_owned external platform
      (armv7a_continuation_resumed_call suspended original) (armv7a_irq_fiq_mask word) **
      UCOS2_inv sg current ** unmap_table_rep sg **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack)
        handler.(os_int_exit_handler_fragments) ** frame).
    assert (Hstore : (perr # UChar |->_ ** tail) restored).
    { match type of Hafter with ?P restored => match goal with |- ?Q restored => assert (Horder : P |-- Q)
        by (unfold tail; entailer!) end end; exact (Horder restored Hafter). }
    destruct (sem_pend_error_store perr 0 tail restored ltac:(lia) Hstore)
      as [after [Hwrite Hwritten]].
    exists after; split; [exact Hwrite|].
    match type of Hwritten with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
    { unfold tail, sem_pend_stack_save_input, sem_pend_optional_stack_resources.
      rewrite mutex_query_closed_equiv; unfold kernel_call_execution_owned; entailer!. }
    exact (Hclose after Hwritten).
Qed.

(** Bounded Boot/counter-only composition at the actual final Restore.
    The same prefix/save heaps, literal scratch writes/reads, matched BSP
    return, remask and continuation restore construct the public history.
    No history is assumed as an input to this theorem.

    TWO SOURCE CUTS REMAIN EXPLICIT: the aligned prologue must establish
    the private entry owner on handler_heap; the actual remasked private
    owner must expose the existing CPU/port resources. These are local
    source-composition premises, not added laws of RestoreHandlerContract,
    new public SemPend Requires, or a proved arbitrary BSP implementation.
    The selected counter clients preserve the kernel/frame by physical
    reads; Task-origin None IRQs and other clients are outside this family. *)
Lemma sem_pend_unowned_boot_restore_public_source : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  (private : RestoreHandlerCall -> (KernelRestoreCursor * Z) -> Assertion) local_step normal_return
  (bsp : RestoreHandlerContract private local_step normal_return)
  sg context original handler suspended mask saved acquired checkpoint initial
  pevent eid timeout perr X cursor before written irq_input saved_heap
  handler_cursor handler_heap returned_cursor returned_heap handler_entry_pc handler_bl_pc
  remask_cursor remasked_cursor remasked_heap remask_word
  irq_return resume_cursor final_cursor restored (frame : Assertion),
  handler.(os_int_exit_interrupted_call) = original ->
  original.(os_sched_call_origin) = BootInvocation ->
  checkpoint.(SchedState).(isRunning) = false ->
  handler.(os_int_exit_handler_stack) = original.(os_sched_call_stack).(stackLeaseRegion) ->
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
  (private handler_cursor.(restore_handler_current_call) handler_cursor.(restore_handler_local) **
    (UCOS2_inv sg checkpoint **
     task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
       suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended **
     unmap_table_rep sg ** perr # UChar |->_ ** frame)) handler_heap ->
  normal_return sg handler_cursor handler_heap returned_cursor returned_heap ->
  sem_pend_boot_handler_pop suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_lr) returned_heap ->
  snd returned_cursor.(restore_handler_local) = sem_pend_boot_handler_sp suspended.(armv7a_continuation_sp) ->
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
  (private remasked_cursor.(restore_handler_current_call) remasked_cursor.(restore_handler_local) |--
    interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler) ->
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
  intros external platform port critical arch abi restore private local_step normal_return bsp sg context original
    handler suspended mask saved acquired checkpoint initial pevent eid timeout perr X cursor before written irq_input
    saved_heap handler_cursor handler_heap returned_cursor returned_heap handler_entry_pc handler_bl_pc remask_cursor
    remasked_cursor remasked_heap remask_word irq_return resume_cursor final_cursor restored frame
    Horiginal Hboot Hrunning Hstack Hhandler Hr0 Hmasked Hcontext Hresult Hnonzero Haddress Hclear Hexec
    Hpre Hprefix Hsave Hsavedlr Hslice Hscratch Hentrypc Hbl Hentrysp Hentrylr Hentry Hnormal Hpop
    Hreturnedsp Hremask Hremaskcursor Hremaskedsp Hremaskedpc Hremaskedcpsr Hremaskedlr Hmsr Hprivate
    Hirq Hresumecpsr Hresumeword Hresumelr Hsuffix.
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
  destruct (armv7a_save_transition_observations _ _ _ abi handler suspended irq_input saved_heap Hsave)
    as [_ [_ [_ [Hsavedmask [Hsavedpc _]]]]].
  set (word := armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)).
  assert (Hwrittenword : written.(kernel_restore_msr_word) = Some word) by (rewrite Hwritten; reflexivity).
  assert (Hhandlermask : handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask word).
  { unfold word; rewrite armv7a_cpsr_restore_mask_eq, Hr0; exact Hhandler. }
  destruct (restore_handler_return_refinement _ _ _ bsp sg handler_cursor handler_heap
    returned_cursor returned_heap Hnormal) as [Hmatched [Hreturnpc Hhandler_run]].
  destruct (mutex_del_restore_handler_execution_trace _ _ _ _ _ _ _ Hhandler_run) as [clients Htrace].
  set (protected := task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
    suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended **
    unmap_table_rep sg ** perr # UChar |->_ ** frame).
  assert (Hentry' : (private handler_cursor.(restore_handler_current_call) handler_cursor.(restore_handler_local) **
    (UCOS2_inv sg checkpoint ** protected)) handler_heap).
  { match type of Hentry with ?P handler_heap => match goal with |- ?Q handler_heap =>
      assert (Horder : P |-- Q) by (unfold protected; entailer!) end end.
    exact (Horder handler_heap Hentry). }
  pose proof (sem_pend_boot_handler_trace_preserves_frame _ _ _ _ bsp sg clients _ _ _ _ Htrace
    checkpoint protected Hrunning Hentry') as Hreturned.
  pose proof (restore_handler_local_resources _ _ _ bsp _ _ _ _ _ Hremask Hreturned) as Hremasked.
  assert (Hreturn_input : (interrupt_platform_running platform handler.(os_int_exit_invocation)
    handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
    task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
      suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended **
    (UCOS2_inv sg checkpoint ** unmap_table_rep sg ** perr # UChar |->_ ** frame)) remasked_heap).
  { match type of Hremasked with ?P remasked_heap => match goal with |- ?Q remasked_heap =>
      assert (Hopen : P |-- Q) by (unfold protected; sep_apply_l_atomic Hprivate; entailer!) end end.
    exact (Hopen remasked_heap Hremasked). }
  assert (Hword : resume_cursor.(kernel_restore_msr_word) = Some word).
  { rewrite Hresumeword, Hwritten; reflexivity. }
  assert (Hwordmask : armv7a_irq_fiq_mask word = mask).
  { unfold word; rewrite armv7a_cpsr_restore_mask_eq, Hr0; exact (proj2 Hsaved). }
  assert (Hsavedmask' : armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) =
    armv7a_irq_fiq_mask word).
  { rewrite Hsavedmask, Hhandler; unfold word; rewrite armv7a_cpsr_restore_mask_eq, Hr0; reflexivity. }
  destruct (sem_pend_unowned_irq_return_tail_source external platform port critical arch abi restore sg original
    handler suspended checkpoint word resume_cursor remasked_heap irq_return final_cursor restored perr frame
    Hcall Hbinding Hslice Hsavedmask' Hword Hresumelr Hreturn_input Hirq Hsuffix)
    as [Hreads [Hsame [Hfinal [after [Hstore Hafter]]]]].
  assert (Hhistory : sem_pend_unowned_restore_history external platform critical sg original checkpoint
    (armv7a_continuation_resumed_call suspended original) (mutex_del_restore_clients_state clients checkpoint)).
  { eapply SemPendUnownedRestoreBootIRQ with (abi := abi) (restore := restore)
      (private := private) (local_step := local_step) (normal_return := normal_return)
      (handler := handler) (suspended := suspended) (cursor := cursor) (before := before) (written := written)
      (written_word := word)
      (irq_input := irq_input) (saved_heap := saved_heap) (handler_cursor := handler_cursor)
      (handler_heap := handler_heap) (returned_cursor := returned_cursor) (returned_heap := returned_heap)
      (handler_entry_pc := handler_entry_pc) (handler_bl_pc := handler_bl_pc) (remask_cursor := remask_cursor)
      (remasked_cursor := remasked_cursor) (remasked_heap := remasked_heap) (remask_word := remask_word)
      (irq_return := irq_return) (resume_cursor := resume_cursor) (final_cursor := final_cursor) (after := restored);
      eassumption. }
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
