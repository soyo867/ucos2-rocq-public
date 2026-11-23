Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
From compcert.lib Require Import Integers.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_entry_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_public_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_irq_register_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_repeated_irq_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_save_irq_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_clients_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_owner_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_program_storage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_readonly_error_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_readonly_irq_save_source_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations KernelHeapObservation KernelHeapStorage.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_recycle_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_wake_source_spec.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** These are the two actual scheduler guards that defer selection. The
    subsequent complete Save/Restore call is executed; no scheduler post
    is included in this source relation. Selector/switch cases are separate. *)
Definition mutex_del_sched_deferred_prefix (sg : StableGlobVars) (before after : model) : Prop :=
  ((exists nesting, uchar_load sg.(g_OSIntNesting) nesting before /\ nesting <> 0) \/
   (uchar_load sg.(g_OSIntNesting) 0 before /\
    exists locks, uchar_load sg.(g_OSLockNesting) locks before /\ locks <> 0)) /\
  kernel_heap_execution [] before after.

Definition mutex_del_sched_deferred_execution environment critical arch
  (save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  sg mask state before after : Prop :=
  exists registers final_registers acquired saved_heap prefix_heap cursor written middle final_cursor,
    registers.(kernel_save_return_word) = None /\ valid_os_cpu_sr registers.(kernel_save_cpsr) /\
    armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask /\
    armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
      final_registers acquired saved_heap /\
    mutex_del_sched_deferred_prefix sg saved_heap prefix_heap /\
    cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) /\
    armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 /\
    armv7a_restore_prefix_transition restore cursor prefix_heap written middle /\
    armv7a_restore_suffix_transition restore written middle final_cursor after.

Lemma mutex_del_sched_deferred_source_post : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  sg call mask state before after (frame : Assertion),
  (os_sched_stack_pre (mutex_del_runtime_sched_environment environment)
    mutex_del_stack_resources sg call mask state ** frame) before ->
  mutex_del_sched_deferred_execution environment critical arch save restore sg mask state before after ->
  (os_sched_stack_return_post (mutex_del_runtime_sched_environment environment)
    mutex_del_stack_resources sg call mask state ** frame) after.
Proof.
  intros environment critical arch save restore sg call mask state before after frame Hpre
    (registers & final_registers & acquired & saved_heap & prefix_heap & cursor & written & middle & final_cursor &
      Hnone & Hvalid & Hmask & Hsave & Hprefix & Hr0 & Hmasked & Hrestore_prefix & Hrestore_suffix).
  set (abi := environment.(mutex_del_call_continuations)).
  set (active := task_stack_call_active_key call).
  assert (Hopen : os_sched_stack_pre (mutex_del_runtime_sched_environment environment)
      mutex_del_stack_resources sg call mask state ** frame |--
    kernel_call_execution_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
      call (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) **
    (kernel_stack_inv abi mutex_del_stack_resources sg active state ** frame)).
  { unfold os_sched_stack_pre, kernel_stack_call_closed.
    cbn [mutex_del_runtime_sched_environment task_stack_call_continuations kernel_save_read_cpsr kernel_save_cpsr];
      rewrite Hmask; entailer!. }
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hvalid|reflexivity]).
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg call (kernel_save_read_cpsr registers)
    state before final_registers acquired saved_heap _ Hsaved (Hopen before Hpre) Hsave)
    as [Hstate [Hmemory [Hreturn [Hword Hsaved_heap]]]].
  assert (Hsame_heap : saved_heap = prefix_heap).
  { destruct Hprefix as [Hguards Hrun]; eapply kernel_heap_execution_deterministic;
      [split; [constructor|split; reflexivity]|exact Hrun]. }
  subst prefix_heap.
  assert (Hrestore_open : critical_region_masked environment.(mutex_del_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
      os_sched_context_resources environment.(mutex_del_call_external) call **
      (kernel_stack_inv abi mutex_del_stack_resources sg active state ** frame) |--
    kernel_stack_call_masked abi mutex_del_stack_resources critical sg active call
      final_registers.(kernel_save_r0) state state ** frame)
    by (unfold kernel_stack_call_masked; entailer!).
  destruct (kernel_stack_call_restore_prefix _ _ _ _ _ abi restore mutex_del_stack_resources sg active call
    final_registers.(kernel_save_r0) state state cursor saved_heap written middle frame
    Hr0 Hmasked (Hrestore_open saved_heap Hsaved_heap) Hrestore_prefix) as [Hwritten [Hmem Hclosed]].
  set (word := armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)).
  assert (Eword : written.(kernel_restore_msr_word) = Some word) by (rewrite Hwritten; reflexivity).
  assert (Eword_mask : armv7a_irq_fiq_mask word = mask).
  { unfold word; rewrite armv7a_cpsr_restore_mask_eq, Hr0, Hword; exact Hmask. }
  assert (Hsaved_mask : armv7a_irq_fiq_mask final_registers.(kernel_save_r0) = mask)
    by (rewrite Hword; exact Hmask).
  rewrite Hsaved_mask, <- Eword_mask in Hclosed.
  assert (Hsuffix_open : kernel_stack_call_closed abi mutex_del_stack_resources sg active call
      (armv7a_irq_fiq_mask word) state ** frame |--
    kernel_call_execution_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
      call (armv7a_irq_fiq_mask word) ** (kernel_stack_inv abi mutex_del_stack_resources sg active state ** frame))
    by (unfold kernel_stack_call_closed; entailer!).
  destruct (armv7a_restore_suffix_transports_owned_execution _ _ _ _ restore call word written middle
    final_cursor after _ Eword (Hsuffix_open middle Hclosed) Hrestore_suffix)
    as [Hcursor [Hafter_memory Hafter]].
  assert (Hclose : kernel_call_execution_owned environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) call (armv7a_irq_fiq_mask word) **
      (kernel_stack_inv abi mutex_del_stack_resources sg active state ** frame) |--
    os_sched_stack_return_post (mutex_del_runtime_sched_environment environment)
      mutex_del_stack_resources sg call mask state ** frame).
  { unfold os_sched_stack_return_post, kernel_stack_call_history_restore_post; Exists call state.
    unfold kernel_stack_call_closed, kernel_stack_call_same_call; rewrite Eword_mask; entailer!. }
  exact (Hclose after Hafter).
Qed.

Section AlwaysReturnSource.
Context (environment : MutexDelCallEnvironment) (critical : CriticalRegionResources)
  (arch : A32InterruptContext) (sg : StableGlobVars) (Local : Type).
Variable save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
  environment.(mutex_del_call_platform) critical arch.
Variable restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
  environment.(mutex_del_call_platform) critical arch.
Variable registers_source : Armv7aIRQRegisterSave environment.(mutex_del_call_external)
  environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
  environment.(mutex_del_call_continuations).
Variable local_step : OsIntExitCallContext ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable normal_return : OsIntExitCallContext -> StableGlobVars ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable handler_contract : forall handler,
  RestoreHandlerContract
    (fun (_ : RestoreHandlerCall) (_ : Local) =>
      mutex_del_restore_handler_owner environment.(mutex_del_call_platform)
        environment.(mutex_del_call_port) handler)
    (local_step handler) (normal_return handler).
Variable handler_stack : TaskStackRegion.
Variable handler_fragments : TaskStackFragments.

(** One complete returning ALWAYS source branch, including concrete wake/recycle,
    repeated counter IRQs around the outer Save/Restore, and the real scheduler
    call when requested. This branch handles the scheduler's deferring guards. *)
Definition mutex_del_always_owner_adjust_execution
  restore_entry call state mask registers pe eid observed group ceiling pointer old_priority priority perr cpu_sr saved_word
  before entered acquired returned final after : Prop :=
  let checkpoint := mutex_del_always_checkpoint sg eid observed (mutex_del_owner_adjusted_state sg acquired eid priority) in
  exists initialized prefix_heap returned_registers resumed final_registers final_state
    saved_heap body_heap released_heap adjusted_heap recycled middle restored returned_heap scheduled_heap cursor written final_cursor count,
    kernel_heap_execution (pointer_store_writes cpu_sr 0) before initialized /\
    mutex_del_call_prefix_execution sg pe perr initialized None prefix_heap /\
    registers.(kernel_save_return_word) = None /\
    valid_os_cpu_sr registers.(kernel_save_cpsr) /\
    armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask /\
    mutex_del_irq_registers_execution environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
      environment.(mutex_del_call_continuations) registers_source sg Local local_step normal_return
      handler_stack handler_fragments (armv7a_save_entry_address save + 4)
      (kernel_save_read_cpsr registers) call state prefix_heap returned_registers entered acquired resumed /\
    armv7a_save_suffix_transition save returned_registers acquired resumed
      final_registers final_state saved_heap /\
    saved_word = final_registers.(kernel_save_r0) /\
    kernel_heap_execution (pointer_store_writes cpu_sr saved_word) saved_heap body_heap /\
    uchar_load (pe + OSEventType_off) 4 body_heap /\
    uchar_load (pe + OSEventGrp_off) group body_heap /\
    mutex_del_count_load (pe + OSEventCnt_off) count body_heap /\
    unsigned_last_nbits (Z.shiftr count 8) 8 = ceiling /\
    ceiling <> 255 /\
    pointer <> 0 /\
    pointer_load (pe + OSEventPtr_off) pointer body_heap /\
    kernel_heap_execution
      (pointer_store_writes (sg.(g_OSTCBPrioTbl) + ceiling * sizeof(PTR)) 0) body_heap released_heap /\
    mutex_del_effective_priority_reads sg pointer released_heap 0 priority /\
    uchar_load (tcb_field_address pointer TCBPrio) old_priority released_heap /\
    old_priority <> priority /\
    mutex_del_rdy_at_priority_execution sg pointer priority released_heap adjusted_heap /\
    mutex_del_always_after_prepare_execution sg pe adjusted_heap recycled /\
    cursor.(kernel_restore_r0) = saved_word /\
    armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 /\
    armv7a_restore_prefix_transition restore cursor recycled written middle /\
    mutex_del_restore_irqs_execution environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
      environment.(mutex_del_call_continuations) sg Local local_step normal_return
      handler_stack handler_fragments (armv7a_irq_fiq_mask saved_word)
      (restore_entry + 8) cursor.(kernel_restore_lr) entered checkpoint middle returned final restored /\
    armv7a_restore_suffix_transition restore written restored final_cursor returned_heap /\
    (if Z.eqb group 0 then scheduled_heap = returned_heap
     else mutex_del_sched_deferred_execution environment critical arch save restore sg mask final
       returned_heap scheduled_heap) /\
    kernel_heap_execution [(perr, 0)] scheduled_heap after.

Lemma mutex_del_runtime_always_owner_adjust_source_post : forall restore_entry call state mask registers
  pe eid observed group ceiling pointer old_priority priority perr old_error cpu_sr saved_word before entered acquired returned final after (frame : Assertion),
  mutex_del_parent_layout sg -> mutex_del_parent_input sg pe state eid observed ->
  (mutex_del_runtime_entry environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) sg call mask state **
    (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
    task_stack_fragments_rep handler_stack handler_fragments ** frame) before ->
  mutex_del_always_owner_adjust_execution restore_entry call state mask registers pe eid observed group ceiling pointer old_priority priority perr cpu_sr
    saved_word before entered acquired returned final after ->
  saved_word = registers.(kernel_save_cpsr) /\
  mutex_del_parent_critical_observation sg eid 1 0 0 (if Z.eqb group 0 then 0 else 1) acquired
    (mutex_del_always_checkpoint sg eid observed (mutex_del_owner_adjusted_state sg acquired eid priority)) /\
  (mutex_del_runtime_post environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) sg call mask state pe 1 eid 0 0 **
    (perr # UChar |-> 0) ** (cpu_sr # UInt |-> saved_word) **
    task_stack_fragments_rep handler_stack handler_fragments ** frame) after.
Proof.
  intros restore_entry call state mask registers pe eid observed group ceiling pointer old_priority priority perr old_error cpu_sr saved_word
    before entered acquired returned final after frame Hlayout Hdomain Hentry Hsource.
  set (abi := environment.(mutex_del_call_continuations)) in *.
  set (active := task_stack_call_active_key call).
  assert (Hopen : mutex_del_runtime_entry environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask state |--
    kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state).
  { unfold mutex_del_runtime_entry; Intros same_environment.
    destruct H as [Henv ->]; reflexivity. }
  assert (Hpre : (kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
      task_stack_fragments_rep handler_stack handler_fragments ** frame) before).
  { match type of Hentry with ?P before => match goal with |- ?Q before => assert (Horder : P |-- Q) end end.
    { sep_apply_l_atomic Hopen; entailer!. } exact (Horder before Hentry). }
  destruct Hsource as (initialized & prefix_heap & returned_registers & resumed & final_registers & final_state &
    saved_heap & body_heap & released_heap & adjusted_heap & recycled & middle & restored & returned_heap & scheduled_heap & cursor & written & final_cursor & count &
    Hinit & Hprefix & Hnone & Hvalid & Hmask & Hsave_irqs & Hsave_suffix & Hsaved & Hstore &
    Htype_read & Hgroup_read & Hcount_read & Hceiling & Hpcp & Hpointer_nonzero & Hptr_read & Hrelease & Hreads & Hcompare & Hdifferent & Hrdy & Hstores & Hr0 & Hmasked & Hrestore_prefix &
    Hrestore_irqs & Hrestore_suffix & Hscheduled & Herror).
  subst saved_word.
  set (entry_residual := mutex_del_stack_critical_frame abi sg active state **
    task_stack_fragments_rep handler_stack handler_fragments ** frame).
  assert (Hinitialize_order : kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
      task_stack_fragments_rep handler_stack handler_fragments ** frame |--
    (cpu_sr # UInt |->_) **
      (kernel_program_inv sg state ** (perr # UChar |-> old_error) **
       (kernel_call_execution_owned environment.(mutex_del_call_external)
          environment.(mutex_del_call_platform) call mask ** entry_residual))).
  { unfold kernel_stack_call_closed, entry_residual.
    rewrite mutex_del_stack_world_split_critical_frame; entailer!. }
  destruct (task_stack_uint_store_execution cpu_sr 0 _ before ltac:(lia)
    (Hinitialize_order before Hpre)) as [produced [Hinitialize Hinitialized]].
  assert (produced = initialized) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hprefix_order : (cpu_sr # UInt |-> 0) **
      (kernel_program_inv sg state ** (perr # UChar |-> old_error) **
       (kernel_call_execution_owned environment.(mutex_del_call_external)
          environment.(mutex_del_call_platform) call mask ** entry_residual)) |--
    kernel_program_inv sg state ** (perr # UChar |-> old_error) **
      (kernel_call_execution_owned environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) call mask ** (cpu_sr # UInt |->_) ** entry_residual)).
  { sep_apply_l_atomic (store_uint_undef_store_uint cpu_sr 0); entailer!. }
  destruct (mutex_del_call_prefix_resources sg state pe eid observed perr old_error initialized None prefix_heap _
    Hdomain (Hprefix_order initialized Hinitialized) Hprefix)
    as [[Hnonnull [Hentry_type Hnest]] Hprefix_owned].
  assert (Hprefix_ok : mutex_del_parent_prefix_ok pe state eid).
  { unfold mutex_del_parent_prefix_ok; apply mutex_del_before_save_continues_iff;
    [rewrite Hnest; lia|auto]. }
  assert (Hsave_order : kernel_program_inv sg state ** (perr # UChar |-> old_error) **
      (kernel_call_execution_owned environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) call mask ** (cpu_sr # UInt |->_) ** entry_residual) |--
    kernel_stack_call_closed abi mutex_del_stack_resources sg active call
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state **
      (task_stack_fragments_rep handler_stack handler_fragments **
       ((cpu_sr # UInt |->_) ** (perr # UChar |-> old_error) ** frame))).
  { unfold kernel_stack_call_closed, entry_residual; rewrite Hmask.
    rewrite mutex_del_stack_world_split_critical_frame; entailer!. }
  destruct (mutex_del_stack_irq_save_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi registers_source sg Local
    local_step normal_return handler_contract handler_stack handler_fragments critical arch save active call state
    registers prefix_heap returned_registers entered acquired resumed final_registers final_state saved_heap _
    Hnone Hvalid (Hsave_order prefix_heap Hprefix_owned) Hsave_irqs Hsave_suffix)
    as [Hmrs [Hsuffix_source [Hstate [Hsaved_value [Hfinal_cpsr [Hreturn [Hsame_entered [Hevents Hsaved_heap]]]]]]]].
  destruct (mutex_del_irq_registers_execution_refinement environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi registers_source sg Local
    local_step normal_return handler_stack handler_fragments _ _ _ _ _ _ _ _ _ Hsave_irqs)
    as [_ [_ [_ Hcounter]]].
  pose proof (mutex_del_counter_irqs_owner_history environment sg Local local_step normal_return
    handler_stack handler_fragments _ _ _ _ _ _ _ _ _ Hcounter) as Hhistory.
  assert (Hstore_order : kernel_stack_call_masked abi mutex_del_stack_resources critical sg active entered
      final_registers.(kernel_save_r0) acquired acquired **
      (task_stack_fragments_rep handler_stack handler_fragments **
       ((cpu_sr # UInt |->_) ** (perr # UChar |-> old_error) ** frame)) |--
    (cpu_sr # UInt |->_) **
      (kernel_stack_call_masked abi mutex_del_stack_resources critical sg active entered
         final_registers.(kernel_save_r0) acquired acquired ** (perr # UChar |-> old_error) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame)) by entailer!.
  destruct (task_stack_uint_store_execution cpu_sr final_registers.(kernel_save_r0) _ saved_heap
    ltac:(rewrite Hsaved_value; exact Hvalid) (Hstore_order saved_heap Hsaved_heap))
    as [produced [Hwrite Hbody_owned]].
  assert (produced = body_heap) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  set (body_frame := critical_region_masked environment.(mutex_del_call_platform) critical sg
      entered.(os_sched_call_invocation) entered.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
    os_sched_context_resources environment.(mutex_del_call_external) entered **
    mutex_del_stack_critical_frame abi sg active acquired **
    task_stack_fragments_rep handler_stack handler_fragments **
    (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** frame).
  assert (Hbody_order : (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
      (kernel_stack_call_masked abi mutex_del_stack_resources critical sg active entered
         final_registers.(kernel_save_r0) acquired acquired ** (perr # UChar |-> old_error) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame) |--
    coq_prop (UCOS2_state_inv sg acquired /\ mutex_program_selected_reachable sg acquired) &&
      (kernel_program_inv sg acquired ** body_frame)).
  { unfold kernel_stack_call_masked, body_frame.
    rewrite mutex_del_stack_world_split_critical_frame.
    unfold kernel_program_inv, mutex_del_stack_critical_frame; entailer!. }
  destruct (Hbody_order body_heap Hbody_owned) as [[Hacquired_valid Hreach] Hbody].
  destruct Hdomain as [Hzero|[_ [Haddress [Hid Hslot]]]]; [contradiction|].
  assert (Hacquired_slot : sem_query_public_slot acquired eid observed).
  { unfold sem_query_public_slot, mutex_query_lookup in *; rewrite Hevents; exact Hslot. }
  pose proof (mutex_del_call_program_type_load sg acquired pe eid observed body_heap _ Haddress Hacquired_slot Hbody)
    as Hactual_type.
  assert (Htype : event_slot_type_value acquired.(EventState) eid = 4)
    by (eapply uchar_load_deterministic; eassumption).
  destruct (mutex_del_parent_recheck_live_fields sg acquired eid observed Hacquired_valid Hacquired_slot Htype)
    as [mutex [Hlookup [Hkind Hfields]]].
  assert (Howner_use : mutex_owner_event_unlinked acquired.(TskState) acquired.(EventState)).
  { eapply mutex_program_reachable_owner_use; [|exact Hreach].
    intros; eapply mutex_program_selected_initial_empty; eassumption. }
  assert (Hparent : mutex_del_parent_entry sg eid acquired observed mutex)
    by (exact (conj Hacquired_valid (conj Hlookup (conj Hkind (conj Hfields Howner_use))))).
  pose proof (mutex_del_call_program_group_load sg acquired pe eid observed body_heap _ Haddress Hlookup Hbody)
    as Hactual_group.
  assert (Hgroup_value : group = encode_event_wait_grp observed.(waitList) acquired.(TskState))
    by (eapply uchar_load_deterministic; eassumption).
  pose proof (mutex_del_program_count_load sg acquired pe eid observed body_heap _ Haddress Hlookup Hbody)
    as Hactual_count.
  assert (Hcount : count = encode_event_cnt_value observed)
    by (eapply mutex_del_count_load_deterministic; eassumption).
  rewrite Hcount, (mutex_del_parent_cast_count sg eid acquired observed mutex Hparent) in Hceiling.
  pose proof (proj2 (proj2 (mutex_del_parent_count_decode sg eid acquired observed mutex Hparent))) as Hdecode.
  rewrite Hdecode in Hceiling; subst ceiling.
  rewrite Haddress in Hptr_read.
  pose proof (mutex_del_owned_ceiling_adjust_resources sg eid acquired observed mutex pointer old_priority priority
    body_heap released_heap adjusted_heap body_frame Hlayout Hparent Hpcp Hpointer_nonzero Hdifferent
    Hbody Hptr_read Hrelease Hreads Hcompare Hrdy) as Hprepared.
  set (prepared := mutex_del_owner_adjusted_state sg acquired eid priority) in *.
  rewrite Haddress in Hstores.
  destruct (mutex_del_always_after_prepare_resources sg eid acquired prepared observed mutex
    adjusted_heap recycled body_frame
    (event_table_layout_select sg eid (proj1 (proj2 Hlayout)) Hid) Hprepared Hstores)
    as [Hcritical Hrecycled].
  set (checkpoint := mutex_del_always_checkpoint sg eid observed prepared) in *.
  assert (Hobservation : mutex_del_parent_critical_observation sg eid 1 0 0
    (if Z.eqb group 0 then 0 else 1) acquired checkpoint).
  { exists OS_ERR_NONE, (negb (Z.eqb (encode_event_wait_grp observed.(waitList) acquired.(TskState)) 0)).
    split; [exact Hcritical|]. rewrite Hgroup_value.
    destruct (Z.eqb (encode_event_wait_grp observed.(waitList) acquired.(TskState)) 0); split; reflexivity. }
  assert (Hcheckpoint : mutex_del_stack_checkpoint sg acquired checkpoint).
  { right; exists eid, 1, (0, (OS_ERR_NONE,
      negb (Z.eqb (encode_event_wait_grp observed.(waitList) acquired.(TskState)) 0))); exact Hcritical. }
  assert (Hrestore_order : kernel_program_inv sg checkpoint ** body_frame |--
    mutex_del_stack_restore_input abi critical sg active entered final_registers.(kernel_save_r0) acquired checkpoint **
      (task_stack_fragments_rep handler_stack handler_fragments **
       ((cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** frame))).
  { unfold body_frame, mutex_del_stack_restore_input; entailer!. }
  destruct (mutex_del_stack_repeated_restore_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi sg Local local_step normal_return
    handler_contract handler_stack handler_fragments critical arch restore active entered
    final_registers.(kernel_save_r0) acquired checkpoint restore_entry cursor recycled written middle
    returned final restored final_cursor returned_heap _ Hr0 Hmasked (Hrestore_order recycled Hrecycled)
    Hrestore_prefix Hrestore_irqs Hrestore_suffix) as [Hi [Ho [Hs [Hrestore_return Hreturned]]]].
  rewrite Hsaved_value, Hmask in Hreturned.
  assert (Hsame : kernel_stack_call_same_call returned call).
  { destruct Hsame_entered as [Hi' [Ho' Hs']]; unfold kernel_stack_call_same_call; repeat split; congruence. }
  set (tail_frame := (cpu_sr # UInt |-> registers.(kernel_save_cpsr)) **
    task_stack_fragments_rep handler_stack handler_fragments ** frame).
  assert (Hreturn_order : kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final **
      (task_stack_fragments_rep handler_stack handler_fragments **
        ((cpu_sr # UInt |-> registers.(kernel_save_cpsr)) ** (perr # UChar |-> old_error) ** frame)) |--
    kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final **
      ((perr # UChar |-> old_error) ** tail_frame)) by (unfold tail_frame; entailer!).
  assert (Hcurrent : (kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final **
      ((perr # UChar |-> old_error) ** tail_frame)) returned_heap)
    by (exact (Hreturn_order returned_heap Hreturned)).
  assert (Hactive : task_stack_call_active_key returned = active).
  { unfold active, task_stack_call_active_key; destruct Hsame as [Hsame_i [Hsame_o Hsame_s]].
    rewrite Hsame_o; reflexivity. }
  assert (Hruntime : (mutex_del_runtime_return environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask **
      ((perr # UChar |-> old_error) ** tail_frame)) scheduled_heap).
  { destruct (Z.eqb group 0) eqn:Hrequest.
    - subst scheduled_heap.
      match type of Hcurrent with ?P returned_heap => match goal with |- ?Q returned_heap =>
        assert (Horder : P |-- Q) end end.
      { unfold mutex_del_runtime_return, mutex_del_runtime_return_at; Exists returned final environment.
        unfold mutex_del_callsite_environment; entailer!. }
      exact (Horder returned_heap Hcurrent).
    - assert (Hsched_pre : kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final **
          ((perr # UChar |-> old_error) ** tail_frame) |--
        os_sched_stack_pre (mutex_del_runtime_sched_environment environment) mutex_del_stack_resources
          sg returned mask final ** ((perr # UChar |-> old_error) ** tail_frame)).
      { unfold os_sched_stack_pre; rewrite Hactive; reflexivity. }
      pose proof (mutex_del_sched_deferred_source_post environment critical arch save restore sg returned mask final
        returned_heap scheduled_heap _ (Hsched_pre returned_heap Hcurrent) Hscheduled) as Hscheduled_post.
      match type of Hscheduled_post with ?P scheduled_heap => match goal with |- ?Q scheduled_heap =>
        assert (Horder : P |-- Q) end end.
      { sep_apply_l_atomic (mutex_del_runtime_sched_post environment environment sg returned mask final eq_refl).
        sep_apply_l_atomic (mutex_del_runtime_return_same_call environment environment.(mutex_del_call_external)
          environment.(mutex_del_call_platform) sg call returned mask Hsame); entailer!. }
      exact (Horder scheduled_heap Hscheduled_post). }
  assert (Herror_order : mutex_del_runtime_return environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask ** ((perr # UChar |-> old_error) ** tail_frame) |--
    perr # UChar |-> old_error ** (mutex_del_runtime_return environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask ** tail_frame)) by entailer!.
  destruct (kernel_heap_framed_uchar_store perr old_error 0 _ scheduled_heap ltac:(lia)
    (Herror_order scheduled_heap Hruntime)) as [finished [Hwrite_error Hfinished]].
  assert (finished = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst finished.
  assert (Hpublic : mutex_del_runtime_return environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask |--
    mutex_del_runtime_post environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask state pe 1 eid 0 0).
  { unfold mutex_del_runtime_post; Left; Right; Exists acquired checkpoint (if Z.eqb group 0 then 0 else 1).
    entailer!. }
  split; [exact Hsaved_value|]. split; [exact Hobservation|].
  match type of Hfinished with ?P after => match goal with |- ?Q after => assert (Hfinish : P |-- Q) end end.
  { rewrite Hsaved_value; unfold tail_frame; sep_apply_l_atomic Hpublic; entailer!. }
  exact (Hfinish after Hfinished).
Qed.

End AlwaysReturnSource.
